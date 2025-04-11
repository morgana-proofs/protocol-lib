use std::marker::PhantomData;

use rayon::prelude::*;

use crate::{common::{algfn::AlgFnSO, claims::{EvalClaim, SinglePointClaims, SumClaim}, math::eq_poly, wrapper::{ComputationalField, TFelt, TFeltUtil}}, components::sumcheck::{dense::DenseSumcheck, dense_eq::eq_eval}, protocol::component::{TProtocol, TProverImpl}, transcript::transcript::TArithmeticTranscript};

/// This structure represents an array of bit chunks. We maintain a collection of these arrays.
#[derive(Clone, Debug)]
pub struct ChunkValuedArr {
    /// Bit size of the chunk. From 1 to 8.
    pub bitsize: usize,
    pub data: Vec<u8>,
}

pub trait SpookupOp : Clone + Copy + Send + Sync {
    type F: TFelt;
    
    fn n_bits_in(&self) -> usize;
    fn n_bits_out(&self) -> usize;

    /// Applies operation to the bitstring and outputs a new one.
    /// Inputs with bit size > n_bits_in are unsound.
    /// Sound outputs have bit size <= n_bits_out.
    fn apply(&self, x: u32) -> u32;

    /// Function is interpreted as sparse matrix; this evaluates multilinear extension of sparse matrix.
    /// Should have acceptable performance for the verifier, otherwise additional commitment argument will
    /// be required.
    fn verifier_evaluate(&self, input_point: &[Self::F], output_point: &[Self::F]) -> Self::F;

    /// If the function is interpreted as matrix A from 2^{n_bits_in} -> 2^{n_bits_out},
    /// computes A^t eq_pt.evals(). Or, in multilinear extension form, computes A(x, pt)
    /// where A(x, y) is a multilinear extension of matrix A.
    fn prover_evaluate_at_output(&self, pt: &[Self::F]) -> Vec<Self::F> where Self::F: ComputationalField {
        assert!(pt.len() == self.n_bits_out());
        let eq_poly = eq_poly(pt); // WE NEED NORMAL EQ BRO
        (0 .. 1 << self.n_bits_in()).into_par_iter().map(|i| {
            eq_poly[self.apply(i) as usize]
        }).collect()
    }
}

#[derive(Clone, Copy, Debug)]
struct MulFn<F: TFelt> {
    _marker: PhantomData<fn() -> F>,
}

impl<F: TFelt> AlgFnSO<F> for MulFn<F> {
    fn exec(&self, args: &impl std::ops::Index<usize, Output = F>) -> F {
        args[0] * args[1]
    }

    fn deg(&self) -> usize {
        2
    }

    fn n_ins(&self) -> usize {
        2
    }
}

impl<F: TFelt> MulFn<F> {
    fn new() -> Self {
        Self { _marker: PhantomData }
    }
}

// De facto, this is just an application of a matrix: sum_x P(x) * L(x, r)
impl<Op: SpookupOp, Transcript: TArithmeticTranscript<Op::F>> TProtocol<Transcript> for Op {
    type ClaimsBefore = EvalClaim<Op::F>;

    type ClaimsAfter = EvalClaim<Op::F>;

    fn verify(&self, ctx: &mut Transcript, claims: Self::ClaimsBefore) -> Self::ClaimsAfter {
        let sum_claim =  SumClaim(claims.ev);
        assert!(claims.point.len() == self.n_bits_out());
        let f = MulFn::new();
        let sumcheck = DenseSumcheck::new(f, self.n_bits_in());
        let claim_to_parse = sumcheck.verify(ctx, sum_claim);

        (claim_to_parse.evs[1] - self.verifier_evaluate(&claim_to_parse.point, &claims.point)).require(); // TODO: unnecessary transcript interaction       
        EvalClaim {point: claim_to_parse.point, ev: claim_to_parse.evs[0]}
    }
}

impl<Op: SpookupOp, Transcript: TArithmeticTranscript<Op::F>> TProverImpl<Transcript> for Op where Op::F : ComputationalField {
    type Verifier = Self;

    type ProverInput = Vec<Op::F>;

    type ProverOutput = ();

    fn _prove(protocol: &Self::Verifier, transcript: &mut Transcript, claims: <Self::Verifier as TProtocol<Transcript>>::ClaimsBefore, advice: Self::ProverInput) -> (<Self::Verifier as TProtocol<Transcript>>::ClaimsAfter, Self::ProverOutput) {
        let sum_claim = SumClaim(claims.ev);
        assert!(claims.point.len() == protocol.n_bits_out());
        let f = MulFn::new();
        let sumcheck = DenseSumcheck::<Op::F, MulFn<Op::F>>::new(f, protocol.n_bits_in());
        
        let advice: Vec<Vec<Op::F>> = vec![advice, protocol.prover_evaluate_at_output(&claims.point)];
        
        let (claim_to_parse, ()) = sumcheck.prove::<DenseSumcheck<_, _>>(transcript, sum_claim, advice);
        (EvalClaim {point: claim_to_parse.point, ev: claim_to_parse.evs[0]}, ())
    }
}
