use std::marker::PhantomData;

use ark_std::{rand::RngCore, test_rng};
use itertools::Itertools;
use rayon::prelude::*;

use crate::{
    common::{algfn::AlgFnSO, claims::{EvalClaim, SumClaim},
    math::{eq_poly, evaluate_multivar},
    wrapper::{ComputationalField, TFelt, TFeltUtil}},
    components::sumcheck::dense::DenseSumcheck,
    protocol::component::{TProtocol, TProverImpl},
    transcript::transcript::TArithmeticTranscript
};

pub trait MatrixOp : Send + Sync {
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
        let eq_poly = eq_poly(pt);
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
impl<Op: MatrixOp, Transcript: TArithmeticTranscript<Op::F>> TProtocol<Transcript> for Op {
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

impl<Op: MatrixOp, Transcript: TArithmeticTranscript<Op::F>> TProverImpl<Transcript> for Op where Op::F : ComputationalField {
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

#[cfg(test)]
pub mod tests {
    use crate::transcript::transcript::tests::ManualTestTranscript;
    use super::*;
    
    pub fn test_spookup_verifier_accepts_prover<F: ComputationalField, Op: MatrixOp<F = F>>(op: Op) {
        let dormant_dim = 8;
        // let n_bits = 7;

        let rng = &mut test_rng();
        let pt_out = (0..op.n_bits_out()).map(|_| {F::rand(rng)}).collect_vec();
        let pt_dorm = (0..dormant_dim).map(|_| {F::rand(rng)}).collect_vec();

        let mut transcript = ManualTestTranscript::new((0..1000).map(|_|F::rand(rng)).collect());

        let inputs = (0 .. 1 << dormant_dim).map(|_| rng.next_u32() % (op.n_bits_in() as u32)).collect_vec(); //inputs are triples a, b, carry bit. outputs are a+b+carry, and output carry
        let outputs = inputs.iter().map(|&x| op.apply(x)).collect_vec();

        let eq_out = eq_poly(&pt_out);
        let output_evals_dorm = outputs.iter().map(|&x| eq_out[x as usize]).collect_vec();

        let claims = EvalClaim{ ev: evaluate_multivar(&output_evals_dorm, &pt_dorm), point: pt_out.clone() };
        
        let eq_dorm = eq_poly(&pt_dorm);
        let mut advice = vec![F::zero(); 1 << op.n_bits_in()];
        inputs.iter().enumerate().map(|(i, &x)| advice[x as usize] += eq_dorm[i]).count(); // pushforward

        let (eval_claim, ()) = op.prove::<Op>(&mut transcript, claims.clone(), advice);

        let _proof = transcript.end();

        let eval_claim_2 = op.verify(&mut transcript, claims);

        assert!(eval_claim == eval_claim_2);
        let pt_in = eval_claim.point;
        let eq_in = eq_poly(&pt_in);

        let mut expected_eval = F::zero();
        inputs.iter().enumerate().map(|(i, &x)| expected_eval += eq_dorm[i] * eq_in[x as usize]).count();

        assert!(eval_claim.ev == expected_eval);
    }
}