use std::marker::PhantomData;
use itertools::Itertools;

use crate::{common::{algfn::AlgFnSO, math::{compress, decompress, evaluate_univar}, wrapper::{ComputationalField, TFelt}}, transcript::transcript::TArithmeticTranscript, protocol::component::{TProtocol, TProverImpl}};
pub(crate) use crate::common::claims::{EvalClaim, SumClaim};
use crate::common::claims::SinglePointClaims;
use crate::components::sumcheck::dense_eq::DenseEqSumcheck;
use crate::components::sumcheck::generic::SumcheckOutput::{Final, Partial};
use super::sumcheckable::Sumcheckable;


/// A sumcheck with single output, without eq multiplier.
#[derive(Clone)]
pub struct SumcheckProtocol<F: TFelt, Fun: AlgFnSO<F>> {
    pub(crate) f: Fun,
    pub(crate) num_vars: usize,
    pub(crate) num_rounds: usize,
    _marker: PhantomData<F>,
}

impl<F: TFelt, Fun: AlgFnSO<F>> SumcheckProtocol<F, Fun> {
    pub fn new(f: Fun, num_vars: usize) -> Self {
        Self::new_partial(f, num_vars, num_vars)
    }
    pub fn new_partial(f: Fun, num_vars: usize, num_rounds: usize) -> Self {
        Self { f, num_vars, num_rounds, _marker: PhantomData }
    }
}


impl<F: TFelt, Fun: AlgFnSO<F>, Transcript: TArithmeticTranscript<F>> TProtocol<Transcript> for SumcheckProtocol<F, Fun> {
    type ClaimsBefore = EvalClaim<F>;
    type ClaimsAfter = EvalClaim<F>;
    
    fn verify(&self, ctx: &mut Transcript, claims: Self::ClaimsBefore) -> Self::ClaimsAfter {
        let d = self.f.deg();
        let mut sum_claim = claims.ev;
        let mut rs = claims.point;
        for _ in 0..self.num_rounds {
            let compressed_poly = (0..d).map(|_| ctx.read()).collect_vec(); // read d coefficients: 0, 2, ..., d
            let poly = decompress(&sum_claim, &compressed_poly); // recover 1st coefficient
            let r = ctx.challenge(); // challenge
            rs.push(r.clone());
            sum_claim = evaluate_univar(&poly, &r);
        }
//        rs.reverse();
        EvalClaim{ev: sum_claim, point: rs}
    }
}

pub struct SumcheckGenericProverImpl<F: TFelt, Fun: AlgFnSO<F>, S: Sumcheckable<F>> {
    pub(crate) f: Fun,
    pub(crate) num_vars: usize,
    pub(crate) num_rounds: usize,
    _marker: PhantomData<(F, Fun, S)>,
}

impl<F: TFelt, Fun: AlgFnSO<F>, S: Sumcheckable<F>> SumcheckGenericProverImpl<F, Fun, S> {
    pub fn new(f: Fun, num_vars: usize) -> Self {
        Self::new_partial(f, num_vars, num_vars)
    }
    pub fn new_partial(f: Fun, num_vars: usize, num_rounds: usize) -> Self {
        Self { f, num_vars, num_rounds, _marker: PhantomData }
    }
}

pub enum SumcheckOutput<F, S> {
    Final(Vec<F>),
    Partial(S)
}

impl<F: ComputationalField, Fun: AlgFnSO<F>, S: Sumcheckable<F>, Transcript: TArithmeticTranscript<F>> TProverImpl<Transcript> for SumcheckGenericProverImpl<F, Fun, S> {
    type Verifier = SumcheckProtocol<F, Fun>;
    type ProverInput = S;
    type ProverOutput = SumcheckOutput<F, S>;

    fn prove(&self, ctx: &mut Transcript, claims: <Self::Verifier as TProtocol<Transcript>>::ClaimsBefore, mut sumcheckable: Self::ProverInput) -> (<Self::Verifier as TProtocol<Transcript>>::ClaimsAfter, Self::ProverOutput) {
        let d = self.f.deg();
        let mut sum_claim = claims.ev;
        let mut rs = claims.point;
        for _ in 0..self.num_rounds {
            let poly = sumcheckable.unipoly();
            let (_sum_claim, compressed_poly) = compress(&poly);
            assert!(_sum_claim == sum_claim);
            assert!(compressed_poly.len() == d);
            compressed_poly.iter().map(|coeff| ctx.write(coeff)).count();
            let r = ctx.challenge();
            rs.push(r);
            sum_claim = evaluate_univar(&poly, &r);
            sumcheckable.bind(r);
        }
        if self.num_rounds == self.num_vars {
            let final_evals = sumcheckable.final_evals();
            debug_assert_eq!(self.f.exec(&final_evals), sum_claim, "Final evals are passed as prover output for last round postprocess");
            (EvalClaim { ev: sum_claim, point: rs }, Final(final_evals))
        } else {
            (EvalClaim { ev: sum_claim, point: rs }, Partial(sumcheckable))
        }
    }
}
