use std::marker::PhantomData;
use itertools::Itertools;

use crate::{common::{algfn::AlgFnSO, math::{compress, decompress, evaluate_univar}, wrapper::{PolyOps, TPrimeField}}, dialects::dialect::TArithmeticDialect, protocol::component::{TProtocol, TProverImpl}};
use super::sumcheckable::Sumcheckable;


/// A sumcheck with single output, without eq multiplier.
#[derive(Clone)]
pub struct SumcheckProtocol<F: PolyOps, Fun: AlgFnSO<F>> {
    f: Fun,
    num_vars: usize,
    _marker: PhantomData<F>,
}

impl<F: PolyOps, Fun: AlgFnSO<F>> SumcheckProtocol<F, Fun> {
    pub fn new(f: Fun, num_vars: usize) -> Self {
        Self { f, num_vars, _marker: PhantomData }
    }
}


pub struct SumClaim<F>(pub F);
pub struct EvalClaim<F> {
    pub ev: F,
    pub point: Vec<F>,
}

impl<F: PolyOps, Fun: AlgFnSO<F>, Dialect: TArithmeticDialect<F>> TProtocol<Dialect> for SumcheckProtocol<F, Fun> {
    type ClaimsBefore = SumClaim<F>;
    type ClaimsAfter = EvalClaim<F>;
    
    fn verify(&self, ctx: &mut Dialect, claims: Self::ClaimsBefore) -> Self::ClaimsAfter {
        let d = self.f.deg();
        let mut sum_claim = claims.0;
        let mut rs = vec![];
        for i in 0..self.num_vars {
            let compressed_poly = (0..d).map(|_| ctx.read()).collect_vec(); // read d coefficients: 0, 2, ..., d
            let poly = decompress(&sum_claim, &compressed_poly); // recover 1st coefficient
            let r = ctx.challenge(); // challenge
            rs.push(r.clone());
            sum_claim = evaluate_univar(&poly, &r);
        }
        rs.reverse();
        EvalClaim{ev: sum_claim, point: rs}
    }
}

pub struct SumcheckGenericProverImpl<F: TPrimeField, Fun: AlgFnSO<F>, S: Sumcheckable<F>> {
    _marker: PhantomData<(F, Fun, S)>,
}
impl<F: TPrimeField, Fun: AlgFnSO<F>, S: Sumcheckable<F>, Dialect: TArithmeticDialect<F>> TProverImpl<Dialect> for SumcheckGenericProverImpl<F, Fun, S> {
    type Verifier = SumcheckProtocol<F, Fun>;
    type ProverInput = S;
    type ProverOutput = Vec<F>; // final evals

    fn _prove(protocol: &Self::Verifier, ctx: &mut Dialect, claims: <Self::Verifier as TProtocol<Dialect>>::ClaimsBefore, mut sumcheckable: Self::ProverInput) -> (<Self::Verifier as TProtocol<Dialect>>::ClaimsAfter, Self::ProverOutput) {
        let d = protocol.f.deg();
        let mut sum_claim = claims.0;
        let mut rs = vec![];
        for i in 0..protocol.num_vars {
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
        rs.reverse();
        let final_evals = sumcheckable.final_evals();
        debug_assert!(protocol.f.exec(&final_evals) == sum_claim); // Final evals are passed as prover output for last round postprocess.
        (EvalClaim{ev: sum_claim, point: rs}, final_evals)
    }
}

