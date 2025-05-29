use std::cmp::min;
use std::marker::PhantomData;
use std::ops::Index;
use itertools::Itertools;
use rayon::current_num_threads;
use tracing::instrument;
use crate::common::algfn::{AlgFn, AlgFnSO};
use crate::common::claims::{EvalClaim, SinglePointClaims, SumClaim};
use crate::common::math::{bind_dense_poly, eq_poly, evaluate_univar, from_evals};
use crate::common::wrapper::{ComputationalField, TFelt, TSigUtil};
use crate::components::sumcheck::algfn_wrappers::{EqWrapper, GammaWrapper};
use crate::components::sumcheck::generic::{SumcheckGenericProverImpl, SumcheckOutput, SumcheckProtocol};
use crate::components::sumcheck::sumcheckable::{FoldToSumcheckable, Sumcheckable};
use crate::transcript::transcript::TArithmeticTranscript;
use crate::protocol::component::{TProtocol, TProverImpl};



#[derive(Clone, Debug)]
pub struct DenseSumcheckableSO<F: ComputationalField, Fun: AlgFnSO<F>> where <F as TSigUtil>::Constants: From<u64>  {
    pub polys: Vec<Vec<F>>,
    challenges: Vec<F>,
    f: Fun,
    num_vars: usize,
    round_idx: usize,
    cached_unipoly: Option<Vec<F>>,

    pub claim: F,
}

impl<F: ComputationalField, Fun: AlgFnSO<F>> DenseSumcheckableSO<F, Fun> where <F as TSigUtil>::Constants: From<u64>  {
    pub fn new(polys: Vec<Vec<F>>, f: Fun, num_vars: usize, claim_hint: F) -> Self {
        let l = polys.len();
        assert_eq!(l, f.n_ins());
        for i in 0..l {
            assert_eq!(polys[i].len(), 1 << num_vars);
        }
        Self { polys, f, num_vars, round_idx: 0, cached_unipoly: None, challenges: vec![], claim: claim_hint }
    }
}

impl<F: ComputationalField, Fun: AlgFnSO<F>> Sumcheckable<F> for DenseSumcheckableSO<F, Fun> where <F as TSigUtil>::Constants: From<u64>  {
    fn bind(&mut self, t: F) {
        assert!(self.round_idx < self.num_vars, "the protocol has already ended");
        self.challenges.push(t);
        for poly in &mut self.polys {
            bind_dense_poly(poly, t);
        }
        self.round_idx += 1;
        match self.cached_unipoly.take() {
            None => {panic!("should evaluate unipoly before binding - it has an opportunity to change the state due to in-place evaluation")}
            Some(u) => {self.claim = evaluate_univar(&u, &t)}
        }
    }

    fn unipoly(&mut self) -> Vec<F>{
        assert!(self.round_idx < self.num_vars, "the protocol has already ended");

        match self.cached_unipoly.as_ref() {
            Some(p) => {return p.clone()},
            None => {
                let half = 1 << (self.num_vars - self.round_idx - 1);
                let n_polys = self.polys.len();

                let num_tasks = 8 * current_num_threads();

                let task_size = (half + num_tasks - 1) / num_tasks;

                let acc: Vec<Vec<F>> = (0..num_tasks).into_iter().map(|task_idx| {
                    let mut difs = vec![F::zero(); n_polys];
                    let mut args = vec![F::zero(); n_polys];
                    let mut acc = vec![F::zero(); self.f.deg()];

                    (task_idx * task_size .. min((task_idx + 1) * task_size, half)).map(|i| {
                        for j in 0..n_polys {
                            args[j] = self.polys[j][2 * i + 1];
                        }

                        acc[0] = acc[0] + self.f.exec(&args);

                        for j in 0..n_polys {
                            difs[j] = self.polys[j][2 * i + 1] - self.polys[j][2 * i]
                        }

                        for s in 1..self.f.deg() {
                            for j in 0..n_polys {
                                args[j] = args[j] + difs[j];
                            }

                            acc[s] = acc[s] + self.f.exec(&args);
                        }
                    }).count();

                    acc
                }).collect();

                let mut total_acc = vec![F::zero(); self.f.deg() + 1];

                for i in 0..acc.len() {
                    for j in 0..self.f.deg() {
                        total_acc[j + 1] = total_acc[j + 1] + acc[i][j]
                    }
                }
                total_acc[0] = self.claim - total_acc[1];

                self.cached_unipoly = Some(from_evals(&total_acc));
            }
        }
        self.cached_unipoly.as_ref().unwrap().clone()

    }


    fn final_evals(&self) -> Vec<F> {
        assert!(self.round_idx == self.num_vars, "can only call final evals after the last round");
        self.polys.iter().map(|poly| poly[0]).collect()
    }

    fn challenges(&self) -> &[F] {
        &self.challenges
    }
}


// Naive impl without Gruen's trick. Will be added later.
pub struct DenseEqSumcheckable<F: TFelt, Fun: AlgFn<F>> {
    polys: Vec<Vec<F>>,
    point: Vec<F>,
    f: Fun,
    claim_hint: Vec<F>,
}

impl<F: TFelt, Fun: AlgFn<F>> DenseEqSumcheckable<F, Fun> {
    pub fn new(polys: Vec<Vec<F>>, f: Fun, point: Vec<F>, claim_hint: Vec<F>) -> Self {
        assert!(claim_hint.len() == f.n_outs());
        Self { polys, f, point, claim_hint }
    }
}

impl<F: ComputationalField, Fun: AlgFn<F>> FoldToSumcheckable<F> for DenseEqSumcheckable<F, Fun> where <F as TSigUtil>::Constants: From<u64>  {
    type Target = DenseSumcheckableSO<F, EqWrapper<F, GammaWrapper<F, Fun>>>; // to be replaced

    fn rlc(self, gamma: F) -> Self::Target {
        let gamma_wrapper = GammaWrapper::new(self.f, gamma);
        let eq_wrapper = EqWrapper::new(gamma_wrapper);

        let claim_hint = gamma_rlc(gamma, &self.claim_hint);
        let num_vars = self.point.len();

        let mut polys = self.polys;
        let eq = eq_poly(&self.point);
        polys.push(eq);

        Self::Target::new(
            polys,
            eq_wrapper,
            num_vars,
            claim_hint,
        )
    }
}

pub struct DenseEqSumcheck<F: TFelt, Fun: AlgFn<F>> {
    f: Fun,
    pub num_vars: usize,
    _pd: PhantomData<F>,
}


impl<F: TFelt, Fun: AlgFn<F>> DenseEqSumcheck<F, Fun> {
    pub fn new(f: Fun, num_vars: usize) -> Self {
        Self { f, num_vars, _pd: PhantomData }
    }
}

pub fn gamma_rlc<F: TFelt>(gamma: F, vals: &[F]) -> F {
    let l = vals.len();
    if l == 0 {
        return F::zero();
    }
    let mut ret = vals[l-1];
    for i in 0..l-1 {
        ret = ret * gamma + vals[l-i-2];
    }
    ret
}

pub fn eq_eval_single<F: TFelt>(x1: &F, x2: &F) -> F {
    F::one() - x1 - x2 + (*x1 * *x2).double()
}

pub fn eq_eval<F: TFelt>(p1: &[F], p2: &[F]) -> F {
    p1.iter().zip_eq(p2.iter()).map(|(x1, x2)| {
        eq_eval_single(x1, x2)
    })
        .fold(F::one(), |acc, x| acc * x)
}

impl <F: TFelt, Fun: AlgFn<F>, Transcript: TArithmeticTranscript<F>> TProtocol<Transcript> for DenseEqSumcheck<F, Fun> {
    type ClaimsBefore = SinglePointClaims<F>;
    type ClaimsAfter = SinglePointClaims<F>;


    fn verify(&self, ctx: &mut Transcript, claims: Self::ClaimsBefore) -> Self::ClaimsAfter {
        let gamma = ctx.challenge();
        let SinglePointClaims { point: input_point, evs } = claims;
        let folded_claim = gamma_rlc(gamma.clone(), &evs);
        let generic_protocol_config = SumcheckProtocol::new(EqWrapper::new(GammaWrapper::new(self.f.clone(), gamma.clone())), self.num_vars);

        let EvalClaim{ ev, point: output_point } = generic_protocol_config.verify(ctx, SumClaim(folded_claim).into());

        let poly_evs = (0..self.f.n_ins()).map(|_| ctx.read()).collect_vec();

        (gamma_rlc(gamma, &self.f.exec(&poly_evs).collect_vec()) * eq_eval(&input_point, &output_point) - ev).require();
        SinglePointClaims {point: output_point, evs: poly_evs}
    }
}


impl<F: ComputationalField, Fun: AlgFn<F>, Transcript: TArithmeticTranscript<F>> TProverImpl<Transcript> for DenseEqSumcheck<F, Fun> where <F as TSigUtil>::Constants: From<u64>  {
    type Verifier = Self;
    type ProverInput = Vec<Vec<F>>;
    type ProverOutput = ();

    #[instrument(name="DenseEqSumcheck::prove", level="info", skip_all)]
    fn prove(&self, ctx: &mut Transcript, claims: <Self as TProtocol<Transcript>>::ClaimsBefore, advice: Self::ProverInput) -> (<Self as TProtocol<Transcript>>::ClaimsAfter, Self::ProverOutput) {
        let gamma = ctx.challenge();
        let SinglePointClaims { point: input_point, evs } = claims;
        let so = DenseEqSumcheckable::new(
            advice,
            self.f.clone(),
            input_point,
            evs,
        );

        let so = so.rlc(gamma);

        let generic_protocol_config = SumcheckGenericProverImpl::new(
            EqWrapper::new(GammaWrapper::new(self.f.clone(), gamma.clone())),
            self.num_vars,
        );

        let (
            EvalClaim{point: output_point, ..},
            poly_evs,
        ) = generic_protocol_config.prove(
            ctx,
            SumClaim(so.claim).into(),
            so,
        );
        let SumcheckOutput::Final(mut poly_evs) = poly_evs else {unreachable!()};

        poly_evs.pop();

        poly_evs.iter().for_each(|ev| ctx.write(ev));

        (SinglePointClaims {point: output_point, evs: poly_evs}, ())    }
}


#[cfg(test)]
mod tests {
    use super::*;
    use ark_bn254::Fq as F;
    use ark_ff::Field;
    use ark_std::{test_rng, UniformRand};
    use num_traits::{One, Zero};
    use crate::common::math::evaluate_multivar;
    use crate::transcript::transcript::ProofTranscript;

    #[derive(Clone, Copy)]
    pub struct TestFunction {}

    impl AlgFn<F> for TestFunction {
        fn exec(&self, args: &impl Index<usize, Output = F>) -> impl Iterator<Item = F> {
            [args[0] * args[1] - F::one(), args[0]*args[2], (args[0] + args[2]).pow([4]), (args[1] - F::one()).pow([3])].into_iter()
        }

        fn deg(&self) -> usize {
            4
        }

        fn n_ins(&self) -> usize {
            3
        }

        fn n_outs(&self) -> usize {
            4
        }
    }

    #[test]
    fn dense_sumcheck_with_eq_verifier_accepts_prover() {
        let rng = &mut test_rng();
        let logsize = 6;
        let polys : Vec<Vec<F>> = (0..3).map(|_| (0 .. 1 << logsize).map(|_|F::rand(rng)).collect()).collect();
        let point : Vec<F> = (0..logsize).map(|_| F::rand(rng)).collect();

        let f = TestFunction{};

        let mut output = vec![vec![]; f.n_outs()];

        for i in 0 .. 1 << logsize {
            let args : Vec<F> = polys.iter().map(|poly| poly[i]).collect();
            f.exec(&args).zip(output.iter_mut()).map(|(ret, output)| output.push(ret)).count();
        }

        let mut transcript_p = ProofTranscript::start_prover(b"test");

        let ev_claims : Vec<F> = output.iter().map(|output| evaluate_multivar(output, &point)).collect();

        let ev_claims = SinglePointClaims { point, evs: ev_claims };

        let sumcheck = DenseEqSumcheck::new(f, logsize);

        let (output_claims, _) = sumcheck.prove(&mut transcript_p, ev_claims.clone(), polys.clone());

        let proof = transcript_p.end();

        let mut transcript_v = ProofTranscript::start_verifier(b"test", proof);

        let expected_output_claims = sumcheck.verify(&mut transcript_v, ev_claims);

        assert_eq!(output_claims, expected_output_claims);

        let SinglePointClaims { point : new_point, evs } = output_claims;
        assert_eq!(polys.iter().map(|poly| evaluate_multivar(poly, &new_point)).collect_vec(), evs);
    }
}