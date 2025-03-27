use std::cmp::min;
use rayon::iter::ParallelIterator;
use std::iter::repeat_n;
use std::marker::PhantomData;
use std::ops::Index;
use itertools::Itertools;
use rayon::current_num_threads;
use rayon::prelude::IntoParallelIterator;
use crate::common::algfn::{AlgFn, AlgFnSO};
use crate::common::claims::{EvalClaim, SinglePointClaims, SumClaim};
use crate::common::math::{bind_dense_poly, eq_poly_sequence_last, evaluate_univar};
use crate::common::wrapper::{PolyOps, TPrimeField};
use crate::components::sumcheck::algfn_wrappers::{EqWrapper, GammaWrapper};
use crate::components::sumcheck::generic::{SumcheckGenericProverImpl, SumcheckProtocol};
use crate::components::sumcheck::sumcheckable::{FoldToSumcheckable, Sumcheckable};
use crate::dialects::dialect::TArithmeticDialect;
use crate::protocol::component::{TProtocol, TProverImpl};



#[derive(Clone, Debug)]
pub struct DenseSumcheckObjectSO<F: TPrimeField, Fun: AlgFnSO<F>> {
    pub polys: Vec<Vec<F>>,
    challenges: Vec<F>,
    f: Fun,
    num_vars: usize,
    round_idx: usize,
    cached_unipoly: Option<Vec<F>>,

    pub claim: F,
}

impl<F: TPrimeField, Fun: AlgFnSO<F>> DenseSumcheckObjectSO<F, Fun> {
    pub fn new(polys: Vec<Vec<F>>, f: Fun, num_vars: usize, claim_hint: F) -> Self {
        let l = polys.len();
        assert_eq!(l, f.n_ins());
        for i in 0..l {
            assert_eq!(polys[i].len(), 1 << num_vars);
        }
        Self { polys, f, num_vars, round_idx: 0, cached_unipoly: None, challenges: vec![], claim: claim_hint }
    }
}

impl<F: TPrimeField, Fun: AlgFnSO<F>> Sumcheckable<F> for DenseSumcheckObjectSO<F, Fun> {
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

    fn unipoly(&mut self) -> Vec<F> {
        assert!(self.round_idx < self.num_vars, "the protocol has already ended");

        match self.cached_unipoly.as_ref() {
            Some(p) => {return p.clone()},
            None => {
                let half = 1 << (self.num_vars - self.round_idx - 1);
                let n_polys = self.polys.len();

                let num_tasks = 8 * current_num_threads();

                let task_size = (half + num_tasks - 1) / num_tasks;
                // todo (rebenkoy): par
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

                self.cached_unipoly = Some(total_acc);
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
pub struct DenseEqSumcheckObject<F: TPrimeField, Fun: AlgFn<F>> {
    polys: Vec<Vec<F>>,
    point: Vec<F>,
    f: Fun,
    claim_hint: Vec<F>,
}

impl<F: TPrimeField, Fun: AlgFn<F>> DenseEqSumcheckObject<F, Fun> {
    pub fn new(polys: Vec<Vec<F>>, f: Fun, point: Vec<F>, claim_hint: Vec<F>) -> Self {
        assert!(claim_hint.len() == f.n_outs());
        Self { polys, f, point, claim_hint }
    }
}

impl<F: TPrimeField, Fun: AlgFn<F>> FoldToSumcheckable<F> for DenseEqSumcheckObject<F, Fun> {
    type Target = DenseSumcheckObjectSO<F, EqWrapper<F, GammaWrapper<F, Fun>>>; // to be replaced

    fn rlc(self, gamma: F) -> Self::Target {
        let gamma_wrapper = GammaWrapper::new(self.f, gamma);
        let eq_wrapper = EqWrapper::new(gamma_wrapper);

        let claim_hint = gamma_rlc(gamma, &self.claim_hint);
        let num_vars = self.point.len();

        let mut polys = self.polys;
        let eq = eq_poly_sequence_last(&self.point).unwrap();
        polys.push(eq);

        Self::Target::new(
            polys,
            eq_wrapper,
            num_vars,
            claim_hint,
        )
    }
}

pub struct DenseEqSumcheck<F: TPrimeField, Fun: AlgFn<F>> {
    f: Fun,
    pub num_vars: usize,
    _pd: PhantomData<F>,
}


impl<F: TPrimeField, Fun: AlgFn<F>> DenseEqSumcheck<F, Fun> {
    pub fn new(f: Fun, num_vars: usize) -> Self {
        Self { f, num_vars, _pd: PhantomData }
    }
}

pub fn gamma_rlc<F: TPrimeField>(gamma: F, vals: &[F]) -> F {
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

pub fn eq_eval<F: TPrimeField>(p1: &[F], p2: &[F]) -> F {
    p1.iter().zip_eq(p2.iter()).map(|(x1, x2)| {
        F::one() - x1 - x2 + (*x1 * *x2).double()
    })
        .fold(F::one(), |acc, x| acc * x)
}

impl <F: TPrimeField, Fun: AlgFn<F>, Dialect: TArithmeticDialect<F>> TProtocol<Dialect> for DenseEqSumcheck<F, Fun> {
    type ClaimsBefore = SinglePointClaims<F>;
    type ClaimsAfter = SinglePointClaims<F>;


    fn verify(&self, ctx: &mut Dialect, claims: Self::ClaimsBefore) -> Self::ClaimsAfter {
        let degrees = repeat_n(self.f.deg() + 1, self.num_vars);
        let gamma = ctx.challenge();
        let SinglePointClaims { point: input_point, evs } = claims;
        let folded_claim = gamma_rlc(gamma.clone(), &evs);
        let generic_protocol_config = SumcheckProtocol::new(EqWrapper::new(GammaWrapper::new(self.f.clone(), gamma.clone())), self.f.deg());

        let EvalClaim{ ev, point: output_point } = generic_protocol_config.verify(ctx, SumClaim(folded_claim));

        let poly_evs = (0..self.f.n_ins()).map(|_| ctx.read()).collect_vec();

        assert_eq!(gamma_rlc(gamma, &self.f.exec(&poly_evs).collect_vec()) * eq_eval(&input_point, &output_point), ev, "Final combinator check has failed.");
        SinglePointClaims {point: output_point, evs: poly_evs}
    }
}


impl<F: TPrimeField, Fun: AlgFn<F>, Dialect: TArithmeticDialect<F>> TProverImpl<Dialect> for DenseEqSumcheck<F, Fun> {
    type Verifier = Self;
    type ProverInput = Vec<Vec<F>>;
    type ProverOutput = ();

    fn _prove(protocol: &Self::Verifier, ctx: &mut Dialect, claims: <Self as TProtocol<Dialect>>::ClaimsBefore, advice: Self::ProverInput) -> (<Self as TProtocol<Dialect>>::ClaimsAfter, Self::ProverOutput) {
        let gamma = ctx.challenge();
        let SinglePointClaims { point: input_point, evs } = claims;
        let so = DenseEqSumcheckObject::new(
            advice,
            protocol.f.clone(),
            input_point,
            evs,
        );

        let so = so.rlc(gamma);

        let generic_protocol_config = SumcheckProtocol::new(EqWrapper::new(GammaWrapper::new(protocol.f.clone(), gamma.clone())), protocol.f.deg());

        let (EvalClaim{point: output_point, ..}, mut poly_evs) = generic_protocol_config.prove::<SumcheckGenericProverImpl<_, _, _>>(ctx, SumClaim(so.claim), so);

        poly_evs.pop();

        poly_evs.iter().for_each(|ev| ctx.write(ev));

        (SinglePointClaims {point: output_point, evs: poly_evs}, ())    }
}



