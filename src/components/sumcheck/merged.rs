use std::collections::VecDeque;
use std::marker::PhantomData;
use itertools::Itertools;
use crate::common::algfn::AlgFnSO;
use crate::common::claims::{EvalClaim, SinglePointClaims, SumClaim};
use crate::common::wrapper::{ComputationalField, TFelt, TSigUtil};
use crate::components::sumcheck::algfn_wrappers::RLCAlgFn;
use crate::components::sumcheck::dense::DenseSumcheck;
use crate::components::sumcheck::dense_eq::DenseSumcheckableSO;
use crate::components::sumcheck::generic::{SumcheckGenericProverImpl, SumcheckOutput, SumcheckProtocol};
use crate::protocol::component::{TProtocol, TProverImpl};
use crate::transcript::transcript::TArithmeticTranscript;

pub struct MergedSumcheck<F: TFelt, Fun: AlgFnSO<F>> {
    pub num_vars: Vec<usize>,
    pub f: Fun,
    _pd: PhantomData<F>
}

impl<F: TFelt, Fun: AlgFnSO<F>> MergedSumcheck<F, Fun> {
    pub fn new(f: Fun, num_vars: Vec<usize>) -> Self {
        Self {
            num_vars,
            f,
            _pd: Default::default(),
        }
    }
}

impl<F: TFelt, Fun: AlgFnSO<F>, Transcript: TArithmeticTranscript<F>> TProtocol<Transcript> for MergedSumcheck<F, Fun>
{
    type ClaimsBefore = Vec<SumClaim<F>>;
    type ClaimsAfter = Vec<SinglePointClaims<F>>;

    fn verify(&self, ctx: &mut Transcript, claims: Self::ClaimsBefore) -> Self::ClaimsAfter {
        let evs = claims.iter().map(|claim| claim.0).collect_vec();
        let (reordering, mut num_vars, mut claims): (Vec<usize>, Vec<usize>, Vec<F>) =
            self.num_vars
                .iter()
                .enumerate()
                .zip(evs.iter())
                .sorted_by(|(a, _), (b, _)| b.1.cmp(a.1))  // decreasing order
                .map(|((a, b), c)| (a, b, c))
                .multiunzip();

        let current_num_vars = num_vars.get(0);
        if current_num_vars.is_none() { panic!("num_vars is empty"); }
        let mut current_num_vars = *current_num_vars.unwrap();
        let current_claim = claims.get(0);
        if current_claim.is_none() { panic!("claims are empty"); }
        let mut current_claim = *current_claim.unwrap();
        let mut function = RLCAlgFn::new(self.f.clone());
        let gamma = ctx.challenge();
        let mut current_gamma_pow = F::one();
        let mut current_point = vec![];

        for i in 1..(num_vars.len() + 1) {
            let mut rerun = true;
            let next_num_vars = *num_vars.get(i).unwrap_or(&0);
            while rerun {
                rerun = false;
                match next_num_vars == current_num_vars {
                    false => {
                        let partial_sumcheck = SumcheckProtocol::new_partial(function.clone(), current_num_vars, current_num_vars - next_num_vars);
                        let claim = partial_sumcheck.verify(ctx, EvalClaim{ ev: current_claim, point: current_point });
                        current_point = claim.point;
                        current_claim = claim.ev;
                        if next_num_vars != 0 {
                            current_num_vars = next_num_vars;
                            rerun = true;
                        }
                    }
                    true => {
                        current_gamma_pow *= gamma;
                        function.extend(current_gamma_pow);
                        current_claim += current_gamma_pow * claims[i];
                    }
                }
            }
        }
        println!("V: {:?}", current_claim);

        let poly_evs = (0..function.n_ins()).map(|_| ctx.read()).collect_vec();

        (function.exec(&poly_evs) - current_claim).require();

        poly_evs.into_iter()
            .chunks(self.f.n_ins())
            .into_iter()
            .zip_eq(reordering.iter())
            .sorted_by(|(_, a), (_, b)| a.cmp(b))
            .map(|(a, _)| a)
            .zip_eq(self.num_vars.iter())
            .map(|(chunk, logsize)| {
                SinglePointClaims {
                    evs: chunk.collect_vec(),
                    point: current_point[current_point.len() - *logsize..].to_vec(),
                }
            })
            .collect_vec()
    }
}

impl<F: ComputationalField, Fun: AlgFnSO<F>, Transcript: TArithmeticTranscript<F>> TProverImpl<Transcript> for MergedSumcheck<F, Fun> where <F as TSigUtil>::Constants: From<u64> {
    type Verifier = Self;
    type ProverInput = Vec<Vec<Vec<F>>>;
    type ProverOutput = ();

    fn prove(&self, ctx: &mut Transcript, claims: <Self::Verifier as TProtocol<Transcript>>::ClaimsBefore, mut advice: Self::ProverInput) -> (<Self::Verifier as TProtocol<Transcript>>::ClaimsAfter, Self::ProverOutput) {
        let evs = claims.iter().map(|claim| claim.0).collect_vec();
        let (reordering, mut num_vars, mut claims, mut advice): (Vec<usize>, Vec<usize>, Vec<F>, VecDeque<Vec<Vec<F>>>) =
            self.num_vars
                .iter()
                .enumerate()
                .zip(evs.iter())
                .zip(advice.into_iter())
                .sorted_by(|((a, _), _), ((b, _), _)| b.1.cmp(a.1))  // decreasing order
                .map(|(((a, b), c), d)| (a, b, c, d))
                .multiunzip();

        let mut current_num_vars = *num_vars.get(0).expect("num_vars is empty");
        let mut current_claim = *claims.get(0).expect("claims are empty");
        let mut function = RLCAlgFn::new(self.f.clone());
        let gamma = ctx.challenge();
        let mut current_gamma_pow = F::one();
        let mut current_point = vec![];
        let mut current_polys = Some(advice.pop_front().expect("advice empty"));

        let mut poly_evs = None;

        for i in 1..(num_vars.len() + 1) {
            let mut rerun = true;
            let next_num_vars = *num_vars.get(i).unwrap_or(&0);
            while rerun {
                rerun = false;
                match next_num_vars == current_num_vars {
                    false => {
                        let partial_sumcheck = SumcheckGenericProverImpl::new_partial(function.clone(), current_num_vars, current_num_vars - next_num_vars);

                        let current_sumcheckable = DenseSumcheckableSO::new(
                            current_polys.take().unwrap(),
                            function.clone(),
                            current_num_vars,
                            current_claim,
                        );
                        let (claim, sumcheck_output) = partial_sumcheck.prove(ctx, EvalClaim{ ev: current_claim, point: current_point }, current_sumcheckable);
                        match sumcheck_output {
                            SumcheckOutput::Final(out_poly_evs) => {
                                current_polys = None;
                                poly_evs = Some(out_poly_evs);
                            }
                            SumcheckOutput::Partial(out_sumcheckable) => {
                                current_num_vars = next_num_vars;
                                rerun = true;
                                current_polys = Some(out_sumcheckable.polys);
                            }
                        }
                        current_point = claim.point;
                        current_claim = claim.ev;
                    }
                    true => {
                        current_gamma_pow *= gamma;
                        current_polys.as_mut().unwrap().extend(advice.pop_front().expect("advice empty"));
                        function.extend(current_gamma_pow);
                        current_claim += current_gamma_pow * claims[i];
                    }
                }
            }
        }
        println!("P: {:?}", current_claim);

        let poly_evs = poly_evs.unwrap();
        poly_evs.iter().for_each(|ev| ctx.write(ev));

        (function.exec(&poly_evs) - current_claim).require();
        (
            poly_evs.into_iter()
                .chunks(self.f.n_ins())
                .into_iter()
                .zip_eq(reordering.iter())
                .sorted_by(|(_, a), (_, b)| a.cmp(b))
                .map(|(a, _)| a)
                .zip_eq(self.num_vars.iter())
                .map(|(chunk, logsize)| {
                    SinglePointClaims {
                        evs: chunk.collect_vec(),
                        point: current_point[current_point.len() - *logsize..].to_vec(),
                    }
                })
                .collect_vec(),
            ()
        )
    }
}


#[cfg(test)]
mod tests {
    use std::ops::Index;
    use super::*;
    use crate::common::wrapper::TFeltUtil;
    use ark_bn254::Fq as F;
    use ark_std::{test_rng, UniformRand};
    //use num_traits::One;
    use crate::common::math::evaluate_multivar;
    use crate::transcript::transcript::ProofTranscript;

    #[derive(Clone, Copy)]
    pub struct TestFunction {}

    impl AlgFnSO<F> for TestFunction {
        fn exec(&self, args: &impl Index<usize, Output = F>) -> F {
            args[0] * args[1] - F::one()
        }

        fn deg(&self) -> usize {
            2
        }

        fn n_ins(&self) -> usize {
            2
        }
    }

    #[test]
    fn dense_sumcheck_with_verifier_accepts_prover() {
        let rng = &mut test_rng();
        let logsizes = vec![4, 4, 5, 6, 7, 6, 5, 5, 4, 4];
        let polys : Vec<Vec<Vec<F>>> = logsizes.iter().map(|logsize| (0..2).map(|_| (0 .. 1 << logsize).map(|_|F::rand(rng)).collect()).collect()).collect();

        let f = TestFunction{};

        let mut output = vec![];

        for (idx, logsize) in logsizes.iter().enumerate() {
            output.push(vec![]);
            for i in 0..1 << logsize {
                let args: Vec<F> = polys[idx].iter().map(|poly| poly[i]).collect();
                output[idx].push(f.exec(&args));
            }
        }

        let mut transcript_p = ProofTranscript::start_prover(b"test");

        let claim = output.iter().map(|p| SumClaim(p.iter().sum())).collect_vec();

        let sumcheck = MergedSumcheck::new(f, logsizes.clone());
        let (output_claims, _) = sumcheck.prove(&mut transcript_p, claim.clone().into(), polys.clone());
        let proof = transcript_p.end();
        let mut transcript_v = ProofTranscript::start_verifier(b"test", proof);

        let expected_output_claims = sumcheck.verify(&mut transcript_v, claim.into());
        assert_eq!(output_claims, expected_output_claims);

        for (poly_group, output) in polys.iter().zip_eq(output_claims.iter()) {
            assert_eq!(
                poly_group.iter()
                    .map(|poly| evaluate_multivar(poly, &output.point))
                    .collect_vec(),
                output.evs,
            )
        }
    }
}



