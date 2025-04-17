use std::iter::once;
use std::marker::PhantomData;
use std::ops::Index;
use itertools::{assert_equal, Itertools};
use crate::common::algfn::AlgFnSO;
use crate::common::claims::{EvalClaim, SinglePointClaims, SumClaim};
use crate::common::math::{eq_poly, evaluate_multivar};
use crate::common::wrapper::{ComputationalField, TFelt};
use crate::components::sumcheck::dense_eq::{eq_eval, DenseSumcheckableSO};
use crate::components::sumcheck::generic::{SumcheckGenericProverImpl, SumcheckProtocol};
use crate::transcript::transcript::TArithmeticTranscript;
use crate::protocol::component::{TProtocol, TProverImpl};


pub struct MultiDenseEqSumcheck<F: TFelt> {
    pub num_vars: usize,
    _pd: PhantomData<F>,
}


impl<F: TFelt> MultiDenseEqSumcheck<F> {
    pub fn new(num_vars: usize) -> Self {
        Self { num_vars, _pd: PhantomData }
    }
}


#[derive(Clone, Debug)]
pub struct MultiPointEvalClaimPart<F> {
    poly_id: usize,
    point_id: usize,
    ev: F
}
impl<F: TFelt> MultiPointEvalClaimPart<F> {
    pub fn new(poly_id: usize, point_id: usize, ev: F) -> Self {
        Self { poly_id, point_id, ev }
    }
}

#[derive(Clone)]
pub struct MultiPointEvalClaim<F> {
    points: Vec<Vec<F>>,
    evals: Vec<MultiPointEvalClaimPart<F>>,
}

impl <F: TFelt> MultiPointEvalClaim<F> {
    pub fn new(points: Vec<Vec<F>>, evals: Vec<MultiPointEvalClaimPart<F>>) -> Self {
        Self {
            points,
            evals,
        }
    }
}


#[derive(Clone)]
pub struct MultiPointCombinator<F: TFelt> {
    sizes: Vec<usize>,
    gammas: Vec<F>
}
impl<F: TFelt> MultiPointCombinator<F> {
    pub fn new(sizes: Vec<usize>, gammas: Vec<F>) -> Self {
        Self { sizes, gammas }
    }
}

impl<F: TFelt> AlgFnSO<F> for MultiPointCombinator<F> {
    fn exec(&self, args: &impl Index<usize, Output=F>) -> F {
        let mut i = 0;
        self.sizes.iter().zip_eq(self.gammas.iter()).map(|(size, gamma)| {
            let res = (0..*size)
                .map(|_| {
                    let res = args[i];
                    i += 1;
                    res
                })
                .reduce(|l, r| l + r).unwrap() * args[i];
            i += 1;
            res * *gamma
        }).reduce(|l, r| l + r).unwrap()
    }

    fn deg(&self) -> usize {
        2
    }

    fn n_ins(&self) -> usize {
        self.sizes.len() + self.sizes.iter().sum::<usize>()
    }
}

impl <F: TFelt, Transcript: TArithmeticTranscript<F>> TProtocol<Transcript> for MultiDenseEqSumcheck<F> {
    type ClaimsBefore = MultiPointEvalClaim<F>;
    type ClaimsAfter = SinglePointClaims<F>;


    fn verify(&self, ctx: &mut Transcript, claims: Self::ClaimsBefore) -> Self::ClaimsAfter {
        let MultiPointEvalClaim { points, evals } = claims;

        let evals = evals.into_iter().enumerate()
            .sorted_by(|(_, a), (_, b)| {a.point_id.cmp(&b.point_id)})
            .chunk_by(|(_, e)| e.point_id).into_iter()
            .map(|(key, evs)| {
                (key, evs.collect_vec())
            })
            .collect_vec();
        let gamma = ctx.challenge();

        let gammas = once(gamma).chain((1..evals.len()).scan(gamma, |acc, i| {
            Some(*acc)
        })).collect_vec();

        let folded_claim = gammas.iter().zip_eq(evals.iter()).map(|(gamma_pow, (_, claims))| {
            claims.iter().map(|(_, claim)| {
                claim.ev * gamma_pow
            }).fold(F::zero(), |acc, ev| acc + ev)
        }).fold(F::zero(), |acc, ev| acc + ev);

        let f = MultiPointCombinator::new(evals.iter().map(|(_, x)| x.len()).collect_vec(), gammas);

        let generic_protocol_config = SumcheckProtocol::new(f.clone(), self.num_vars);

        let EvalClaim{ ev, point: output_point } = generic_protocol_config.verify(ctx, SumClaim(folded_claim));

        let poly_evs = (0..f.n_ins() - evals.len()).map(|_| ctx.read()).collect_vec();

        println!("{:?}", poly_evs);

        let mut i = 0;
        (
            ev -
            f.exec(
                &evals.iter().map(|(point_id, evs)| {
                    let res = poly_evs[i..(i + evs.len())].iter().cloned().chain(once(eq_eval(&points[*point_id], &output_point)));
                    i += evs.len();
                    res
                }).flatten().collect_vec()
            )
        ).require();

        SinglePointClaims {
            point: output_point,
            evs: poly_evs.into_iter()
                .zip_eq(evals.iter().map(|(_, eval)| {eval.iter().map(|(i, _)| i)}).flatten())
                .sorted_by(|&(_, x), &(_, y)| {x.cmp(&y)})
                .map(|(v, _)| v)
                .collect_vec(),
        }
    }
}

impl<F: ComputationalField, Transcript: TArithmeticTranscript<F>> TProverImpl<Transcript> for MultiDenseEqSumcheck<F> {
    type Verifier = Self;
    type ProverInput = Vec<Vec<F>>;
    type ProverOutput = ();

    fn _prove(protocol: &Self::Verifier, ctx: &mut Transcript, claims: <Self as TProtocol<Transcript>>::ClaimsBefore, advice: Self::ProverInput) -> (<Self as TProtocol<Transcript>>::ClaimsAfter, Self::ProverOutput) {
        let MultiPointEvalClaim { points, evals } = claims;
        points.iter().enumerate().for_each(|(idx, point)| {assert_eq!(point.len(), protocol.num_vars, "Wrong point len idx {}", idx)});

        let (evals, polys): (Vec<(usize, Vec<(usize, MultiPointEvalClaimPart<F>)>)>, Vec<(usize, Vec<Vec<F>>)>) = evals.into_iter().enumerate()
            .sorted_by(|(_, a), (_, b)| {a.point_id.cmp(&b.point_id)})
            .chunk_by(|(_, e)| e.point_id).into_iter()
            .map(|(key, evs)| {
                let (claims, polys): (Vec<(usize, MultiPointEvalClaimPart<F>)>, Vec<Vec<F>>) = evs.map(|(idx, claim)| {
                    let data = advice[claim.poly_id].clone();
                    println!("{:?}", claim);
                    assert_eq!(claim.ev, evaluate_multivar(&data, &points[claim.point_id]), "Wrong input claim for poly {} point {} at index {}", claim.poly_id, claim.point_id, idx);
                    ((idx, claim), data)
                }).unzip();
                ((key, claims), (key, polys))
            }).unzip();
        let gamma = ctx.challenge();

        let gammas = once(gamma).chain((1..evals.len()).scan(gamma, |acc, i| {
            Some(*acc)
        })).collect_vec();

        let folded_claim = gammas.iter().zip_eq(evals.iter()).map(|(gamma_pow, (_, claims))| {
            claims.iter().map(|(_, claim)| {
                claim.ev * gamma_pow
            }).fold(F::zero(), |acc, ev| acc + ev)
        }).fold(F::zero(), |acc, ev| acc + ev);


        let f = MultiPointCombinator::new(evals.iter().map(|(_, x)| x.len()).collect_vec(), gammas);


        let so = DenseSumcheckableSO::<F, MultiPointCombinator<F>>::new(
            polys.into_iter()
                .map(|(point_idx, polys)| {
                    polys.into_iter()
                        .chain(once(eq_poly(&points[point_idx])))
                })
                .flatten()
                .collect_vec(),
            f.clone(),
            protocol.num_vars,
            folded_claim
        );

        let generic_protocol_config = SumcheckProtocol::new(
            f.clone(),
            protocol.num_vars,
        );

        let (
            EvalClaim{point: output_point, ev},
            mut poly_evs,
        ) = generic_protocol_config.prove::<SumcheckGenericProverImpl<_, _, _>>(
            ctx,
            SumClaim(so.claim),
            so,
        );

        assert_eq!(
            ev,
            f.exec(
                &poly_evs
            ),
            "Final combinator check has failed."
        );


        let mut i = 0;
        for (_, group) in evals.iter() {
            for _ in 0..group.len() {
                ctx.write(&poly_evs[i]);
                i += 1
            }
            poly_evs.remove(i);
        }


        (SinglePointClaims {
            point: output_point,
            evs: poly_evs.into_iter()
                .zip_eq(evals.iter().map(|(_, eval)| {eval.iter().map(|(i, _)| i)}).flatten())
                .sorted_by(|&(_, x), &(_, y)| {x.cmp(&y)})
                .map(|(v, _)| v)
                .collect_vec(),
        }, ())
}

    }
#[cfg(test)]
mod tests {
    use ark_std::rand::RngCore;
use super::*;
    use crate::transcript::transcript::tests::ManualTestTranscript as ManualTestTranscript;
    use ark_bn254::Fq as F;
    use ark_ff::Field;
    use ark_std::{test_rng, UniformRand};
    use ark_std::rand::Rng;
    use num_traits::{One, Zero};
    use crate::common::math::evaluate_multivar;
    #[test]
    fn verifier_accepts_prover() {
        let rng = &mut test_rng();
        for _ in 0..20 {
            let logsize = 6;
            let num_points = rng.next_u64() as usize % 10 + 5;
            let num_polys = rng.next_u64() as usize % 10 + 5;
            let num_evals = rng.next_u64() as usize % 10 + 5;
            let points: Vec<Vec<F>> = (0..num_points).map(|_| (0..logsize).map(|_| F::rand(rng)).collect()).collect();
            let polys: Vec<Vec<F>> = (0..num_polys).map(|_| (0..1 << logsize).map(|_| F::rand(rng)).collect()).collect();
            let polys_ids: Vec<usize> = (0..num_evals).map(|i| rng.gen::<usize>() % polys.len()).collect();
            let point_ids: Vec<usize> = (0..num_evals).map(|_| rng.gen::<usize>() % points.len()).collect();

            let evals = polys_ids.iter().zip_eq(point_ids.iter()).map(|(&poly_id, &point_id)| {
                MultiPointEvalClaimPart {
                    poly_id,
                    point_id,
                    ev: evaluate_multivar(&polys[poly_id], &points[point_id]),
                }
            }).collect_vec();

            let claim = MultiPointEvalClaim {
                points: points.clone(),
                evals,
            };

            let sumcheck = MultiDenseEqSumcheck::new(logsize);

            let mut transcript_p = ManualTestTranscript::new((0..1000).map(|_| F::rand(rng)).collect_vec());

            let (output_claims, _) = sumcheck.prove::<MultiDenseEqSumcheck<_, >>(&mut transcript_p, claim.clone(), polys.clone());

            let proof = transcript_p.end();
            let mut transcript_v = transcript_p;

            let expected_output_claims = sumcheck.verify(&mut transcript_v, claim.clone());

            assert_eq!(output_claims, expected_output_claims);

            let SinglePointClaims { point: new_point, evs } = output_claims;
            assert_eq!(claim.evals.iter().map(|part| evaluate_multivar(&polys[part.poly_id], &new_point)).collect_vec(), evs);
        }
    }
}