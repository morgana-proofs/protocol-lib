use crate::common::algfn::AlgFnUtils;
use std::marker::PhantomData;
use ark_ff::PrimeField;
use itertools::Itertools;
use crate::common::algfn::AlgFn;
use crate::common::claims::{SinglePointClaims, SumClaim};
use crate::common::wrapper::{PolyOps, TPrimeField};
use crate::components::splits::split::{SplitAt, SplitIdx};
use crate::components::sumcheck::dense_eq::DenseEqSumcheck;
use crate::dialects::dialect::TArithmeticDialect;
use crate::protocol::component::{TProtocol, TProverImpl};

#[derive(Debug, Clone, Copy)]
pub struct LogupLayerFn<F: TPrimeField> {
    _marker: PhantomData<F>,
}

impl<F: TPrimeField> LogupLayerFn<F> {
    pub fn new() -> Self {
        Self { _marker: PhantomData }
    }
}

impl<F: TPrimeField> AlgFn<F> for LogupLayerFn<F>{
    fn exec(&self, args: &impl std::ops::Index<usize, Output = F>) -> impl Iterator<Item = F> {
        [
            args[0] * args[3] + args[1] * args[2], // ad + bc
            args[1] * args[3]                      // bd
        ].into_iter()
    }

    fn deg(&self) -> usize {
        2
    }

    fn n_ins(&self) -> usize {
        4
    }

    fn n_outs(&self) -> usize {
        2
    }
}

pub struct LogupMainphase<F: TPrimeField> {
    pub logsizes: Vec<usize>,
    pub do_initial_split: bool,
    pub input_permutation: Vec<usize>,
    _pd: PhantomData<F>
}

impl<F: TPrimeField> LogupMainphase<F> {

    /// Assumes that first two logsizes have the same length - i.e. they corresponding polynomial is already split.
    pub fn new(logsizes: Vec<usize>) -> Self {
        let (input_permutation, logsizes): (Vec<usize>, Vec<usize>) = logsizes.iter().enumerate().sorted_by(|(_, a), (_, b)| b.cmp(a)).unzip();

        let do_initial_split = logsizes.len() == 1 || logsizes[0] != logsizes[1];

        Self {
            logsizes,
            do_initial_split,
            input_permutation,
            _pd: PhantomData,
        }
    }

    pub fn make_witness(&self, input: Vec<[Vec<F>; 2]>) -> (Vec<[Vec<F>; 2]>, [F; 2]) {
        let mut input = input.into_iter().map(|x| Some(x)).collect_vec();
        let input = self.input_permutation.iter().map(|i| input[*i].take().unwrap()).collect_vec();

        input.iter().zip_eq(self.logsizes.iter()).for_each(|(fraction_arr, logsize)| assert!(fraction_arr[0].len() == 1 << logsize && fraction_arr[1].len() == 1 << logsize));


        let mut input = input;
        input.reverse();

        let mut i = 0;
        let mut layers : Vec<[Vec<F>; 2]> = vec![];
        layers.push(input.pop().unwrap());
        if !self.do_initial_split {
            layers.push(input.pop().unwrap());
        } else {
            let (nl, nr) = layers[0][0].split_at(1 << (self.logsizes[0] - 1));
            let (dl, dr): (&[F], &[F]) = layers[0][1].split_at(1 << (self.logsizes[0] - 1));
            let l1 = [nl.to_vec(), dl.to_vec()];
            let l2 = [nr.to_vec(), dr.to_vec()];
            layers.push(l1);
            layers.push(l2);
            i += 1;
        }


        let f = LogupLayerFn::new();

        // This cycle is concerned with 2 last elements of layers (they always have the same size). If the next advice has the same size, it maps them without splitting, and fetches next advice.
        // If the next advice is smaller, then it maps and splits.
        // First option will be chosen if there is no next advice and size == 1, in which case it will just push the final mapping result and break from the cycle.
        loop {
            let next_size = input.last().map_or(1, |arr|arr[0].len());
            let curr_size = layers[i][0].len();

            if curr_size == next_size {
                let a0 = &layers[i];
                let a1 = &layers[i+1];
                let out = f.map(&[&a0[0], &a0[1], &a1[0], &a1[1]]);
                layers.push(out.try_into().unwrap());
                if let Some(adv) = input.pop() {
                    layers.push(adv)
                } else {break};
                i += 2;

            } else if curr_size > next_size {
                let a0 = &layers[i];
                let a1 = &layers[i+1];
                let out = f.map_split_hi(&[&a0[0], &a0[1], &a1[0], &a1[1]]);
                let [out0, out1] = out;
                layers.push(out0.try_into().unwrap());
                layers.push(out1.try_into().unwrap());
                i += 2;
            } else {
                unreachable!()
            }
        }

        let tmp = layers.pop().unwrap();
        assert!(tmp[0].len() == 1);
        assert!(tmp[1].len() == 1); // sanity

        let n = tmp[0][0];
        let d = tmp[1][0];

        (layers, [n, d])
    }
}

impl<F: TPrimeField, Dialect: TArithmeticDialect<F>> TProtocol<Dialect> for LogupMainphase<F> {
    type ClaimsBefore = SumClaim<F>;
    type ClaimsAfter = Vec<SinglePointClaims<F>>;

    fn verify(&self, ctx: &mut Dialect, claims: Self::ClaimsBefore) -> Self::ClaimsAfter {
        let claims = claims.0;
        let f = LogupLayerFn::<F>::new();




        let [num, denom] = [
            ctx.read(),
            ctx.read(),
        ];
        assert!(denom != F::zero());
        assert!(num == denom * claims);




        let mut logsizes = self.logsizes.clone();

        let mut curr_logsize = 0;
        let mut running_claim = SinglePointClaims{ point: vec![], evs: vec![num, denom] };
        let mut accumulated_claims = vec![];

        let tmp =
            loop {
                let incoming_logsize = logsizes.last().unwrap();

                let protocol = DenseEqSumcheck::new(f.clone(), curr_logsize);

                let claim_4 = protocol.verify(
                    ctx,
                    running_claim.clone()
                );


                if *incoming_logsize == curr_logsize {
                    if (logsizes.len() == 2 && !self.do_initial_split) || (logsizes.len() == 1 && self.do_initial_split) {
                        break claim_4
                    }
                    running_claim = SinglePointClaims{ point: claim_4.point.clone(), evs: vec![claim_4.evs[0], claim_4.evs[1]] };
                    accumulated_claims.push(SinglePointClaims{ point: claim_4.point, evs: vec![claim_4.evs[2], claim_4.evs[3]] });
                    logsizes.pop();
                } else {
                    let split = SplitAt::new(SplitIdx::HI(0), 2);
                    running_claim = split.verify(ctx, claim_4);
                    curr_logsize += 1;
                }
                if self.do_initial_split && logsizes.len() == 1 && logsizes.last().unwrap() == &curr_logsize {
                    break running_claim;
                }
            };


        if self.do_initial_split {
            accumulated_claims.push(tmp);
        } else {
            accumulated_claims.push(SinglePointClaims{ point: tmp.point.clone(), evs: vec![tmp.evs[0], tmp.evs[1]] });
            accumulated_claims.push(SinglePointClaims{ point: tmp.point.clone(), evs: vec![tmp.evs[2], tmp.evs[3]] });
        }

        self.input_permutation.iter()
            .zip(
                accumulated_claims
                    .into_iter()
                    .rev()
            )
            .sorted_by(|(a, _), (b, _)| a.cmp(b))
            .map(|(_, x)| x)
            .collect_vec()
    }
}

impl<F: TPrimeField, Dialect: TArithmeticDialect<F>> TProverImpl<Dialect> for LogupMainphase<F> {
    type Verifier = Self;
    type ProverInput = Vec<[Vec<F>; 2]>;
    type ProverOutput = ();

    fn _prove(protocol: &Self::Verifier, ctx: &mut Dialect, claims: <Self::Verifier as TProtocol<Dialect>>::ClaimsBefore, advice: Self::ProverInput) -> (<Self::Verifier as TProtocol<Dialect>>::ClaimsAfter, Self::ProverOutput) {
        let f = LogupLayerFn::<F>::new();

        let (mut witness, [num, denom]) = protocol.make_witness(advice);

        assert!(denom != F::zero());
        assert!(num == denom.clone() * claims.0);

        ctx.write(&num);
        ctx.write(&denom);




        let mut logsizes = protocol.logsizes.clone();
        let mut curr_logsize = 0;
        let mut running_claim = SinglePointClaims{ point: vec![], evs: vec![num, denom] };
        let mut accumulated_claims = vec![];

        let tmp =
            loop {
                let incoming_logsize = logsizes.last().unwrap();

                if witness.len() == 1 {
                    break running_claim;
                }
                
                let proto = DenseEqSumcheck::new(f, curr_logsize);

                let [advice_r_0, advice_r_1] = witness.pop().unwrap();
                let [advice_l_0, advice_l_1] = witness.pop().unwrap();
                let advice = vec![advice_l_0, advice_l_1, advice_r_0, advice_r_1];
                println!("Reducing claim with advice sizes: {:?} through DenseEqSumcheck", advice.iter().map(|x| x.len()).collect_vec());
                let (claim_4, _) = proto.prove::<DenseEqSumcheck<_,_,>>(
                    ctx,
                    running_claim.clone(),
                    advice
                );

                if *incoming_logsize == curr_logsize {
                    if (logsizes.len() == 2 && !protocol.do_initial_split) || (logsizes.len() == 1 && protocol.do_initial_split) {
                        break claim_4
                    }
                    running_claim = SinglePointClaims{ point: claim_4.point.clone(), evs: vec![claim_4.evs[0], claim_4.evs[1]] };
                    accumulated_claims.push(SinglePointClaims{ point: claim_4.point, evs: vec![claim_4.evs[2], claim_4.evs[3]] });
                    logsizes.pop();
                } else {
                    let split = SplitAt::new(SplitIdx::HI(0), 2);
                    println!("Reducing claim through Split, witness sizes: {:?}", witness.iter().map(|x| x[0].len()).collect_vec());
                    (running_claim, _) = split.prove::<SplitAt<_,>>(ctx, claim_4, ());
                    curr_logsize += 1;
                }
            };

        if protocol.do_initial_split {
            accumulated_claims.push(tmp);
        } else {
            accumulated_claims.push(SinglePointClaims{ point: tmp.point.clone(), evs: vec![tmp.evs[0], tmp.evs[1]] });
            accumulated_claims.push(SinglePointClaims{ point: tmp.point.clone(), evs: vec![tmp.evs[2], tmp.evs[3]] });
        }

        accumulated_claims = protocol.input_permutation.iter()
            .zip(
                accumulated_claims
                    .into_iter()
                    .rev()
            )
            .sorted_by(|(a, _), (b, _)| a.cmp(b))
            .map(|(_, x)| x)
            .collect_vec();

        (accumulated_claims, ())    }
}

//
//
// #[derive(Debug, Clone, Copy)]
// pub struct LogupFirstLayerFn<F: TPrimeField> {
//     _marker: PhantomData<F>,
// }
//
// impl<F: TPrimeField> LogupFirstLayerFn<F> {
//     pub fn new() -> Self {
//         Self { _marker: PhantomData }
//     }
// }
//
// impl<F: TPrimeField> AlgFn<F> for LogupFirstLayerFn<F>{
//     fn exec(&self, args: &impl std::ops::Index<usize, Output = F>) -> impl Iterator<Item = F> { // a, b aka 1/a + 1/b
//         [
//             args[0] + args[1], // a + b
//             args[0] * args[1], // ab
//         ].into_iter()
//     }
//
//     fn deg(&self) -> usize {
//         2
//     }
//
//     fn n_ins(&self) -> usize {
//         2
//     }
//
//     fn n_outs(&self) -> usize {
//         2
//     }
// }
//
//
// pub struct SingleLogupMainphase<F: TPrimeField> {
//     _pd: PhantomData<F>,
//     logsize: usize
// }
//
// impl<F: TPrimeField> SingleLogupMainphase<F> {
//     pub fn new(logsize: usize) -> Self {
//         Self { _pd: PhantomData, logsize }
//     }
// }
//
// impl<F: TPrimeField, Dialect: TArithmeticDialect<F>> TProtocol<Dialect> for SingleLogupMainphase<F> {
//     type ClaimsBefore = SumClaim<F>;
//     type ClaimsAfter = SinglePointClaims<F>;
//
//     fn verify(&self, ctx: &mut Dialect, claims: Self::ClaimsBefore) -> Self::ClaimsAfter {
//         let mainphase = LogupMainphase::new(
//             vec![self.logsize - 2; 2]
//         );
//         let mut claims = mainphase.verify(
//             ctx,
//             claims,
//         );
//
//         assert!(claims.len() == 2);
//         let rclaim = claims.pop().unwrap();
//         let lclaim = claims.pop().unwrap();
//         assert!(rclaim.point == lclaim.point);
//         let claims = SinglePointClaims {
//             evs: lclaim.evs.into_iter().chain(rclaim.evs.into_iter()).collect(),
//             point: lclaim.point,
//         };
//
//         let split = SplitAt::new(SplitIdx::HI(0), 2);
//         let claims = split.verify(ctx, claims);
//
//         let f = LogupLayerFn::<F>::new();
//         let sumcheck = DenseEqSumcheck::new(f, self.logsize - 1);
//         let claims = sumcheck.verify(ctx, claims);
//
//         let claims = split.verify(ctx, claims);
//
//         claims
//     }
// }
//
// impl<F: TPrimeField, Dialect: TArithmeticDialect<F>> TProverImpl<Dialect> for SingleLogupMainphase<F> {
//     type Verifier = Self;
//     type ProverInput = Vec<F>;
//     type ProverOutput = ();
//
//     fn _prove(protocol: &Self::Verifier, ctx: &mut Dialect, claims: <Self::Verifier as TProtocol<Dialect>>::ClaimsBefore, advice: Self::ProverInput) -> (<Self::Verifier as TProtocol<Dialect>>::ClaimsAfter, Self::ProverOutput) {
//         assert_eq!(advice.len(), 1 << protocol.logsize);
//         let f = LogupLayerFn::<F>::new();
//         let (l, r) = advice.split_at(1 << (protocol.logsize - 1));
//         let [ml, mr] = f.map_split_hi(&[l, r]);
//
//         let mainphase = LogupMainphase::new(
//             vec![protocol.logsize - 2; 2]
//         );
//         let (mut claims, _) = mainphase.prove::<LogupMainphase<_>>(
//             ctx,
//             claims,
//             ml.iter().zip(mr.iter()).map(|(l, r)| [l.clone(), r.clone()]).collect(),
//         );
//         assert!(claims.len() == 2);
//         let rclaim = claims.pop().unwrap();
//         let lclaim = claims.pop().unwrap();
//         assert!(rclaim.point == lclaim.point);
//         let claims = SinglePointClaims {
//             evs: lclaim.evs.into_iter().chain(rclaim.evs.into_iter()).collect(),
//             point: lclaim.point,
//         };
//
//         let split = SplitAt::new(SplitIdx::HI(0), 2);
//         let (claims, _) = split.prove::<SplitAt<_,>>(ctx, claims, ());
//
//         let sumcheck = DenseEqSumcheck::new(f, protocol.logsize - 1);
//         let (claims, _) = sumcheck.prove::<DenseEqSumcheck<_,_,>>(ctx, claims, vec![l.to_vec(), r.to_vec()]);
//
//         let (claims, _) = split.prove::<SplitAt<_,>>(ctx, claims, ());
//
//         (claims, ())
//     }
// }
//
// pub struct SingleLogup<F: TPrimeField> {
//     logsize: usize,
//     _pd: PhantomData<F>,
// }
//
//
// pub struct SingleLookupInput<F: TPrimeField> {
//     values: Vec<F>,
//     accesses: Vec<F>,
//     table: Vec<F>,
//     indexes: Option<Vec<usize>>,
// }
//
// impl<F: TPrimeField, Dialect: TArithmeticDialect<F>> TProverImpl<Dialect> for SingleLogup<F> {
//     type Verifier = SingleLogupMainphase<F>;
//     type ProverInput = SingleLookupInput<F>;
//     type ProverOutput = ();
//
//     fn _prove(protocol: &Self::Verifier, ctx: &mut Dialect, claims: <Self::Verifier as TProtocol<Dialect>>::ClaimsBefore, advice: Self::ProverInput) -> (<Self::Verifier as TProtocol<Dialect>>::ClaimsAfter, Self::ProverOutput) {
//         let SingleLookupInput { values, accesses, table, indexes } = advice;
//         let c = ctx.challenge();
//         let gamma = ctx.challenge();
//         let mut running_gamma = gamma.clone();
//         let gammas = table.iter().map(|_| {
//             let res = running_gamma;
//             running_gamma = res + gamma.clone();
//             res
//         }).collect_vec();
//
//         let table_iter = table.into_iter().map(|t| {
//             t - c
//         });
//
//         let table_denoms = if indexes.is_some() {
//             table_iter.enumerate().map(|(i, t)| {
//                 t + gammas[i]
//             })
//                 .collect_vec()
//         } else {
//             table_iter.collect_vec()
//         };
//
//         let values_iter = values.into_iter().map(|v| {
//             v - c
//         });
//
//         let values_denoms = if let Some(indexes) = indexes {
//             values_iter.enumerate().map(|(i, v)| {
//                 v - gammas[indexes[i]]
//             }).collect_vec()
//         } else {
//             values_iter.collect_vec()
//         };
//
//
//
//         1
//     }
// }

#[cfg(test)]
mod tests {
    use crate::dialects::dialect::{TDialectInterface, TTranscriptSupports};
    use super::*;
    use ark_bn254::Fq as F;
    use ark_std::UniformRand;
    use num_traits::Zero;
    use crate::common::wrapper::Invert;
    use crate::dialects::dialect::tests::ManualTestDialect;

    #[test]
    fn test_logup_mainphase() {
        let rng = &mut ark_std::test_rng();
        let logsizes = vec![
            4,
            8,
            4,
        ];
        let data = logsizes.iter().map(|ls| {
            [
                (0..(1 << ls)).map(|_| F::rand(rng)).collect_vec(),
                (0..(1 << ls)).map(|_| F::rand(rng)).collect_vec(),
            ]
        }).collect_vec();

        let logup = LogupMainphase::new(logsizes.clone());

        let (_, [num, denom]) = logup.make_witness(data.clone());

        assert!(denom != F::zero());

        let sum_claim = SumClaim(num * denom.invert().unwrap());

        let mut ctx = ManualTestDialect::new((0..1000).map(|_| F::rand(rng)).collect_vec());

        let (pclaims, _) = logup.prove::<LogupMainphase<_>>(&mut ctx, sum_claim.clone(), data);
        ctx.end();
        let vclaims = logup.verify(&mut ctx, sum_claim);

        pclaims.iter().zip(logsizes).for_each(|(claim, logsize)| {
            println!("{}, {}", logsize, claim.point.len());
            assert_eq!(logsize, claim.point.len());
        });
        assert_eq!(pclaims, vclaims);
    }
}