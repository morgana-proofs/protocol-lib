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
    _pd: PhantomData<F>
}


impl<F: TPrimeField> LogupMainphase<F> {

    /// Assumes that first two logsizes have the same length - i.e. they corresponding polynomial is already split.
    pub fn new(logsizes: Vec<usize>) -> Self {
        assert!(logsizes.len() > 1);
        for i in 0 .. logsizes.len() - 1 {
            assert!(logsizes[i] >= logsizes[i+1], "logsizes must be non-increasing")
        }
        assert!(logsizes[0] == logsizes[1]);

        Self { logsizes, _pd: PhantomData }
    }

    pub fn make_witness(&self, input: Vec<[Vec<F>; 2]>) -> (Vec<[Vec<F>; 2]>, [F; 2]) {
        input.iter().zip_eq(self.logsizes.iter()).for_each(|(fraction_arr, logsize)| assert!(fraction_arr[0].len() == 1 << logsize && fraction_arr[1].len() == 1 << logsize));

        let mut input = input;
        input.reverse();

        let mut layers : Vec<[Vec<F>; 2]> = vec![];
        layers.push(input.pop().unwrap());
        layers.push(input.pop().unwrap());

        let mut i = 0;

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

        let [num, denom] = [ctx.read(), ctx.read()];
        // assert!(denom != F::zero());  todo: rebenkoy
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
                    if logsizes.len() == 2 {
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
            };

        accumulated_claims.push(tmp);
        accumulated_claims.reverse();
        accumulated_claims
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

                let protocol = DenseEqSumcheck::new(f, curr_logsize);

                let [advice_r_0, advice_r_1] = witness.pop().unwrap();
                let [advice_l_0, advice_l_1] = witness.pop().unwrap();
                let advice = vec![advice_l_0, advice_l_1, advice_r_0, advice_r_1];

                let (claim_4, _) = protocol.prove::<DenseEqSumcheck<_,_,>>(
                    ctx,
                    running_claim.clone(),
                    advice
                );

                if *incoming_logsize == curr_logsize {
                    if logsizes.len() == 2 {
                        break claim_4
                    }
                    running_claim = SinglePointClaims{ point: claim_4.point.clone(), evs: vec![claim_4.evs[0], claim_4.evs[1]] };
                    accumulated_claims.push(SinglePointClaims{ point: claim_4.point, evs: vec![claim_4.evs[2], claim_4.evs[3]] });
                    logsizes.pop();
                } else {
                    let split = SplitAt::new(SplitIdx::HI(0), 2);
                    (running_claim, _) = split.prove::<SplitAt<_,>>(ctx, claim_4, ());
                    curr_logsize += 1;
                }

            };

        accumulated_claims.push(tmp);
        accumulated_claims.reverse();
        (accumulated_claims, ())    }
}