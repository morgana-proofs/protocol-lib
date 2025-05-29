/*use std::marker::PhantomData;
use ark_std::iterable::Iterable;
use itertools::Itertools;
use crate::common::claims::{EvalClaim, SinglePointClaims, SumClaim};
use crate::common::math::{eq_poly, evaluate_index_poly, evaluate_multivar};
use crate::common::wrapper::{ComputationalField, TFelt};
use crate::components::lookups::logup::logup::{IndexedLookupClaim, IndexedLookupInput, LogupMainphase, LookupClaim, LookupInput, SubsetLookupClaim, SubsetLookupInput};
use crate::components::sumcheck::dense::DenseSumcheck;
use crate::protocol::component::{TProtocol, TProverImpl};
use crate::transcript::transcript::TArithmeticTranscript;

pub struct StarVerifier<F> {
    _pd: PhantomData<F>,
}

pub struct StarProver<F> {
    _pd: PhantomData<F>,
    num_vars: usize
}


impl<F: TFelt, Transcript: TArithmeticTranscript<F>> TProtocol<Transcript> for StarVerifier<F> {
    type ClaimsBefore = EvalClaim<F>;
    type ClaimsAfter = LogupStarOutputClaims<F>;

    fn verify(&self, ctx: &mut Transcript, claims: Self::ClaimsBefore) -> Self::ClaimsAfter {
        todo!()
    }
}

#[derive(Debug, Clone)]
pub struct LogupStarInput<F: TFelt> {
    pub table: Vec<F>,
    pub indexes: Vec<usize>,
}

pub struct LogupStarOutputClaims<F: TFelt> {
    pub table: EvalClaim<F>,
    pub indexes: EvalClaim<F>,
}

impl<F: ComputationalField, Transcript: TArithmeticTranscript<F>> TProverImpl<Transcript> for StarProver<F> {
    type Verifier = StarVerifier<F>;
    type ProverInput = LogupStarInput<F>;
    type ProverOutput = ();

    fn prove(&self, ctx: &mut Transcript, claims: <Self::Verifier as TProtocol<Transcript>>::ClaimsBefore, advice: Self::ProverInput) -> (<Self::Verifier as TProtocol<Transcript>>::ClaimsAfter, Self::ProverOutput) where <F as TSigUtil>::Constants: From<u64> {
        let LogupStarInput{ table, indexes } = advice;
        let findexes = indexes.iter().map(|x| F::from(*x as u64)).collect_vec();
        let EvalClaim{ ev, point: ref r } = claims;
        let eq_r = eq_poly(&r);
        let mut pushforward = vec![F::zero(); table.len()];
        for (i, v) in indexes.iter().enumerate() {
            pushforward[*v] += eq_r[i]
        }
        commit(pushforward.clone());

        let f = Mul2AlgFn::new();
        let sumcheck = DenseSumcheck::new(f, self.num_vars);
        let (sumcheck_claims, _) = sumcheck.prove(ctx, ev, vec![table, pushforward]);

        let mainphase = LogupMainphase::new(vec![]);

        let c = ctx.challenge();

        let data = vec![
                [
                    eq_r.clone(),
                    indexes.iter().map(|i| {
                        c - F::from(*i as u64)
                    }).collect_vec()
                ],
                [
                    pushforward.iter().map(|x| -*x).collect_vec(),
                    pushforward.iter().enumerate().map(|(i, _)| {
                        c - F::from(i as u64)
                    }).collect_vec()
                ]
        ];

        let (mainphase_claims, _) = mainphase.prove(ctx, SumClaim(F::zero()), data);

        let [lc, rc]: [SinglePointClaims<F>; 2] = mainphase_claims.try_into().unwrap();
        let ln_claim = lc.evs[0];
        let ld_claim = lc.evs[1];
        let l_point = lc.point;
        let rn_claim = rc.evs[0];
        let rd_claim = rc.evs[1];
        let r_point = rc.point;
        let indexes_claim = -ld_claim + c;

        open(pushforward.clone(), EvalClaim{ ev: sumcheck_claims.evs[1], point: sumcheck_claims.point.clone() });
        open(pushforward.clone(), EvalClaim{ ev: rn_claim, point: r_point.clone() });

        (
             LogupStarOutputClaims{
                table: EvalClaim{ ev: sumcheck_claims.evs[1], point: sumcheck_claims.point.clone() },
                indexes: EvalClaim{ ev: indexes_claim, point: r_point },
             },
             ()
        )
    }
}*/