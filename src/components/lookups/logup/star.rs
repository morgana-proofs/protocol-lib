use std::marker::PhantomData;
use ark_std::iterable::Iterable;
use itertools::Itertools;
use crate::common::algfns::Mul2AlgFn;
use crate::common::claims::{EvalClaim, SinglePointClaims, SumClaim};
use crate::common::math::{eq_poly, evaluate_index_poly, evaluate_multivar};
use crate::common::wrapper::{ComputationalField, TFelt, TSigUtil};
use crate::components::commitments::scheme::{TCommitmentEngineProver, TCommitmentEngineVerifier};
use crate::components::lookups::logup::logup::{IndexedLookupClaim, IndexedLookupInput, LogupMainphase, LookupClaim, LookupInput, SubsetLookupClaim, SubsetLookupInput};
use crate::components::sumcheck::dense::DenseSumcheck;
use crate::protocol::component::{TProtocol, TProverImpl};
use crate::transcript::transcript::{TArithmeticTranscript, TTranscriptSupportsIO};

pub struct StarConfig<F> {
    num_vars: usize,
    _pd: PhantomData<F>,
}

pub struct StarVerifier<
    F: TFelt,
    CommEngine: TCommitmentEngineVerifier<F>,
> {
    _pd: StarConfig<F>,
    commitment_scheme: CommEngine,

}

pub struct StarProver<
    F: ComputationalField,
    CommEngine: TCommitmentEngineProver<F>,
> {
    config: StarConfig<F>,
    commitment_scheme: CommEngine,
}


impl<
    F: TFelt,
    Transcript: TArithmeticTranscript<F>,
    CommEngine: TCommitmentEngineVerifier<F, MultiConfig=(usize, Vec<usize>), MultiClaim=Vec<EvalClaim<F>>, Claim=EvalClaim<F>>,
> TProtocol<Transcript> for StarVerifier<F, CommEngine> {
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

impl<
    F: ComputationalField,
    Transcript: TArithmeticTranscript<F>
    + TTranscriptSupportsIO<<CommEngine::Verifier as TCommitmentEngineVerifier<F>>::Commitment>
    + TTranscriptSupportsIO<<CommEngine::Verifier as TCommitmentEngineVerifier<F>>::MultiCommitment>,
    CommEngine: TCommitmentEngineProver<F, CommitmentAdvice=Vec<F>, OpeneingAdvice=Vec<F>, MultiCommitmentAdvice=Vec<Vec<F>>, MultiOpeneingAdvice=Vec<Vec<F>>>,
> TProverImpl<Transcript> for StarProver<F, CommEngine> where
    CommEngine::Verifier: TCommitmentEngineVerifier<F, MultiConfig=(usize, Vec<usize>), MultiClaim=Vec<EvalClaim<F>>, Claim=EvalClaim<F>>,
    <CommEngine::Verifier as TCommitmentEngineVerifier<F>>::Commitment: Clone,
    <F as TSigUtil>::Constants: From<u64>
{
    type Verifier = StarVerifier<F, CommEngine::Verifier>;
    type ProverInput = LogupStarInput<F>;
    type ProverOutput = ();

    fn prove(&self, ctx: &mut Transcript, claims: <Self::Verifier as TProtocol<Transcript>>::ClaimsBefore, advice: Self::ProverInput) -> (<Self::Verifier as TProtocol<Transcript>>::ClaimsAfter, Self::ProverOutput) {
        let Self { config, commitment_scheme } = self;
        let LogupStarInput{ table, indexes } = advice;
        let EvalClaim{ ev, point: ref r } = claims;
        let eq_r = eq_poly(&r);
        let mut pushforward = vec![F::zero(); table.len()];
        for (i, v) in indexes.iter().enumerate() {
            pushforward[*v] += eq_r[i]
        }
        let pushforward_commitment = commitment_scheme.commit(ctx, pushforward.clone());

        let f = Mul2AlgFn::new();
        let sumcheck = DenseSumcheck::new(f, config.num_vars);
        let (sumcheck_claims, _) = sumcheck.prove(ctx, EvalClaim{ev, point: r.clone()}, vec![table, pushforward.clone()]);

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
        let ln_ev = lc.evs[0];
        let ld_ev = lc.evs[1];
        let l_point = lc.point;
        let rn_ev = rc.evs[0];
        let rd_ev = rc.evs[1];
        let r_point = rc.point;
        let indexes_claim = -ld_ev + c;

        (ln_ev - evaluate_multivar(&eq_r, &l_point)).require();
        (rd_ev - c + evaluate_index_poly(&r_point)).require();

        commitment_scheme.open(ctx, pushforward_commitment.clone(),EvalClaim{ ev: sumcheck_claims.evs[1], point: sumcheck_claims.point.clone() }, pushforward.clone());
        commitment_scheme.open(ctx, pushforward_commitment, EvalClaim{ ev: rn_ev, point: r_point.clone() }, pushforward.clone());

        (
             LogupStarOutputClaims{
                table: EvalClaim{ ev: sumcheck_claims.evs[1], point: sumcheck_claims.point.clone() },
                indexes: EvalClaim{ ev: indexes_claim, point: r_point },
             },
             ()
        )
    }
}