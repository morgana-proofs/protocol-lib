use crate::common::algfn::{AlgFn, AlgFnSO, AlgFnSoUtils, RLC};
use crate::common::claims::{EvalClaim, SinglePointClaims, SumClaim};
use crate::common::math::{eq_poly, evaluate_multivar, top_bind_multivar_point};
use crate::common::wrapper::{ComputationalField, TFelt, TSigUtil};
use crate::components::lookups::logup::logup::{
    IndexedLookupClaim, IndexedLookupInput, Logup, LookupClaim, LookupInput, LookupType,
};
use crate::components::sumcheck::dense::DenseSumcheck;
use crate::components::sumcheck::dense_eq::eq_eval;
use crate::components::sumcheck::generic::SumcheckProtocol;
use crate::components::sumcheck::multi_dense_eq::{
    MultiDenseEqSumcheck, MultiPointEvalClaim, MultiPointEvalClaimPart,
};
use crate::components::sumcheck::sumcheckable::Sumcheckable;
use crate::components::vspark::matrix::{
    r_size, tau, tau::no_decomposition::at_point, tau::no_decomposition::table,
};
use crate::protocol::component::{TProtocol, TProverImpl};
use crate::transcript::transcript::{TArithmeticTranscript, TTranscriptInterface, TTranscriptSupportsIO};
use ark_ff::PrimeField;
use ark_std::iterable::Iterable;
use ark_std::log2;
use itertools::{repeat_n, Itertools};
use std::collections::HashMap;
use std::iter::once;
use std::marker::PhantomData;
use std::ops::Index;
use ark_ec::pairing::Pairing;
use tracing::{info_span, instrument};
use crate::components::commitments::scheme::{TCommitmentEngineProver, TCommitmentEngineVerifier};
use crate::components::vspark::matrix::tau::sqrt_decomposition::SqrtSplitTauTable;
use crate::components::vspark::vspark::VsparkProverInput;


#[derive(Debug, Clone)]
pub struct VsparkConfig<F: TFelt> {
    d: usize,  // matrix number logsize
    h: usize,  // description logsize
    nx: usize, // aka x-logsize
    midx: usize,
    px: usize,
    ny: usize, // aka y-logsize
    midy: usize,
    py: usize,
    _pd: PhantomData<F>,
}


#[derive(Debug, Clone)]
pub struct VsparkVerifier<
    F: TFelt,
    CommEngine: TCommitmentEngineVerifier<F>,
> {
    config: VsparkConfig<F>,
    commitment_scheme: CommEngine,
}

#[derive(Debug, Clone)]
pub struct VsparkProver<
    F: ComputationalField,
    CommEngine: TCommitmentEngineProver<F>
> {
    pub config: VsparkConfig<F>,
    pub commitment_scheme: CommEngine,
}

impl<
    F: ComputationalField,
    CommEngine: TCommitmentEngineProver<F>
> VsparkProver<F, CommEngine> {
    pub fn verifier(&self) -> VsparkVerifier<F, CommEngine::Verifier> {
        let Self{config, commitment_scheme, .. } = self;
        VsparkVerifier {
            config: config.clone(),
            commitment_scheme: commitment_scheme.clone().verifier(),
        }
    }
}

impl<F: TFelt> VsparkConfig<F> {
    pub fn new(
        nx: usize,
        midx: usize,
        px: usize,
        ny: usize,
        midy: usize,
        py: usize,
        h: usize,
        d: usize,
    ) -> Self {
        Self {
            d,
            h,
            nx,
            midx,
            px,
            ny,
            midy,
            py,
            _pd: Default::default(),
        }
    }

    fn compute_tau(n: usize, p: usize, mid: usize, x: &[F], r: &[F]) -> F {
        tau::sqrt_decomposition::at_point(n, p, mid, x, r)
    }
}

#[derive(Clone)]
pub struct VsparkFinalProd<F> {
    _pd: PhantomData<F>,
}

impl<F> VsparkFinalProd<F> {
    pub fn new() -> Self {
        Self {
            _pd: Default::default(),
        }
    }
}

impl<F: TFelt> AlgFnSO<F> for VsparkFinalProd<F> {
    fn exec(&self, args: &impl Index<usize, Output = F>) -> F {
        args[0] * args[1] * args[2] * (args[3] * args[4] + args[5] * args[6] + args[7] * args[8]) * (args[9] * args[10] + args[11] * args[12] + args[13] * args[14])
    }

    fn deg(&self) -> usize {
        7
    }

    fn n_ins(&self) -> usize {
        15
    }
}

impl<
    F: TFelt,
    Transcript: TArithmeticTranscript<F>
    + TTranscriptSupportsIO<CommEngine::Commitment>
    + TTranscriptSupportsIO<CommEngine::MultiCommitment>,
    CommEngine: TCommitmentEngineVerifier<F>,
> TProtocol<Transcript> for VsparkVerifier<F, CommEngine> {
    type ClaimsBefore = EvalClaim<F>;
    type ClaimsAfter = (
        SinglePointClaims<F>,
        SinglePointClaims<F>,
        [EvalClaim<F>; 2],
        [EvalClaim<F>; 2],
    );

    #[instrument(name = "VSpark::verify", level = "info", skip_all)]
    fn verify(&self, ctx: &mut Transcript, claims: Self::ClaimsBefore) -> Self::ClaimsAfter {
        let Self{ config: self_config, commitment_scheme, .. } = self;
        let EvalClaim {
            ev: e_ev_old,
            point: e_point_old,
        } = claims;
        let (t, rs) = e_point_old.split_at(self_config.d);
        let (r_x, rs) = rs.split_at(r_size(self_config.nx, self_config.px));
        let (r_y, rs) = rs.split_at(r_size(self_config.ny, self_config.py));
        assert_eq!(rs.len(), 0);

        let span = info_span!("final-prod-inputs").entered();
        let gamma = (0..self_config.d).map(|_| ctx.challenge()).collect_vec();

        let e_in_gamma_eval = ctx.read();

        let f = VsparkFinalProd::new();

        let sumcheck = DenseSumcheck::new(f, self_config.h + self_config.d);

        let e_claim_sumcheck: SinglePointClaims<F> = sumcheck
            .verify(ctx, SumClaim(e_in_gamma_eval));

        let [
        c_ev_sumcheck,
        i_pull_ev_sumcheck,
        eq_ev_sumcheck,
        x_tau_values_leq_l_sumcheck,
        x_tau_values_leq_r_sumcheck,
        x_tau_values_mid_l_sumcheck,
        x_tau_values_mid_r_sumcheck,
        x_tau_values_ge_l_sumcheck,
        x_tau_values_ge_r_sumcheck,
        y_tau_values_leq_l_sumcheck,
        y_tau_values_leq_r_sumcheck,
        y_tau_values_mid_l_sumcheck,
        y_tau_values_mid_r_sumcheck,
        y_tau_values_ge_l_sumcheck,
        y_tau_values_ge_r_sumcheck,
        ] =
            e_claim_sumcheck.evs.try_into().unwrap();
        (eq_ev_sumcheck - eq_eval(&gamma, &e_claim_sumcheck.point[self_config.h..])).require();
        span.exit();

        let span = info_span!("lookup-inputs").entered();
        let lookup = Logup::new(vec![
            LookupType::Indexed(self_config.midx, self_config.h + self_config.d),
            LookupType::Indexed(self_config.midx, self_config.h + self_config.d),
            LookupType::Indexed(self_config.midx, self_config.h + self_config.d),
            LookupType::Indexed(self_config.nx + 2 - self_config.midx, self_config.h + self_config.d),
            LookupType::Indexed(self_config.nx + 2 - self_config.midx, self_config.h + self_config.d),
            LookupType::Indexed(self_config.nx + 2 - self_config.midx, self_config.h + self_config.d),
            LookupType::Indexed(self_config.midy, self_config.h + self_config.d),
            LookupType::Indexed(self_config.midy, self_config.h + self_config.d),
            LookupType::Indexed(self_config.midy, self_config.h + self_config.d),
            LookupType::Indexed(self_config.ny + 2 - self_config.midy, self_config.h + self_config.d),
            LookupType::Indexed(self_config.ny + 2 - self_config.midy, self_config.h + self_config.d),
            LookupType::Indexed(self_config.ny + 2 - self_config.midy, self_config.h + self_config.d),
            LookupType::Indexed(self_config.d, self_config.h + self_config.d),
        ]);

        span.exit();

        let lookup_claims: [_; 13] = lookup
            .verify(ctx, ())
            .into_iter()
            .map(|c| {
                if let LookupClaim::Indexed(c) = c {
                    c
                } else {
                    panic!("Invalid LookupType::Indexed {:?}", c)
                }
            })
            .collect_array()
            .unwrap();

        let (x_tau_left_claims, lookup_claims) = lookup_claims.split_at(3);
        let (x_tau_right_claims, lookup_claims) = lookup_claims.split_at(3);
        let (y_tau_left_claims, lookup_claims) = lookup_claims.split_at(3);
        let (y_tau_right_claims, lookup_claims) = lookup_claims.split_at(3);
        let [i_lookup_claim] = lookup_claims else { unreachable!() };

        let (x_tau_left_accesses_claims, x_tau_left_table_claims, x_tau_left_values_claims, x_tau_left_index_claims): (Vec<&EvalClaim<F>>, Vec<&EvalClaim<F>>, Vec<&EvalClaim<F>>, Vec<&EvalClaim<F>>) =
            x_tau_left_claims.iter().map(|lookup_claim| {
                let IndexedLookupClaim {
                    accesses,
                    table,
                    values,
                    indexes,
                } = lookup_claim;
                (accesses, table, values, indexes)
            }).multiunzip();

        let (x_tau_right_accesses_claims, x_tau_right_table_claims, x_tau_right_values_claims, x_tau_right_index_claims): (Vec<&EvalClaim<F>>, Vec<&EvalClaim<F>>, Vec<&EvalClaim<F>>, Vec<&EvalClaim<F>>) =
            x_tau_right_claims.iter().map(|lookup_claim| {
                let IndexedLookupClaim {
                    accesses,
                    table,
                    values,
                    indexes,
                } = lookup_claim;
                (accesses, table, values, indexes)
            }).multiunzip();

        let (y_tau_left_accesses_claims, y_tau_left_table_claims, y_tau_left_values_claims, y_tau_left_index_claims): (Vec<&EvalClaim<F>>, Vec<&EvalClaim<F>>, Vec<&EvalClaim<F>>, Vec<&EvalClaim<F>>) =
            y_tau_left_claims.iter().map(|lookup_claim| {
                let IndexedLookupClaim {
                    accesses,
                    table,
                    values,
                    indexes,
                } = lookup_claim;
                (accesses, table, values, indexes)
            }).multiunzip();

        let (y_tau_right_accesses_claims, y_tau_right_table_claims, y_tau_right_values_claims, y_tau_right_index_claims): (Vec<&EvalClaim<F>>, Vec<&EvalClaim<F>>, Vec<&EvalClaim<F>>, Vec<&EvalClaim<F>>) =
            y_tau_right_claims.iter().map(|lookup_claim| {
                let IndexedLookupClaim {
                    accesses,
                    table,
                    values,
                    indexes,
                } = lookup_claim;
                (accesses, table, values, indexes)
            }).multiunzip();

        let IndexedLookupClaim {
            accesses: i_acc,
            table: e_adj_claim_lookup,
            values: i_pull,
            indexes: i_claim,
        } = i_lookup_claim;

        for (i, f) in [
            tau::sqrt_decomposition::parts::leq_l,
            tau::sqrt_decomposition::parts::mid_l,
            tau::sqrt_decomposition::parts::ge_l,
        ].iter().enumerate() {
            (x_tau_left_table_claims[i].ev - f(self_config.nx, self_config.px, self_config.midx, &x_tau_left_table_claims[i].point, r_x))
                .require();
        }
        for (i, f) in [
            tau::sqrt_decomposition::parts::leq_r,
            tau::sqrt_decomposition::parts::mid_r,
            tau::sqrt_decomposition::parts::ge_r,
        ].iter().enumerate() {
            (x_tau_right_table_claims[i].ev - f(self_config.nx, self_config.px, self_config.midx, &x_tau_right_table_claims[i].point, r_x))
                .require();
        }
        for (i, f) in [
            tau::sqrt_decomposition::parts::leq_l,
            tau::sqrt_decomposition::parts::mid_l,
            tau::sqrt_decomposition::parts::ge_l,
        ].iter().enumerate() {
            (y_tau_left_table_claims[i].ev - f(self_config.ny, self_config.py, self_config.midy, &y_tau_left_table_claims[i].point, r_y))
                .require();
        }
        for (i, f) in [
            tau::sqrt_decomposition::parts::leq_r,
            tau::sqrt_decomposition::parts::mid_r,
            tau::sqrt_decomposition::parts::ge_r,
        ].iter().enumerate() {
            (y_tau_right_table_claims[i].ev - f(self_config.ny, self_config.py, self_config.midy, &y_tau_right_table_claims[i].point, r_y))
                .require();
        }


        let reducer = MultiDenseEqSumcheck::new(self_config.h + self_config.d);

        let mut claims_mess_1 = reducer
            .verify(
                ctx,
                MultiPointEvalClaim::new(
                    vec![
                        e_claim_sumcheck.point,
                        i_claim.point.clone(),
                        x_tau_left_index_claims[0].point.clone(),
                        x_tau_left_index_claims[1].point.clone(),
                        x_tau_left_index_claims[2].point.clone(),
                        x_tau_right_index_claims[0].point.clone(),
                        x_tau_right_index_claims[1].point.clone(),
                        x_tau_right_index_claims[2].point.clone(),
                        y_tau_left_index_claims[0].point.clone(),
                        y_tau_left_index_claims[1].point.clone(),
                        y_tau_left_index_claims[2].point.clone(),
                        y_tau_right_index_claims[0].point.clone(),
                        y_tau_right_index_claims[1].point.clone(),
                        y_tau_right_index_claims[2].point.clone(),
                    ],
                    vec![
                        /* 0  */MultiPointEvalClaimPart::new(1, 0, c_ev_sumcheck),
                        /* 1  */MultiPointEvalClaimPart::new(0, 0, i_pull_ev_sumcheck),
                        /* 2  */MultiPointEvalClaimPart::new(0, 1, i_pull.ev),
                        /* 3  */MultiPointEvalClaimPart::new(2, 1, i_claim.ev),

                        /* 4  */MultiPointEvalClaimPart::new(7, 0, x_tau_values_leq_l_sumcheck),
                        /* 5  */MultiPointEvalClaimPart::new(9, 0, x_tau_values_mid_l_sumcheck),
                        /* 6  */MultiPointEvalClaimPart::new(11, 0, x_tau_values_ge_l_sumcheck),

                        /* 7  */MultiPointEvalClaimPart::new(8, 0, x_tau_values_leq_r_sumcheck),
                        /* 8  */MultiPointEvalClaimPart::new(10, 0, x_tau_values_mid_r_sumcheck),
                        /* 9  */MultiPointEvalClaimPart::new(12, 0, x_tau_values_ge_r_sumcheck),

                        /* 10 */MultiPointEvalClaimPart::new(13, 0, y_tau_values_leq_l_sumcheck),
                        /* 11 */MultiPointEvalClaimPart::new(15, 0, y_tau_values_mid_l_sumcheck),
                        /* 12 */MultiPointEvalClaimPart::new(17, 0, y_tau_values_ge_l_sumcheck),

                        /* 13 */MultiPointEvalClaimPart::new(14, 0, y_tau_values_leq_r_sumcheck),
                        /* 14 */MultiPointEvalClaimPart::new(16, 0, y_tau_values_mid_r_sumcheck),
                        /* 15 */MultiPointEvalClaimPart::new(18, 0, y_tau_values_ge_r_sumcheck),

                        /* 16 */MultiPointEvalClaimPart::new(3, 2, x_tau_left_index_claims[0].ev),
                        /* 17 */MultiPointEvalClaimPart::new(3, 3, x_tau_left_index_claims[1].ev),
                        /* 18 */MultiPointEvalClaimPart::new(3, 4, x_tau_left_index_claims[2].ev),
                        /* 19 */MultiPointEvalClaimPart::new(7, 2, x_tau_left_values_claims[0].ev),
                        /* 20 */MultiPointEvalClaimPart::new(9, 3, x_tau_left_values_claims[1].ev),
                        /* 21 */MultiPointEvalClaimPart::new(11, 4, x_tau_left_values_claims[2].ev),

                        /* 22 */MultiPointEvalClaimPart::new(4, 5, x_tau_right_index_claims[0].ev),
                        /* 23 */MultiPointEvalClaimPart::new(4, 6, x_tau_right_index_claims[1].ev),
                        /* 24 */MultiPointEvalClaimPart::new(4, 7, x_tau_right_index_claims[2].ev),
                        /* 25 */MultiPointEvalClaimPart::new(8, 5, x_tau_right_values_claims[0].ev),
                        /* 26 */MultiPointEvalClaimPart::new(10, 6, x_tau_right_values_claims[1].ev),
                        /* 27 */MultiPointEvalClaimPart::new(12, 7, x_tau_right_values_claims[2].ev),

                        /* 28 */MultiPointEvalClaimPart::new(5, 8, y_tau_left_index_claims[0].ev),
                        /* 29 */MultiPointEvalClaimPart::new(5, 9, y_tau_left_index_claims[1].ev),
                        /* 30 */MultiPointEvalClaimPart::new(5, 10, y_tau_left_index_claims[2].ev),
                        /* 31 */MultiPointEvalClaimPart::new(13, 8, y_tau_left_values_claims[0].ev),
                        /* 32 */MultiPointEvalClaimPart::new(15, 9, y_tau_left_values_claims[1].ev),
                        /* 33 */MultiPointEvalClaimPart::new(17, 10, y_tau_left_values_claims[2].ev),

                        /* 34 */MultiPointEvalClaimPart::new(6, 11, y_tau_right_index_claims[0].ev),
                        /* 35 */MultiPointEvalClaimPart::new(6, 12, y_tau_right_index_claims[1].ev),
                        /* 36 */MultiPointEvalClaimPart::new(6, 13, y_tau_right_index_claims[2].ev),
                        /* 37 */MultiPointEvalClaimPart::new(14, 11, y_tau_right_values_claims[0].ev),
                        /* 38 */MultiPointEvalClaimPart::new(16, 12, y_tau_right_values_claims[1].ev),
                        /* 39 */MultiPointEvalClaimPart::new(18, 13, y_tau_right_values_claims[2].ev),
                    ],
                )
            );

        (claims_mess_1.evs[1] - claims_mess_1.evs[2]).require();

        (claims_mess_1.evs[4] - claims_mess_1.evs[19]).require();
        (claims_mess_1.evs[5] - claims_mess_1.evs[20]).require();
        (claims_mess_1.evs[6] - claims_mess_1.evs[21]).require();
        (claims_mess_1.evs[7] - claims_mess_1.evs[25]).require();
        (claims_mess_1.evs[8] - claims_mess_1.evs[26]).require();
        (claims_mess_1.evs[9] - claims_mess_1.evs[27]).require();
        (claims_mess_1.evs[10] - claims_mess_1.evs[31]).require();
        (claims_mess_1.evs[11] - claims_mess_1.evs[32]).require();
        (claims_mess_1.evs[12] - claims_mess_1.evs[33]).require();
        (claims_mess_1.evs[13] - claims_mess_1.evs[37]).require();
        (claims_mess_1.evs[14] - claims_mess_1.evs[38]).require();
        (claims_mess_1.evs[15] - claims_mess_1.evs[39]).require();

        (claims_mess_1.evs[16] - claims_mess_1.evs[17]).require();
        (claims_mess_1.evs[16] - claims_mess_1.evs[18]).require();
        (claims_mess_1.evs[22] - claims_mess_1.evs[23]).require();
        (claims_mess_1.evs[22] - claims_mess_1.evs[24]).require();
        (claims_mess_1.evs[28] - claims_mess_1.evs[29]).require();
        (claims_mess_1.evs[28] - claims_mess_1.evs[30]).require();
        (claims_mess_1.evs[34] - claims_mess_1.evs[35]).require();
        (claims_mess_1.evs[34] - claims_mess_1.evs[36]).require();


        let reducer2 = MultiDenseEqSumcheck::new(self_config.d);

        let mut claims_mess_2 = reducer2
            .verify(
                ctx,
                MultiPointEvalClaim::new(
                    vec![
                        e_adj_claim_lookup.point.clone(),
                        t.to_vec(),
                        gamma,
                        i_acc.point.clone(),
                    ],
                    vec![
                        MultiPointEvalClaimPart::new(0, 1, e_ev_old),
                        MultiPointEvalClaimPart::new(0, 2, e_in_gamma_eval),
                        MultiPointEvalClaimPart::new(
                            0,
                            0,
                            e_adj_claim_lookup.ev
                                - eq_eval(&vec![F::zero(); self_config.d], &e_adj_claim_lookup.point),
                        ),
                        MultiPointEvalClaimPart::new(1, 3, i_acc.ev),
                    ],
                ),
            );

        (claims_mess_2.evs[0] - claims_mess_2.evs[1]).require();
        (claims_mess_2.evs[0] - claims_mess_2.evs[2]).require();

        let reducer_x_accesses_left = MultiDenseEqSumcheck::new(self_config.midx);
        let x_accesses_unified_claim_left = reducer_x_accesses_left.verify(
            ctx,
            MultiPointEvalClaim::new(
                x_tau_left_accesses_claims.iter().map(|c| c.point.clone()).collect_vec(),
                x_tau_left_accesses_claims.iter().enumerate().map(|(i, c)| MultiPointEvalClaimPart::new(0, i, c.ev)).collect_vec(),
            ),

        );
        (x_accesses_unified_claim_left.evs[0] - x_accesses_unified_claim_left.evs[1]).require();
        (x_accesses_unified_claim_left.evs[0] - x_accesses_unified_claim_left.evs[2]).require();

        let reducer_x_accesses_right = MultiDenseEqSumcheck::new(self_config.nx + 2 - self_config.midx);
        let x_accesses_unified_claim_right = reducer_x_accesses_right.verify(
            ctx,
            MultiPointEvalClaim::new(
                x_tau_right_accesses_claims.iter().map(|c| c.point.clone()).collect_vec(),
                x_tau_right_accesses_claims.iter().enumerate().map(|(i, c)| MultiPointEvalClaimPart::new(0, i, c.ev)).collect_vec(),
            ),

        );
        (x_accesses_unified_claim_right.evs[0] - x_accesses_unified_claim_right.evs[1]).require();
        (x_accesses_unified_claim_right.evs[0] - x_accesses_unified_claim_right.evs[2]).require();

        let x_accesses_claims = [
            EvalClaim{
                ev: x_accesses_unified_claim_left.evs[0],
                point: x_accesses_unified_claim_left.point,
            },
            EvalClaim{
                ev: x_accesses_unified_claim_right.evs[0],
                point: x_accesses_unified_claim_right.point,
            },
        ];

        let reducer_y_accesses_left = MultiDenseEqSumcheck::new(self_config.midy);
        let y_accesses_unified_claim_left = reducer_y_accesses_left.verify(
            ctx,
            MultiPointEvalClaim::new(
                y_tau_left_accesses_claims.iter().map(|c| c.point.clone()).collect_vec(),
                y_tau_left_accesses_claims.iter().enumerate().map(|(i, c)| MultiPointEvalClaimPart::new(0, i, c.ev)).collect_vec(),
            ),

        );
        (y_accesses_unified_claim_left.evs[0] - y_accesses_unified_claim_left.evs[1]).require();
        (y_accesses_unified_claim_left.evs[0] - y_accesses_unified_claim_left.evs[2]).require();

        let reducer_y_accesses_right = MultiDenseEqSumcheck::new(self_config.ny + 2 - self_config.midy);
        let y_accesses_unified_claim_right = reducer_y_accesses_right.verify(
            ctx,
            MultiPointEvalClaim::new(
                y_tau_right_accesses_claims.iter().map(|c| c.point.clone()).collect_vec(),
                y_tau_right_accesses_claims.iter().enumerate().map(|(i, c)| MultiPointEvalClaimPart::new(0, i, c.ev)).collect_vec(),
            ),

        );
        (y_accesses_unified_claim_right.evs[0] - y_accesses_unified_claim_right.evs[1]).require();
        (y_accesses_unified_claim_right.evs[0] - y_accesses_unified_claim_right.evs[2]).require();

        let y_accesses_claims = [
            EvalClaim{
                ev: y_accesses_unified_claim_left.evs[0],
                point: y_accesses_unified_claim_left.point,
            },
            EvalClaim{
                ev: y_accesses_unified_claim_right.evs[0],
                point: y_accesses_unified_claim_right.point,
            },
        ];

        // All these claims should be returned.
        // This is a mess. there are actually like 12 of them.
        // Why would we invent a self_config like this?
        (claims_mess_1, claims_mess_2, x_accesses_claims, y_accesses_claims)
    }
}

impl<
    F: ComputationalField,
    Transcript: TArithmeticTranscript<F>
    + TTranscriptSupportsIO<<CommEngine::Verifier as TCommitmentEngineVerifier<F>>::Commitment>
    + TTranscriptSupportsIO<<CommEngine::Verifier as TCommitmentEngineVerifier<F>>::MultiCommitment>,
    CommEngine: TCommitmentEngineProver<F, CommitmentAdvice=Vec<F>, OpeneingAdvice=Vec<F>, MultiCommitmentAdvice=Vec<Vec<F>>, MultiOpeneingAdvice=Vec<Vec<F>>>,
> TProverImpl<Transcript> for VsparkProver<F, CommEngine> where
    <F as TSigUtil>::Constants: From<u64>,
    CommEngine::Verifier: TCommitmentEngineVerifier<F, MultiConfig=usize, MultiClaim=Vec<EvalClaim<F>>, Claim=EvalClaim<F>>,
{
    type Verifier = VsparkVerifier<F, CommEngine::Verifier>;
    type ProverInput = VsparkProverInput<F>;
    type ProverOutput = ();

    #[instrument(name = "VSpark::prove", level = "info", skip_all)]
    fn prove(
        &self,
        ctx: &mut Transcript,
        claims: <Self::Verifier as TProtocol<Transcript>>::ClaimsBefore,
        advice: Self::ProverInput,
    ) -> (
        <Self::Verifier as TProtocol<Transcript>>::ClaimsAfter,
        Self::ProverOutput,
    ) {
        let Self{ config: self_config, commitment_scheme, .. } = self;
        let VsparkProverInput {
            e_poly,
            c_poly,
            i_poly,
            x_poly,
            y_poly,
            _pd,
        } = advice;
        let EvalClaim {
            ev: e_ev_old,
            point: e_point_old,
        } = claims;
        let (t, rs) = e_point_old.split_at(self_config.d);
        let (r_x, rs) = rs.split_at(r_size(self_config.nx, self_config.px));
        let (r_y, rs) = rs.split_at(r_size(self_config.ny, self_config.py));
        assert_eq!(rs.len(), 0);

        let delta_poly = eq_poly(&vec![F::zero(); self_config.d]);
        let e_adj = e_poly
            .iter()
            .zip(delta_poly.iter())
            .map(|(e, d)| *e + d)
            .collect_vec();

        let mut accesses_i = e_poly.iter().map(|_| F::zero()).collect::<Vec<_>>();
        let values_i = i_poly
            .iter()
            .map(|idx| {
                accesses_i[*idx] += F::one();
                e_adj[*idx]
            })
            .collect::<Vec<_>>();

        let e_poly_commitment = commitment_scheme.commit(
            ctx,
            e_poly.clone(),
        );

        let SqrtSplitTauTable {
            parts: [[x_tau_table_leq_l, x_tau_table_leq_r], [x_tau_table_mid_l, x_tau_table_mid_r], [x_tau_table_ge_l, x_tau_table_ge_r]],
            ..
        } =
            tau::sqrt_decomposition::tables(self_config.nx, self_config.px, self_config.midx, r_x);
        let mut x_tau_accesses_l = x_tau_table_leq_l
            .iter()
            .map(|_| F::zero())
            .collect::<Vec<_>>();
        let mut x_tau_accesses_r = x_tau_table_leq_r
            .iter()
            .map(|_| F::zero())
            .collect::<Vec<_>>();
        let mut x_tau_indexes_l = vec![];
        let mut x_tau_indexes_r = vec![];
        let mut x_tau_values_leq_l = vec![];
        let mut x_tau_values_leq_r = vec![];
        let mut x_tau_values_mid_l = vec![];
        let mut x_tau_values_mid_r = vec![];
        let mut x_tau_values_ge_l = vec![];
        let mut x_tau_values_ge_r = vec![];
        x_poly
            .iter()
            .for_each(|&idx| {
                let l_idx = idx % (1 << self_config.midx);
                let r_idx = idx >> self_config.midx;
                x_tau_indexes_l.push(F::from(l_idx as u64));
                x_tau_indexes_r.push(F::from(r_idx as u64));
                x_tau_accesses_l[l_idx] += F::one();
                x_tau_accesses_r[r_idx] += F::one();
                x_tau_values_leq_l.push(x_tau_table_leq_l[l_idx]);
                x_tau_values_leq_r.push(x_tau_table_leq_r[r_idx]);
                x_tau_values_mid_l.push(x_tau_table_mid_l[l_idx]);
                x_tau_values_mid_r.push(x_tau_table_mid_r[r_idx]);
                x_tau_values_ge_l.push(x_tau_table_ge_l[l_idx]);
                x_tau_values_ge_r.push(x_tau_table_ge_r[r_idx]);
            });

        let SqrtSplitTauTable {
            parts: [[y_tau_table_leq_l, y_tau_table_leq_r], [y_tau_table_mid_l, y_tau_table_mid_r], [y_tau_table_ge_l, y_tau_table_ge_r]],
            ..
        } =
            tau::sqrt_decomposition::tables(self_config.ny, self_config.py, self_config.midy, r_y);
        let mut y_tau_accesses_l = y_tau_table_leq_l
            .iter()
            .map(|_| F::zero())
            .collect::<Vec<_>>();
        let mut y_tau_accesses_r = y_tau_table_leq_r
            .iter()
            .map(|_| F::zero())
            .collect::<Vec<_>>();
        let mut y_tau_indexes_l = vec![];
        let mut y_tau_indexes_r = vec![];
        let mut y_tau_values_leq_l = vec![];
        let mut y_tau_values_leq_r = vec![];
        let mut y_tau_values_mid_l = vec![];
        let mut y_tau_values_mid_r = vec![];
        let mut y_tau_values_ge_l = vec![];
        let mut y_tau_values_ge_r = vec![];
        y_poly
            .iter()
            .for_each(|&idx| {
                let l_idx = idx % (1 << self_config.midy);
                let r_idx = idx >> self_config.midy;
                y_tau_indexes_l.push(F::from(l_idx as u64));
                y_tau_indexes_r.push(F::from(r_idx as u64));
                y_tau_accesses_l[l_idx] += F::one();
                y_tau_accesses_r[r_idx] += F::one();
                y_tau_values_leq_l.push(y_tau_table_leq_l[l_idx]);
                y_tau_values_leq_r.push(y_tau_table_leq_r[r_idx]);
                y_tau_values_mid_l.push(y_tau_table_mid_l[l_idx]);
                y_tau_values_mid_r.push(y_tau_table_mid_r[r_idx]);
                y_tau_values_ge_l.push(y_tau_table_ge_l[l_idx]);
                y_tau_values_ge_r.push(y_tau_table_ge_r[r_idx]);
            });

        assert_eq!(e_poly.len(), 1 << log2(e_poly.len()));
        assert_eq!(accesses_i.len(), 1 << log2(accesses_i.len()));
        assert_eq!(values_i.len(), 1 << log2(values_i.len()));

        let gamma = (0..self_config.d).map(|_| ctx.challenge()).collect_vec();

        let e_in_gamma_eval = evaluate_multivar(&e_poly, &gamma);
        ctx.write(&e_in_gamma_eval);

        let f = VsparkFinalProd::new();

        let e_data = vec![
            c_poly.clone(),
            values_i.clone(),
            eq_poly(&gamma)
                .into_iter()
                .map(|x| repeat_n(x, (1 << self_config.h)))
                .flatten()
                .collect_vec(),
            x_tau_values_leq_l.clone(),
            x_tau_values_leq_r.clone(),
            x_tau_values_mid_l.clone(),
            x_tau_values_mid_r.clone(),
            x_tau_values_ge_l.clone(),
            x_tau_values_ge_r.clone(),
            y_tau_values_leq_l.clone(),
            y_tau_values_leq_r.clone(),
            y_tau_values_mid_l.clone(),
            y_tau_values_mid_r.clone(),
            y_tau_values_ge_l.clone(),
            y_tau_values_ge_r.clone(),
        ];
        let e_output = f.map_so(&e_data.iter().map(|v| v.as_ref()).collect_vec());
        let e_sum = e_output
            .iter()
            .chunks(1 << self_config.h)
            .into_iter()
            .map(|c| c.fold(F::zero(), |a, b| a + b))
            .collect_vec();
        assert_eq!(
            e_sum,
            e_poly
                .iter()
                .zip(eq_poly(&gamma).iter())
                .map(|(a, b)| *a * b)
                .collect_vec()
        );

        let sumcheck = DenseSumcheck::new(f, self_config.h + self_config.d);

        let e_claim_sumcheck: SinglePointClaims<F> = sumcheck
            .prove(ctx, SumClaim(e_in_gamma_eval), e_data)
            .0;

        let [
        c_ev_sumcheck,
        i_pull_ev_sumcheck,
        eq_ev_sumcheck,
        x_tau_values_leq_l_sumcheck,
        x_tau_values_leq_r_sumcheck,
        x_tau_values_mid_l_sumcheck,
        x_tau_values_mid_r_sumcheck,
        x_tau_values_ge_l_sumcheck,
        x_tau_values_ge_r_sumcheck,
        y_tau_values_leq_l_sumcheck,
        y_tau_values_leq_r_sumcheck,
        y_tau_values_mid_l_sumcheck,
        y_tau_values_mid_r_sumcheck,
        y_tau_values_ge_l_sumcheck,
        y_tau_values_ge_r_sumcheck,
        ] =
            e_claim_sumcheck.evs.try_into().unwrap();
        (eq_ev_sumcheck - eq_eval(&gamma, &e_claim_sumcheck.point[self_config.h..])).require();

        let rlc = ctx.challenge();
        let rlc2 = rlc * rlc;
        let x_tau_values_left_rlc_claim = x_tau_values_leq_l_sumcheck + rlc * x_tau_values_mid_l_sumcheck + rlc2 * x_tau_values_ge_l_sumcheck;
        let x_tau_values_right_rlc_claim = x_tau_values_leq_r_sumcheck + rlc * x_tau_values_mid_r_sumcheck + rlc2 * x_tau_values_ge_r_sumcheck;
        let y_tau_values_left_rlc_claim = y_tau_values_leq_l_sumcheck + rlc * y_tau_values_mid_l_sumcheck + rlc2 * y_tau_values_ge_l_sumcheck;
        let y_tau_values_right_rlc_claim = y_tau_values_leq_r_sumcheck + rlc * y_tau_values_mid_r_sumcheck + rlc2 * y_tau_values_ge_r_sumcheck;
        let rlcf = RLC::new(rlc, 3);

        let i_poly_f = i_poly.iter().map(|x| F::from(*x as u64)).collect_vec();
        // let x_poly_f = x_poly.iter().map(|x| F::from(*x as u64)).collect_vec();
        // let y_poly_f = y_poly.iter().map(|x| F::from(*x as u64)).collect_vec();
        let lookup = Logup::new(vec![
            LookupType::Indexed(self_config.midx, self_config.h + self_config.d),
            LookupType::Indexed(self_config.nx + 2 - self_config.midx, self_config.h + self_config.d),
            LookupType::Indexed(self_config.midy, self_config.h + self_config.d),
            LookupType::Indexed(self_config.ny + 2 - self_config.midy, self_config.h + self_config.d),
            LookupType::Indexed(self_config.d, self_config.h + self_config.d),
        ]);

        let mut lookup_advice = vec![];

        let x_tau_table_l_rlc = rlcf.map_so(&[&x_tau_table_leq_l, &x_tau_table_mid_l, &x_tau_table_ge_l]);
        let x_tau_values_l_rlc = rlcf.map_so(&[&x_tau_values_leq_l, &x_tau_values_mid_l, &x_tau_values_ge_l]);
        lookup_advice.push(LookupInput::indexed(
            x_tau_table_l_rlc.clone(),
            x_tau_accesses_l.clone(),
            x_tau_values_l_rlc.clone(),
            x_tau_indexes_l.clone(),
        ));

        let x_tau_table_r_rlc = rlcf.map_so(&[&x_tau_table_leq_r, &x_tau_table_mid_r, &x_tau_table_ge_r]);
        let x_tau_values_r_rlc = rlcf.map_so(&[&x_tau_values_leq_r, &x_tau_values_mid_r, &x_tau_values_ge_r]);
        lookup_advice.push(LookupInput::indexed(
            x_tau_table_r_rlc.clone(),
            x_tau_accesses_r.clone(),
            x_tau_values_r_rlc.clone(),
            x_tau_indexes_r.clone(),
        ));

        let y_tau_table_l_rlc = rlcf.map_so(&[&y_tau_table_leq_l, &y_tau_table_mid_l, &y_tau_table_ge_l]);
        let y_tau_values_l_rlc = rlcf.map_so(&[&y_tau_values_leq_l, &y_tau_values_mid_l, &y_tau_values_ge_l]);
        lookup_advice.push(LookupInput::indexed(
            y_tau_table_l_rlc.clone(),
            y_tau_accesses_l.clone(),
            y_tau_values_l_rlc.clone(),
            y_tau_indexes_l.clone(),
        ));

        let y_tau_table_r_rlc = rlcf.map_so(&[&y_tau_table_leq_r, &y_tau_table_mid_r, &y_tau_table_ge_r]);
        let y_tau_values_r_rlc = rlcf.map_so(&[&y_tau_values_leq_r, &y_tau_values_mid_r, &y_tau_values_ge_r]);
        lookup_advice.push(LookupInput::indexed(
            y_tau_table_r_rlc.clone(),
            y_tau_accesses_r.clone(),
            y_tau_values_r_rlc.clone(),
            y_tau_indexes_r.clone(),
        ));

        let tau_commitments = commitment_scheme.multi_commit(ctx, vec![
            values_i.clone(),
            x_tau_values_l_rlc.clone(),
            x_tau_values_r_rlc.clone(),
            y_tau_values_l_rlc.clone(),
            y_tau_values_r_rlc.clone(),
        ], 5);

        lookup_advice.push(LookupInput::indexed_by_usize(e_adj, accesses_i.clone(), values_i.clone(), i_poly));

        let lookup_claims: [_; 5] = lookup
            .prove(ctx, (), lookup_advice)
            .0
            .into_iter()
            .map(|c| {
                if let LookupClaim::Indexed(c) = c {
                    c
                } else {
                    panic!("Invalid LookupType::Indexed {:?}", c)
                }
            })
            .collect_array()
            .unwrap();

        let [x_tau_left_claims, x_tau_right_claims, y_tau_left_claims, y_tau_right_claims, i_lookup_claim] = lookup_claims else { unreachable!() };

        let IndexedLookupClaim {
            accesses: x_tau_left_accesses_claims,
            table: x_tau_left_table_claims,
            values: x_tau_left_values_claims,
            indexes: x_tau_left_index_claims
        } = x_tau_left_claims;
        let IndexedLookupClaim {
            accesses: x_tau_right_accesses_claims,
            table: x_tau_right_table_claims,
            values: x_tau_right_values_claims,
            indexes: x_tau_right_index_claims
        } = x_tau_right_claims;
        let IndexedLookupClaim {
            accesses: y_tau_left_accesses_claims,
            table: y_tau_left_table_claims,
            values: y_tau_left_values_claims,
            indexes: y_tau_left_index_claims
        } = y_tau_left_claims;
        let IndexedLookupClaim {
            accesses: y_tau_right_accesses_claims,
            table: y_tau_right_table_claims,
            values: y_tau_right_values_claims,
            indexes: y_tau_right_index_claims
        } = y_tau_right_claims;

        let IndexedLookupClaim {
            accesses: i_acc,
            table: e_adj_claim_lookup,
            values: i_pull,
            indexes: i_claim,
        } = i_lookup_claim;

        (x_tau_left_table_claims.ev
            - tau::sqrt_decomposition::parts::leq_l(self_config.nx, self_config.px, self_config.midx, &x_tau_left_table_claims.point, r_x)
            - rlc * tau::sqrt_decomposition::parts::mid_l(self_config.nx, self_config.px, self_config.midx, &x_tau_left_table_claims.point, r_x)
            - rlc2 * tau::sqrt_decomposition::parts::ge_l(self_config.nx, self_config.px, self_config.midx, &x_tau_left_table_claims.point, r_x)
        ).require();

        (x_tau_right_table_claims.ev
            - tau::sqrt_decomposition::parts::leq_r(self_config.nx, self_config.px, self_config.midx, &x_tau_right_table_claims.point, r_x)
            - rlc * tau::sqrt_decomposition::parts::mid_r(self_config.nx, self_config.px, self_config.midx, &x_tau_right_table_claims.point, r_x)
            - rlc2 * tau::sqrt_decomposition::parts::ge_r(self_config.nx, self_config.px, self_config.midx, &x_tau_right_table_claims.point, r_x)
        ).require();


        (y_tau_left_table_claims.ev
            - tau::sqrt_decomposition::parts::leq_l(self_config.ny, self_config.py, self_config.midy, &y_tau_left_table_claims.point, r_y)
            - rlc * tau::sqrt_decomposition::parts::mid_l(self_config.ny, self_config.py, self_config.midy, &y_tau_left_table_claims.point, r_y)
            - rlc2 * tau::sqrt_decomposition::parts::ge_l(self_config.ny, self_config.py, self_config.midy, &y_tau_left_table_claims.point, r_y)
        ).require();

        (y_tau_right_table_claims.ev
            - tau::sqrt_decomposition::parts::leq_r(self_config.ny, self_config.py, self_config.midy, &y_tau_right_table_claims.point, r_y)
            - rlc * tau::sqrt_decomposition::parts::mid_r(self_config.ny, self_config.py, self_config.midy, &y_tau_right_table_claims.point, r_y)
            - rlc2 * tau::sqrt_decomposition::parts::ge_r(self_config.ny, self_config.py, self_config.midy, &y_tau_right_table_claims.point, r_y)
        ).require();

        let reducer = MultiDenseEqSumcheck::new(self_config.h + self_config.d);

        let mut claims_mess_1 = reducer
            .prove(
                ctx,
                MultiPointEvalClaim::new(
                    vec![
                        e_claim_sumcheck.point,
                        i_claim.point.clone(),
                        x_tau_left_index_claims.point.clone(),
                        x_tau_right_index_claims.point.clone(),
                        y_tau_left_index_claims.point.clone(),
                        y_tau_right_index_claims.point.clone(),
                    ],
                    vec![
                        /* 0  */MultiPointEvalClaimPart::new(1, 0, c_ev_sumcheck),
                        /* 1  */MultiPointEvalClaimPart::new(0, 0, i_pull_ev_sumcheck),
                        /* 2  */MultiPointEvalClaimPart::new(0, 1, i_pull.ev),
                        /* 3  */MultiPointEvalClaimPart::new(2, 1, i_claim.ev),

                        /* 4  */MultiPointEvalClaimPart::new(7, 0, x_tau_values_left_rlc_claim),
                        /* 5  */MultiPointEvalClaimPart::new(3, 2, x_tau_left_index_claims.ev),
                        /* 6  */MultiPointEvalClaimPart::new(7, 2, x_tau_left_values_claims.ev),

                        /* 7  */MultiPointEvalClaimPart::new(8, 0, x_tau_values_right_rlc_claim),
                        /* 8  */MultiPointEvalClaimPart::new(4, 3, x_tau_right_index_claims.ev),
                        /* 9  */MultiPointEvalClaimPart::new(8, 3, x_tau_right_values_claims.ev),

                        /* 10 */MultiPointEvalClaimPart::new(9, 0, y_tau_values_left_rlc_claim),
                        /* 11 */MultiPointEvalClaimPart::new(5, 4, y_tau_left_index_claims.ev),
                        /* 12 */MultiPointEvalClaimPart::new(9, 4, y_tau_left_values_claims.ev),

                        /* 13 */MultiPointEvalClaimPart::new(10, 0, y_tau_values_right_rlc_claim),
                        /* 14 */MultiPointEvalClaimPart::new(6, 5, y_tau_right_index_claims.ev),
                        /* 15 */MultiPointEvalClaimPart::new(10, 5, y_tau_right_values_claims.ev),
                    ],
                ),
                vec![
                    /* 0  */values_i.clone(),
                    /* 1  */c_poly,
                    /* 2  */i_poly_f,
                    /* 3  */x_tau_indexes_l,
                    /* 4  */x_tau_indexes_r,
                    /* 5  */y_tau_indexes_l,
                    /* 6  */y_tau_indexes_r,
                    /* 7  */x_tau_values_l_rlc.clone(),
                    /* 8  */x_tau_values_r_rlc.clone(),
                    /* 9  */y_tau_values_l_rlc.clone(),
                    /* 10 */y_tau_values_r_rlc.clone(),
                ],
            )
            .0;
        (claims_mess_1.evs[1] - claims_mess_1.evs[2]).require();
        (claims_mess_1.evs[4] - claims_mess_1.evs[6]).require();
        (claims_mess_1.evs[7] - claims_mess_1.evs[9]).require();
        (claims_mess_1.evs[10] - claims_mess_1.evs[12]).require();
        (claims_mess_1.evs[13] - claims_mess_1.evs[15]).require();

        commitment_scheme.multi_open(
            ctx,
            tau_commitments,
            vec![
                EvalClaim{ ev: claims_mess_1.evs[1], point: claims_mess_1.point.clone() },
                EvalClaim{ ev: claims_mess_1.evs[4], point: claims_mess_1.point.clone() },
                EvalClaim{ ev: claims_mess_1.evs[7], point: claims_mess_1.point.clone() },
                EvalClaim{ ev: claims_mess_1.evs[10], point: claims_mess_1.point.clone() },
                EvalClaim{ ev: claims_mess_1.evs[13], point: claims_mess_1.point.clone() },
            ],
            vec![
                values_i,
                x_tau_values_l_rlc,
                x_tau_values_r_rlc,
                y_tau_values_l_rlc,
                y_tau_values_r_rlc,
            ],
            5
        );

        let reducer2 = MultiDenseEqSumcheck::new(self_config.d);

        let mut claims_mess_2 = reducer2
            .prove(
                ctx,
                MultiPointEvalClaim::new(
                    vec![
                        e_adj_claim_lookup.point.clone(),
                        t.to_vec(),
                        gamma,
                        i_acc.point.clone(),
                    ],
                    vec![
                        MultiPointEvalClaimPart::new(0, 1, e_ev_old),
                        MultiPointEvalClaimPart::new(0, 2, e_in_gamma_eval),
                        MultiPointEvalClaimPart::new(
                            0,
                            0,
                            e_adj_claim_lookup.ev
                                - eq_eval(&vec![F::zero(); self_config.d], &e_adj_claim_lookup.point),
                        ),
                        MultiPointEvalClaimPart::new(1, 3, i_acc.ev),
                    ],
                ),
                vec![e_poly.clone(), accesses_i],
            )
            .0;

        (claims_mess_2.evs[0] - claims_mess_2.evs[1]).require();
        (claims_mess_2.evs[0] - claims_mess_2.evs[2]).require();

        commitment_scheme.open(
            ctx,
            e_poly_commitment,
            EvalClaim{ ev: claims_mess_2.evs[0], point: claims_mess_2.point.clone() },
            e_poly,
        );

        let x_accesses_claims = [
            x_tau_left_accesses_claims,
            x_tau_right_accesses_claims,
        ];

        let y_accesses_claims = [
            y_tau_left_accesses_claims,
            y_tau_right_accesses_claims,
        ];



        let claims_mess_1 = SinglePointClaims {
            evs: vec![
                claims_mess_1.evs[1],
                claims_mess_1.evs[0],
                claims_mess_1.evs[3],
                claims_mess_1.evs[5],
                claims_mess_1.evs[8],
                claims_mess_1.evs[11],
                claims_mess_1.evs[12],
            ],
            point: claims_mess_1.point,
        };

        // All these claims should be returned.
        // This is a mess. there are actually like 12 of them.
        // Why would we invent a self_config like this?
        ((claims_mess_1, claims_mess_2, x_accesses_claims, y_accesses_claims), ())
    }
}

pub mod bench_parts {
    use ark_ec::pairing::Pairing;
    use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
    use ark_std::rand::RngCore;
    use ark_std::UniformRand;
    use itertools::Itertools;
    use serde::{Deserialize, Serialize};
    use tracing::info_span;
    use crate::common::claims::EvalClaim;
    use crate::common::math::evaluate_multivar;
    use crate::common::wrapper::{ComputationalField, TFelt, TSigUtil};
    use crate::components::commitments::knuckles::KnucklesSetup;
    use crate::components::commitments::kzg::KZGSetup;
    use crate::components::commitments::scheme::{TCommitmentEngineProver, TCommitmentEngineVerifier};
    use crate::components::vspark::matrix::{r_size, tau, VsparkMatrixGroup};
    use crate::components::vspark::sqrt_vspark::{VsparkConfig, VsparkProver};
    use crate::components::vspark::vspark::VsparkProverInput;
    use crate::protocol::component::{TProtocol, TProverImpl};
    use crate::transcript::transcript::ProofTranscript;

    #[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
    pub struct VsparkTestcaseData<F: ComputationalField + Sync + Send> {
        pub prover_input: VsparkProverInput<F>,
        pub eval_claim: EvalClaim<F>,
    }

    #[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
    pub struct VsparkExtTestcaseData<F: ComputationalField + Sync + Send, P: Pairing<ScalarField=F>> {
        pub prover_input: VsparkProverInput<F>,
        pub eval_claim: EvalClaim<F>,
        pub knuckles_setup: KnucklesSetup<P>
    }

    pub fn build_sqrt_vspark_data<F: ComputationalField + UniformRand, RNG: RngCore, P: Pairing<ScalarField=F>>(rng: &mut RNG, vspark: &VsparkConfig<F>) -> VsparkExtTestcaseData<F, P> {
        let VsparkConfig { nx, midx, px, ny, midy, py, h, d, _pd: _} = *vspark;
        let grp = VsparkMatrixGroup::<F>::rand(rng, nx, px, ny, py, h, d);

        let rd = (0..d).map(|_| F::rand(rng)).collect_vec();
        let rx = (0..r_size(nx, px)).map(|_| F::rand(rng)).collect_vec();
        let ry = (0..r_size(ny, py)).map(|_| F::rand(rng)).collect_vec();
        let mut r = rd.clone();
        r.extend_from_slice(&rx);
        r.extend_from_slice(&ry);

        let tau_table_x = tau::sqrt_decomposition::tables(nx, px, midx, &rx);
        let tau_table_y = tau::sqrt_decomposition::tables(ny, py, midy, &ry);
        let e_poly = grp.e_poly(&tau_table_x, &tau_table_y, d);

        let e_claim_before = EvalClaim {
            ev: evaluate_multivar(&e_poly, &rd),
            point: r,
        };

        VsparkExtTestcaseData {
            prover_input: VsparkProverInput {
                e_poly: e_poly.clone(),
                c_poly: grp.c_poly(h, d),
                i_poly: grp.i_poly(h, d),
                x_poly: grp.x_poly(h, d),
                y_poly: grp.y_poly(h, d),
                _pd: Default::default(),
            },
            eval_claim: e_claim_before,
            knuckles_setup: KnucklesSetup {
                tau: P::ScalarField::rand(rng),
                g0: P::G1Affine::rand(rng),
                h0: P::G2Affine::rand(rng),
                num_vars: *[nx + 2 - midx, ny + 2 - midy, midx, midy, h + d].iter().max().unwrap(),
                k: P::ScalarField::rand(rng),
            },
        }
    }
    pub fn run_sqrt_vspark<
        F: ComputationalField,
        CommEngine: TCommitmentEngineProver<F, CommitmentAdvice=Vec<F>, OpeneingAdvice=Vec<F>, MultiCommitmentAdvice=Vec<Vec<F>>, MultiOpeneingAdvice=Vec<Vec<F>>>
    >(vspark: &VsparkProver<F, CommEngine>, input: VsparkTestcaseData<F>)
    where
        <F as TSigUtil>::Constants: From<u64>,
        CommEngine::Verifier: TCommitmentEngineVerifier<F, MultiConfig=usize, MultiClaim=Vec<EvalClaim<F>>, Claim=EvalClaim<F>>
    {
        let span = info_span!("sqrt").entered();
        let mut transcript_p = ProofTranscript::start_prover("asd".as_bytes());
        let (output_claims, _) = vspark.prove(&mut transcript_p, input.eval_claim.clone(), input.prover_input);
        let proof = transcript_p.end();
        let vspark = vspark.verifier();
        let mut transcript_v = ProofTranscript::start_verifier("asd".as_bytes(), proof);
        let expected_output_claims = vspark.verify(&mut transcript_v, input.eval_claim);
        assert_eq!(output_claims, expected_output_claims);
    }
}

#[cfg(test)]
mod tests {
    use super::{VsparkConfig, VsparkProver, VsparkProverInput};
    use crate::common::claims::EvalClaim;
    use crate::common::math::evaluate_multivar;
    use crate::components::vspark::matrix::{
        r_size, tau::no_decomposition::table, VsparkMatrixGroup,
    };
    use crate::protocol::component::{TProtocol, TProverImpl};
    use ark_bn254::Fr as F;
    use ark_ec::pairing::Pairing;
    use ark_std::UniformRand;
    use itertools::Itertools;
    use tracing::info_span;

    use tracing::level_filters::LevelFilter;
    use tracing_subscriber::fmt::format::FmtSpan;
    use tracing_subscriber::layer::{Layered, SubscriberExt};
    use tracing_subscriber::util::{SubscriberInitExt, TryInitError};
    use tracing_subscriber::{fmt, prelude::*, reload, EnvFilter, Layer, Registry};
    use crate::components::commitments::knuckles::KnucklesProvingKey;
    use crate::components::commitments::kzg::{random_kzg_pk, KzgProvingKey};
    use crate::components::vspark::sqrt_vspark::bench_parts::build_sqrt_vspark_data;
    use crate::test_utils::data::load_or_generate_data;
    use crate::transcript::transcript::ProofTranscript;

    #[test]
    fn test_sqrt_vspark() {
        let rng = &mut ark_std::test_rng();
        let span = info_span!("test_sqrt_vspark").entered();
        for _ in 0..10 {
            let span = info_span!("generation").entered();
            let (nx, midx, px, ny, midy, py, h, d) = (5, 3, 3, 5, 2, 4, 3, 3);
            let grp = VsparkMatrixGroup::<F>::rand(rng, nx, px, ny, py, h, d);
            let num_vars = 10;
            let N = 1 << num_vars;
            let vspark = VsparkProver{
                config: VsparkConfig::<F>::new(nx, midx, px, ny, midy, py, h, d),
                commitment_scheme: KnucklesProvingKey::<ark_bn254::Bn254>::new(random_kzg_pk(2 * N - 1, rng), num_vars, <ark_bn254::Bn254 as Pairing>::ScalarField::rand(rng)),
            };

            let rd = (0..d).map(|_| F::rand(rng)).collect_vec();
            let rx = (0..r_size(nx, px)).map(|_| F::rand(rng)).collect_vec();
            let ry = (0..r_size(ny, py)).map(|_| F::rand(rng)).collect_vec();
            let mut r = rd.clone();
            r.extend_from_slice(&rx);
            r.extend_from_slice(&ry);

            let tau_table_x = table(nx, px, &rx);
            let tau_table_y = table(ny, py, &ry);
            let e_poly = grp.e_poly(&tau_table_x, &tau_table_y, d);

            let e_claim_before = EvalClaim {
                ev: evaluate_multivar(&e_poly, &rd),
                point: r,
            };

            let prover_input = VsparkProverInput {
                e_poly: e_poly.clone(),
                c_poly: grp.c_poly(h, d),
                i_poly: grp.i_poly(h, d),
                x_poly: grp.x_poly(h, d),
                y_poly: grp.y_poly(h, d),
                _pd: Default::default(),
            };
            span.exit();
            let span = info_span!("payload").entered();
            let mut transcript_p = ProofTranscript::start_prover(b"test");
            let (output_claims, _) = vspark.prove(&mut transcript_p, e_claim_before.clone(), prover_input);
            let proof = transcript_p.end();;
            let vspark = vspark.verifier();
            let mut transcript_v = ProofTranscript::start_verifier(b"test", proof);
            let expected_output_claims = vspark.verify(&mut transcript_v, e_claim_before.clone());
            assert_eq!(output_claims, expected_output_claims);
        }
    }


    #[cfg(feature = "testbench")]
    #[test]
    fn bench_vspark() {
        // Create a tracing layer with the configured tracer
        crate::test_utils::tracing::setup();

        let rng = &mut ark_std::test_rng();
        let span = info_span!("test").entered();
        let span = info_span!("generation").entered();
        let (nx, midx, px, ny, midy, py, h, d) = (
            20,
            11,
            4,
            20,
            11,
            4,
            3,
            10,
        );
        let vspark_config = VsparkConfig::<F>::new(nx, midx, px, ny, midy, py, h, d);
        let test_data = load_or_generate_data("sqrt-vspark", build_sqrt_vspark_data, rng, &vspark_config);

        span.exit();
        {
            let span = info_span!("payload").entered();
            {
                let span = info_span!("sqrt").entered();
                let mut transcript_p = ProofTranscript::start_prover(b"test");
                let vspark = VsparkProver{
                    config: vspark_config,
                    commitment_scheme: KnucklesProvingKey::<ark_bn254::Bn254>::build(test_data.knuckles_setup),
                    _pd: Default::default(),
                };
                let (output_claims, _) = vspark.prove(&mut transcript_p, test_data.eval_claim.clone(), test_data.prover_input);
                let proof = transcript_p.end();
                let vspark = vspark.verifier();
                let mut transcript_v = ProofTranscript::start_verifier(b"test", proof);
                let expected_output_claims = vspark.verify(&mut transcript_v, test_data.eval_claim);
                transcript_v.end();
                assert_eq!(output_claims, expected_output_claims);
            }
        }
    }
}
