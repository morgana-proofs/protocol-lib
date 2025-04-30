use std::collections::HashMap;
use std::iter::once;
use std::marker::PhantomData;
use std::ops::Index;
use ark_ff::PrimeField;
use ark_std::iterable::Iterable;
use ark_std::log2;
use itertools::{repeat_n, Itertools};
use crate::common::algfn::{AlgFn, AlgFnSO, AlgFnSoUtils};
use crate::common::claims::{EvalClaim, SinglePointClaims, SumClaim};
use crate::common::math::{eq_poly, evaluate_multivar, top_bind_multivar_point};
use crate::common::wrapper::{ComputationalField, TFelt};
use crate::components::lookups::logup::logup::{IndexedLookupClaim, IndexedLookupInput, Logup, LookupClaim, LookupInput, LookupType};
use crate::components::sumcheck::dense::DenseSumcheck;
use crate::components::sumcheck::dense_eq::eq_eval;
use crate::components::sumcheck::generic::SumcheckProtocol;
use crate::components::sumcheck::multi_dense_eq::{MultiDenseEqSumcheck, MultiPointEvalClaim, MultiPointEvalClaimPart};
use crate::components::sumcheck::sumcheckable::Sumcheckable;
use crate::components::vspark::matrix::{tau::no_decomposition::at_point, tau::no_decomposition::table, r_size, tau};
use crate::transcript::transcript::{TArithmeticTranscript, TTranscriptInterface};
use crate::protocol::component::{TProtocol, TProverImpl};
use tracing::{info_span, instrument};


pub struct Vspark<F: TFelt> {
    d: usize,  // matrix number logsize
    h: usize,  // description logsize
    nx: usize,  // aka x-logsize
    px: usize,
    ny: usize,  // aka y-logsize
    py: usize,
    _pd: PhantomData<F>,
}

impl<F: TFelt> Vspark<F> {
    fn new(nx: usize, px: usize, ny: usize, py: usize, h: usize, d: usize) -> Self {
        Self {
            d,
            h,
            nx,
            px,
            ny,
            py,
            _pd: Default::default(),
        }
    }

    fn compute_tau(n: usize, p: usize, x: &[F], r: &[F]) -> F {
        tau::no_decomposition::at_point(n, p, x, r)
    }
}

pub struct VsparkProverInput<F: TFelt> {
    e_poly: Vec<F>,
    c_poly: Vec<F>,
    i_poly: Vec<usize>,
    x_poly: Vec<usize>,
    y_poly: Vec<usize>,
    _pd: PhantomData<F>
}

pub struct VsparkProverOutput<F: TFelt> {
    _pd: PhantomData<F>
}

#[derive(Clone)]
pub struct VsparkFinalProd<F> {
    _pd: PhantomData<F>
}

impl<F> VsparkFinalProd<F> {
    pub fn new() -> Self {
        Self {
            _pd: Default::default(),
        }
    }
}

impl<F: TFelt> AlgFnSO<F> for VsparkFinalProd<F> {
    fn exec(&self, args: &impl Index<usize, Output=F>) -> F {
        args[0] * args[1] * args[2] * args[3] * args[4]
    }

    fn deg(&self) -> usize {
        5
    }

    fn n_ins(&self) -> usize {
        5
    }
}

impl<F: TFelt, Transcript: TArithmeticTranscript<F>> TProtocol<Transcript> for Vspark<F> {
    type ClaimsBefore = EvalClaim<F>;
    type ClaimsAfter = (SinglePointClaims<F>, SinglePointClaims<F>, EvalClaim<F>, EvalClaim<F>);

    #[instrument(name="VSpark::verify", level="info", skip_all)]
    fn verify(&self, ctx: &mut Transcript, claims: Self::ClaimsBefore) -> Self::ClaimsAfter {
        let EvalClaim { ev: e_ev_old, point: e_point_old } = claims;
        let (t, rs) = e_point_old.split_at(self.d);
        let (r_x, rs) = rs.split_at(r_size(self.nx, self.px));
        let (r_y, rs) = rs.split_at(r_size(self.ny, self.py));
        assert_eq!(rs.len(), 0);

        let lookup = Logup::new(vec![
            LookupType::Indexed(self.nx + 2, self.h + self.d),
            LookupType::Indexed(self.ny + 2, self.h + self.d),
            LookupType::Indexed(self.d, self.h + self.d),
        ]);

        let lookup_claims: [_; 3] = lookup.verify(ctx, ()).into_iter().map(|c| {
            if let LookupClaim::Indexed(c) = c {
                c
            } else {
                panic!("Invalid LookupType::Subset {:?}", c)
            }
        }).collect_array().unwrap();

        let [a, b, c] = lookup_claims; // RUST, WHY!?!?!?!
        let IndexedLookupClaim{ accesses: x_acc, table: tau_x_claim, values: x_pull, indexes: x_claim } = a;
        let IndexedLookupClaim{ accesses: y_acc, table: tau_y_claim, values: y_pull, indexes: y_claim } = b;
        let IndexedLookupClaim{ accesses: i_acc, table: e_adj_claim_lookup, values: i_pull, indexes: i_claim } = c;

        (tau_x_claim.ev - Self::compute_tau(self.nx, self.px, &tau_x_claim.point, r_x)).require();
        (tau_y_claim.ev - Self::compute_tau(self.ny, self.py, &tau_y_claim.point, r_y)).require();

        let gamma = (0..self.d).map(|_| ctx.challenge()).collect_vec();

        let e_in_gamma_eval = ctx.read();

        let delta0_in_gamma = eq_eval(&vec![F::zero(); self.d], &gamma);
        let f = VsparkFinalProd::new();

        let sumcheck = DenseSumcheck::new(f, self.h + self.d);

        let e_claim_sumcheck: SinglePointClaims<F> = sumcheck.verify(ctx, SumClaim(e_in_gamma_eval));
        let [c_ev_sumcheck, i_pull_ev_sumcheck, x_pull_ev_sumcheck, y_pull_ev_sumcheck, eq_ev_sumcheck] = e_claim_sumcheck.evs.try_into().unwrap();
        (eq_ev_sumcheck - eq_eval(&gamma, &e_claim_sumcheck.point[self.h..])).require();


        let reducer = MultiDenseEqSumcheck::new(self.h + self.d);
        let mut claims_mess_1 = reducer.verify(ctx, MultiPointEvalClaim::new(
            vec![
                e_claim_sumcheck.point,
                x_claim.point,
                y_claim.point,
                i_claim.point,
            ],
            vec![
                MultiPointEvalClaimPart::new(0, 1, x_claim.ev),
                MultiPointEvalClaimPart::new(1, 1, x_pull.ev),
                MultiPointEvalClaimPart::new(1, 0, x_pull_ev_sumcheck),
                MultiPointEvalClaimPart::new(3, 2, y_claim.ev),
                MultiPointEvalClaimPart::new(4, 2, y_pull.ev),
                MultiPointEvalClaimPart::new(4, 0, y_pull_ev_sumcheck),
                MultiPointEvalClaimPart::new(5, 3, i_claim.ev),
                MultiPointEvalClaimPart::new(6, 3, i_pull.ev),
                MultiPointEvalClaimPart::new(6, 0, i_pull_ev_sumcheck),
                MultiPointEvalClaimPart::new(7, 0, c_ev_sumcheck),
            ],
        ));

        (claims_mess_1.evs[1] - claims_mess_1.evs[2]).require();
        (claims_mess_1.evs[4] - claims_mess_1.evs[5]).require();
        (claims_mess_1.evs[7] - claims_mess_1.evs[8]).require();

        let reducer2 = MultiDenseEqSumcheck::new(self.d);

        let mut claims_mess_2 = reducer2.verify(ctx, MultiPointEvalClaim::new(
            vec![
                e_adj_claim_lookup.point.clone(),
                t.to_vec(),
                gamma,
                i_acc.point,
            ],
            vec![
                MultiPointEvalClaimPart::new(0, 1, e_ev_old),
                MultiPointEvalClaimPart::new(0, 2, e_in_gamma_eval),
                MultiPointEvalClaimPart::new(0, 0, e_adj_claim_lookup.ev - eq_eval(&vec![F::zero(); self.d], &e_adj_claim_lookup.point)),
                MultiPointEvalClaimPart::new(1, 3, i_acc.ev),
            ],
        ));

        (claims_mess_2.evs[0] - claims_mess_2.evs[1]).require();
        // (claims_mess_2.evs[1] - claims_mess_2.evs[3]).require();

        // All these claims should be returned.
        // This is a mess. there are actually like 12 of them.
        // Why would we invent a protocol like this?
        (
            claims_mess_1,
            claims_mess_2,
            x_acc,
            y_acc,
        )
    }
}


impl<F: ComputationalField, Transcript: TArithmeticTranscript<F>> TProverImpl<Transcript> for Vspark<F> {
    type Verifier = Self;
    type ProverInput = VsparkProverInput<F>;
    type ProverOutput = ();

    #[instrument(name="VSpark::prove", level="info", skip_all)]
    fn _prove(protocol: &Self::Verifier, ctx: &mut Transcript, claims: <Self::Verifier as TProtocol<Transcript>>::ClaimsBefore, advice: Self::ProverInput) -> (<Self::Verifier as TProtocol<Transcript>>::ClaimsAfter, Self::ProverOutput) {
        let VsparkProverInput{ e_poly, c_poly, i_poly, x_poly, y_poly, _pd } = advice;
        let EvalClaim { ev: e_ev_old, point: e_point_old } = claims;
        let (t, rs) = e_point_old.split_at(protocol.d);
        let (r_x, rs) = rs.split_at(r_size(protocol.nx, protocol.px));
        let (r_y, rs) = rs.split_at(r_size(protocol.ny, protocol.py));
        assert_eq!(rs.len(), 0);


        let span = info_span!("lookup-inputs").entered();
        let lookup = Logup::new(vec![
            LookupType::Indexed(protocol.nx + 2, protocol.h + protocol.d),
            LookupType::Indexed(protocol.ny + 2, protocol.h + protocol.d),
            LookupType::Indexed(protocol.d, protocol.h + protocol.d),
        ]);

        let tau_table_x = tau::no_decomposition::table(protocol.nx, protocol.px, r_x);
        assert_eq!(tau_table_x.len(), 1 << protocol.nx + 2);
        let mut tau_accesses_x = tau_table_x.iter().map(|_| F::zero()).collect::<Vec<_>>();
        let tau_values_x = x_poly.iter().map(|idx| {
            tau_accesses_x[*idx] += F::one();
            tau_table_x[*idx]
        }).collect::<Vec<_>>();

        let tau_table_y = tau::no_decomposition::table(protocol.ny, protocol.py, r_y);
        assert_eq!(tau_table_y.len(), 1 << protocol.ny + 2);
        let mut tau_accesses_y = tau_table_y.iter().map(|_| F::zero()).collect::<Vec<_>>();
        let tau_values_y = y_poly.iter().map(|idx| {
            tau_accesses_y[*idx] += F::one();
            tau_table_y[*idx]
        }).collect::<Vec<_>>();

        let delta_poly = eq_poly(&vec![F::zero(); protocol.d]);
        let e_adj = e_poly.iter().zip(delta_poly.iter()).map(|(e, d)| *e + d).collect_vec();

        let mut accesses_i = e_poly.iter().map(|_| F::zero()).collect::<Vec<_>>();
        let values_i = i_poly.iter().map(|idx| {
            accesses_i[*idx] += F::one();
            e_adj[*idx]
        }).collect::<Vec<_>>();

        assert_eq!(e_poly.len(), 1 << log2(e_poly.len()));
        assert_eq!(accesses_i.len(), 1 << log2(accesses_i.len()));
        assert_eq!(values_i.len(), 1 << log2(values_i.len()));

        let i_poly_f = i_poly.iter().map(|x| F::from(*x as u64)).collect_vec();
        let x_poly_f = x_poly.iter().map(|x| F::from(*x as u64)).collect_vec();
        let y_poly_f = y_poly.iter().map(|x| F::from(*x as u64)).collect_vec();

        let lookup_advice = vec![
            LookupInput::indexed_by_usize(
                tau_table_x.clone(),
                tau_accesses_x,
                tau_values_x.clone(),
                x_poly,
            ),
            LookupInput::indexed_by_usize(
                tau_table_y.clone(),
                tau_accesses_y,
                tau_values_y.clone(),
                y_poly,
            ),
            LookupInput::indexed_by_usize(
                e_adj,
                accesses_i.clone(),
                values_i.clone(),
                i_poly,
            ),
        ];

        span.exit();
        let lookup_claims: [_; 3] = lookup.prove::<Logup<_>>(ctx, (), lookup_advice).0.into_iter().map(|c| {
            if let LookupClaim::Indexed(c) = c {
                c
            } else {
                panic!("Invalid LookupType::Indexed {:?}", c)
            }
        }).collect_array().unwrap();

        let [a, b, c] = lookup_claims; // RUST, WHY!?!?!?!
        let IndexedLookupClaim{ accesses: x_acc, table: tau_x_claim, values: x_pull, indexes: x_claim } = a;
        let IndexedLookupClaim{ accesses: y_acc, table: tau_y_claim, values: y_pull, indexes: y_claim } = b;
        let IndexedLookupClaim{ accesses: i_acc, table: e_adj_claim_lookup, values: i_pull, indexes: i_claim } = c;

        (tau_x_claim.ev - Self::compute_tau(protocol.nx, protocol.px, &tau_x_claim.point, r_x)).require();
        (tau_y_claim.ev - Self::compute_tau(protocol.ny, protocol.py, &tau_y_claim.point, r_y)).require();

        let span = info_span!("final-prod-inputs").entered();
        let gamma = (0..protocol.d).map(|_| ctx.challenge()).collect_vec();

        let e_in_gamma_eval = evaluate_multivar(&e_poly, &gamma);
        ctx.write(&e_in_gamma_eval);

        let f = VsparkFinalProd::new();

        let e_data = vec![
            c_poly.clone(),
            values_i.clone(),
            tau_values_x.clone(),
            tau_values_y.clone(),
            eq_poly(&gamma).into_iter().map(|x| repeat_n(x, (1 << protocol.h))).flatten().collect_vec(),
        ];
        let e_output = f.map_so(&e_data.iter().map(|v| v.as_ref()).collect_vec());
        let e_sum = e_output.iter().chunks(1 << protocol.h).into_iter().map(|c| c.fold(F::zero(), |a, b| a + b)).collect_vec();
        assert_eq!(e_sum, e_poly.iter().zip(eq_poly(&gamma).iter()).map(|(a, b)| *a * b).collect_vec());

        let sumcheck = DenseSumcheck::new(f, protocol.h + protocol.d);
        span.exit();

        let e_claim_sumcheck: SinglePointClaims<F> = sumcheck.prove::<DenseSumcheck<_,_>>(ctx, SumClaim(e_in_gamma_eval), e_data).0;

        let [c_ev_sumcheck, i_pull_ev_sumcheck, x_pull_ev_sumcheck, y_pull_ev_sumcheck, eq_ev_sumcheck] = e_claim_sumcheck.evs.try_into().unwrap();
        (eq_ev_sumcheck - eq_eval(&gamma, &e_claim_sumcheck.point[protocol.h..])).require();

        let reducer = MultiDenseEqSumcheck::new(protocol.h + protocol.d);

        let mut claims_mess_1 = reducer.prove::<MultiDenseEqSumcheck<_>>(
            ctx,
            MultiPointEvalClaim::new(
                vec![
                    e_claim_sumcheck.point,
                    x_claim.point,
                    y_claim.point,
                    i_claim.point,
                ],
                vec![
                    MultiPointEvalClaimPart::new(0, 1, x_claim.ev),
                    MultiPointEvalClaimPart::new(1, 1, x_pull.ev),
                    MultiPointEvalClaimPart::new(1, 0, x_pull_ev_sumcheck),
                    MultiPointEvalClaimPart::new(2, 2, y_claim.ev),
                    MultiPointEvalClaimPart::new(3, 2, y_pull.ev),
                    MultiPointEvalClaimPart::new(3, 0, y_pull_ev_sumcheck),
                    MultiPointEvalClaimPart::new(4, 3, i_claim.ev),
                    MultiPointEvalClaimPart::new(5, 3, i_pull.ev),
                    MultiPointEvalClaimPart::new(5, 0, i_pull_ev_sumcheck),
                    MultiPointEvalClaimPart::new(6, 0, c_ev_sumcheck),
                ],
            ),
            vec![
                x_poly_f,
                tau_values_x,
                y_poly_f,
                tau_values_y,
                i_poly_f,
                values_i,
                c_poly,
            ]
        ).0;

        (claims_mess_1.evs[1] - claims_mess_1.evs[2]).require();
        (claims_mess_1.evs[4] - claims_mess_1.evs[5]).require();
        (claims_mess_1.evs[7] - claims_mess_1.evs[8]).require();

        let reducer2 = MultiDenseEqSumcheck::new(protocol.d);

        let mut claims_mess_2 = reducer2.prove::<MultiDenseEqSumcheck<_>>(
            ctx,
            MultiPointEvalClaim::new(
                vec![
                    e_adj_claim_lookup.point.clone(),
                    t.to_vec(),
                    gamma,
                    i_acc.point,
                ],
                vec![
                    MultiPointEvalClaimPart::new(0, 1, e_ev_old),
                    MultiPointEvalClaimPart::new(0, 2, e_in_gamma_eval),
                    MultiPointEvalClaimPart::new(0, 0, e_adj_claim_lookup.ev - eq_eval(&vec![F::zero(); protocol.d], &e_adj_claim_lookup.point)),
                    MultiPointEvalClaimPart::new(1, 3, i_acc.ev),
                ],
            ),
            vec![
                e_poly,
                accesses_i,
            ]
        ).0;

        (claims_mess_2.evs[0] - claims_mess_2.evs[1]).require();
        (claims_mess_2.evs[0] - claims_mess_2.evs[2]).require();

        // All these claims should be returned.
        // This is a mess. there are actually like 12 of them.
        // Why would we invent a protocol like this?
        ((
            claims_mess_1,
            claims_mess_2,
            x_acc,
            y_acc,
        ), ())
    }
}

#[cfg(test)]
mod tests {
    use itertools::Itertools;
    use crate::components::vspark::vspark::{Vspark, VsparkProverInput};
    use ark_bn254::Fq as F;
    use ark_std::UniformRand;
    use tracing::info_span;
    use crate::common::claims::EvalClaim;
    use crate::common::math::evaluate_multivar;
    use crate::components::vspark::matrix::{tau::no_decomposition::table, r_size, VsparkMatrixGroup};
    use crate::protocol::component::TProtocol;
    use crate::transcript::transcript::tests::ManualTestTranscript;

    use tracing::level_filters::LevelFilter;
    use tracing_subscriber::{EnvFilter, fmt, prelude::*, reload, Registry, Layer};
    use tracing_subscriber::fmt::format::FmtSpan;
    use tracing_subscriber::layer::{Layered, SubscriberExt};
    use tracing_subscriber::util::{SubscriberInitExt, TryInitError};

    #[test]
    fn test_vspark() {
        // Create a tracing layer with the configured tracer
        let tracer = tracing_subscriber::registry();
        let tracer = tracer
            .with(EnvFilter::builder()
                .with_default_directive(LevelFilter::INFO.into())
                .from_env_lossy())
            .with(tracing_span_tree::span_tree().aggregate(true))
            .init();

        let rng = &mut ark_std::test_rng();
        let span = info_span!("test").entered();
        for _ in 0..10 {
            let (nx, px, ny, py, h, d) = (
                5,
                3,
                5,
                4,
                3,
                3,
            );
            let grp = VsparkMatrixGroup::<F>::rand(
                rng,
                nx,
                px,
                ny,
                py,
                h,
                d,
            );
            let vspark = Vspark::<F>::new(
                nx,
                px,
                ny,
                py,
                h,
                d,
            );

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

            let mut transcript_p = ManualTestTranscript::new((0..1000).map(|_| F::rand(rng)).collect_vec());
            let (output_claims, _) = vspark.prove::<Vspark<_, >>(&mut transcript_p, e_claim_before.clone(), prover_input);
            let proof = transcript_p.end();
            let mut transcript_v = transcript_p;

            let expected_output_claims = vspark.verify(&mut transcript_v, e_claim_before.clone());
            transcript_v.end();
            assert_eq!(output_claims, expected_output_claims);
        }
    }
}
