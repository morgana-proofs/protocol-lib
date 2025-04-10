use std::collections::HashMap;
use std::iter::once;
use std::marker::PhantomData;
use std::ops::Index;
use ark_ff::PrimeField;
use ark_std::iterable::Iterable;
use itertools::Itertools;
use crate::common::algfn::{AlgFn, AlgFnSO, AlgFnSoUtils};
use crate::common::claims::{EvalClaim, SinglePointClaims, SumClaim};
use crate::common::wrapper::{ComputationalField, TFelt};
use crate::components::lookups::logup::logup::{IndexedLookupClaim, IndexedLookupInput, Logup, LookupClaim, LookupInput, LookupType};
use crate::components::sumcheck::dense::DenseSumcheck;
use crate::components::sumcheck::dense_eq::eq_eval;
use crate::components::sumcheck::generic::SumcheckProtocol;
use crate::components::sumcheck::multi_dense_eq::{MultiDenseEqSumcheck, MultiPointEvalClaim, MultiPointEvalClaimPart};
use crate::components::sumcheck::sumcheckable::Sumcheckable;
use crate::components::vspark::matrix::{compute_tau_at_point, compute_tau_table};
use crate::transcript::transcript::{TArithmeticTranscript, TTranscriptInterface};
use crate::protocol::component::{TProtocol, TProverImpl};

pub struct Padded<T: Clone, It: Iterator<Item = T>> {
    inner: It,
    len: usize,
    up_to: usize,
    pad: T
}

impl<T: Clone, It: Iterator<Item=T>> Iterator for Padded<T, It> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        self.len += 1;
        self.inner.next().or_else(|| {
            if self.len <= self.up_to {
                Some(self.pad.clone())
            } else {
                None
            }
        })
    }
}

pub trait Pad<T: Clone>: Sized
where Self: Iterator<Item = T> {
    fn pad(self, elt: T, up_to: usize) -> Padded<T, Self>;
}

impl<T: Clone, It: Iterator<Item=T>> Pad<T> for It {
    fn pad(self, elt: T, up_to: usize) -> Padded<T, Self> {
        Padded {
            inner: self,
            len: 0,
            up_to,
            pad: elt,
        }
    }
}

pub struct Vspark<F: TFelt> {
    d: usize,  // matrix number logsize
    h: usize,  // description logsize
    n: usize,  // somehow needed for tau, must be sum of some other values here
    px: usize,
    py: usize,
    x_logsize: usize,
    y_logsize: usize,
    _pd: PhantomData<F>,
}

impl<F: TFelt> Vspark<F> {
    fn compute_tau(n: usize, p: usize, x: &[F], r: &[F]) -> F {
        compute_tau_at_point(n, p, x, r)
    }
}

///
///
type VsparkClaimsBefore<F: TFelt> = EvalClaim<F>;  // claim of M[t](r_x, r_y) at point (t | r_x | r_y)

pub struct VsparkClaimsAfter<F: TFelt> {
    _pd: PhantomData<F>,
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
pub struct VsparkFinalProd<F>(F);

impl<F: TFelt> AlgFnSO<F> for VsparkFinalProd<F> {
    fn exec(&self, args: &impl Index<usize, Output=F>) -> F {
        args[0] * args[1] * args[2] * args[3] + self.0
    }

    fn deg(&self) -> usize {
        4
    }

    fn n_ins(&self) -> usize {
        4
    }
}

impl<F: TFelt, Transcript: TArithmeticTranscript<F>> TProtocol<Transcript> for Vspark<F> {
    type ClaimsBefore = VsparkClaimsBefore<F>;
    type ClaimsAfter = (SinglePointClaims<F>, SinglePointClaims<F>, EvalClaim<F>, EvalClaim<F>);

    fn verify(&self, ctx: &mut Transcript, claims: Self::ClaimsBefore) -> Self::ClaimsAfter {
        let EvalClaim { ev: e_ev_old, point: e_point_old } = claims;
        let (t, rs) = e_point_old.split_at(self.d);
        let (r_x, rs) = rs.split_at(self.x_logsize);
        let (r_y, rs) = rs.split_at(self.y_logsize);
        assert_eq!(rs.len(), 0);

        let lookup = Logup::new(vec![
            LookupType::Indexed(self.x_logsize + 1, self.h + self.d),
            LookupType::Indexed(self.y_logsize + 1, self.h + self.d),
            LookupType::Indexed(self.d, self.h + self.d),
        ]);

        let lookup_claims: [_; 3] = lookup.verify(ctx, ()).into_iter().map(|c| {
            if let LookupClaim::Indexed(c) = c {
                c
            } else {
                panic!("Invalid LookupType::Indexed {:?}", c)
            }
        }).collect_array().unwrap();

        let [a, b, c] = lookup_claims; // RUST, WHY!?!?!?!
        let IndexedLookupClaim{ accesses: x_acc, table: tau_x_claim, values: x_pull, indexes: x_claim } = a;
        let IndexedLookupClaim{ accesses: y_acc, table: tau_y_claim, values: y_pull, indexes: y_claim } = b;
        let IndexedLookupClaim{ accesses: i_acc, table: e_claim_lookup, values: i_pull, indexes: i_claim } = c;

        (tau_x_claim.ev - Self::compute_tau(self.n, self.px, &tau_x_claim.point, r_x)).require();
        (tau_y_claim.ev - Self::compute_tau(self.n, self.py, &tau_y_claim.point, r_y)).require();

        let gamma = (0..self.d).map(|_| ctx.challenge()).collect_vec();

        let e_in_gamma_eval = ctx.read();

        let delta0_in_gamma = eq_eval(&vec![F::zero(); self.d], &gamma);
        let f = VsparkFinalProd(delta0_in_gamma);

        let sumcheck = DenseSumcheck::new(f, self.h);

        let e_claim_sumcheck: SinglePointClaims<F> = sumcheck.verify(ctx, SumClaim(e_in_gamma_eval));

        let mut sumcheck_point = gamma.clone();
        sumcheck_point.extend(e_claim_sumcheck.point);  // todo: check if order is correct

        let [c_ev_sumcheck, i_pull_ev_sumcheck, x_pull_ev_sumcheck, y_pull_ev_sumcheck] = e_claim_sumcheck.evs.try_into().unwrap();
        let reducer = MultiDenseEqSumcheck::new(self.h + self.d);
        let mut claims_mess_1 = reducer.verify(ctx, MultiPointEvalClaim::new(
            vec![
                sumcheck_point,
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
                e_claim_lookup.point,
                t.to_vec(),
                gamma,
                i_acc.point,
            ],
            vec![
                MultiPointEvalClaimPart::new(1, 3, i_acc.ev),
                MultiPointEvalClaimPart::new(0, 0, e_claim_lookup.ev),
                MultiPointEvalClaimPart::new(0, 1, e_ev_old),
                MultiPointEvalClaimPart::new(0, 2, e_in_gamma_eval),
            ],
        ));

        (claims_mess_2.evs[1] - claims_mess_2.evs[2]).require();
        (claims_mess_2.evs[1] - claims_mess_2.evs[3]).require();

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

    fn _prove(protocol: &Self::Verifier, ctx: &mut Transcript, claims: <Self::Verifier as TProtocol<Transcript>>::ClaimsBefore, advice: Self::ProverInput) -> (<Self::Verifier as TProtocol<Transcript>>::ClaimsAfter, Self::ProverOutput) {
        let VsparkProverInput{ e_poly, c_poly, i_poly, x_poly, y_poly, _pd } = advice;
        let EvalClaim { ev: e_ev_old, point: e_point_old } = claims;
        let (t, rs) = e_point_old.split_at(protocol.d);
        let (r_x, rs) = rs.split_at(protocol.x_logsize);
        let (r_y, rs) = rs.split_at(protocol.y_logsize);
        assert_eq!(rs.len(), 0);

        let lookup = Logup::new(vec![
            LookupType::Indexed(protocol.x_logsize + 1, protocol.h + protocol.d),
            LookupType::Indexed(protocol.y_logsize + 1, protocol.h + protocol.d),
            LookupType::Indexed(protocol.d, protocol.h + protocol.d),
        ]);

        let tau_table_x = compute_tau_table(protocol.n, protocol.px, r_x);
        let mut tau_accesses_x = tau_table_x.iter().map(|_| F::zero()).collect::<Vec<_>>();
        let tau_values_x = x_poly.iter().map(|idx| {
            tau_accesses_x[*idx] = tau_accesses_x[*idx] + F::one();
            tau_table_x[*idx]
        }).collect::<Vec<_>>();

        let tau_table_y = compute_tau_table(protocol.n, protocol.py, r_y);
        let mut tau_accesses_y = tau_table_x.iter().map(|_| F::zero()).collect::<Vec<_>>();
        let tau_values_y = y_poly.iter().map(|idx| {
            tau_accesses_y[*idx] = tau_accesses_y[*idx] + F::one();
            tau_table_y[*idx]
        }).collect::<Vec<_>>();

        let mut accesses_i = e_poly.iter().map(|_| F::zero()).collect::<Vec<_>>();
        let values_i = y_poly.iter().map(|idx| {
            accesses_i[*idx] = tau_accesses_y[*idx] + F::one();
            e_poly[*idx]
        }).collect::<Vec<_>>();


        let i_poly_f = i_poly.iter().map(|x| F::from(*x as u64)).collect_vec();
        let x_poly_f = x_poly.iter().map(|x| F::from(*x as u64)).collect_vec();
        let y_poly_f = y_poly.iter().map(|x| F::from(*x as u64)).collect_vec();

        let lookup_advice = vec![
            LookupInput::indexed_by_usize(
                tau_table_x,
                tau_accesses_x,
                tau_values_x.clone(),
                x_poly,
            ),
            LookupInput::indexed_by_usize(
                tau_table_y,
                tau_accesses_y,
                tau_values_y.clone(),
                y_poly,
            ),
            LookupInput::indexed_by_usize(
                e_poly.clone(),
                accesses_i.clone(),
                values_i.clone(),
                i_poly,
            ),
        ];

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
        let IndexedLookupClaim{ accesses: i_acc, table: e_claim_lookup, values: i_pull, indexes: i_claim } = c;

        (tau_x_claim.ev - Self::compute_tau(protocol.n, protocol.px, &tau_x_claim.point, r_x)).require();
        (tau_y_claim.ev - Self::compute_tau(protocol.n, protocol.py, &tau_y_claim.point, r_y)).require();

        let gamma = (0..protocol.d).map(|_| ctx.challenge()).collect_vec();

        let e_in_gamma_eval = ctx.read();

        let delta0_in_gamma = eq_eval(&vec![F::zero(); protocol.d], &gamma);
        let f = VsparkFinalProd(delta0_in_gamma);

        let e_data = vec![
            c_poly,
            i_poly_f.clone(),
            x_poly_f.clone(),
            y_poly_f.clone(),
        ];
        let e_output = f.map_so(&e_data.iter().map(|v| v.as_ref()).collect_vec());

        let sumcheck = DenseSumcheck::new(f, protocol.h);

        let e_claim_sumcheck: SinglePointClaims<F> = sumcheck.prove::<DenseSumcheck<_,_>>(ctx, SumClaim(e_in_gamma_eval), e_data).0;

        let mut sumcheck_point = gamma.clone();
        sumcheck_point.extend(e_claim_sumcheck.point);  // todo: check if order is correct

        let [c_ev_sumcheck, i_pull_ev_sumcheck, x_pull_ev_sumcheck, y_pull_ev_sumcheck] = e_claim_sumcheck.evs.try_into().unwrap();
        let reducer = MultiDenseEqSumcheck::new(protocol.h + protocol.d);
        let mut claims_mess_1 = reducer.prove::<MultiDenseEqSumcheck<_>>(
            ctx,
            MultiPointEvalClaim::new(
                vec![
                    sumcheck_point,
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
                e_output,
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
                    e_claim_lookup.point,
                    t.to_vec(),
                    gamma,
                    i_acc.point,
                ],
                vec![
                    MultiPointEvalClaimPart::new(1, 3, i_acc.ev),
                    MultiPointEvalClaimPart::new(0, 0, e_claim_lookup.ev),
                    MultiPointEvalClaimPart::new(0, 1, e_ev_old),
                    MultiPointEvalClaimPart::new(0, 2, e_in_gamma_eval),
                ],
            ),
            vec![
                accesses_i,
                e_poly,
            ]
        ).0;

        (claims_mess_2.evs[1] - claims_mess_2.evs[2]).require();
        (claims_mess_2.evs[1] - claims_mess_2.evs[3]).require();

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
    use crate::components::vspark::vspark::{Pad, Vspark};
    use ark_bn254::Fq as F;

    #[test]
    fn test_pad_iterator() {
        assert_eq!(
            (0..3).collect_vec().into_iter().pad(4, 10).collect_vec(),
            vec![0, 1, 2, 4, 4, 4, 4, 4, 4, 4],
        )
    }
    
    #[test]
    fn test_vspark_verifier_accepts_prover() {
        
    }
}