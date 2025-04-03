use std::marker::PhantomData;
use std::ops::Index;
use ark_ff::PrimeField;
use itertools::Itertools;
use crate::common::algfn::{AlgFn, AlgFnSO};
use crate::common::claims::{EvalClaim, SinglePointClaims, SumClaim};
use crate::common::wrapper::TPrimeField;
use crate::components::lookups::logup::logup::{IndexedLookupClaim, Logup, LookupClaim, LookupType};
use crate::components::sumcheck::dense::DenseSumcheck;
use crate::components::sumcheck::dense_eq::eq_eval;
use crate::components::sumcheck::generic::SumcheckProtocol;
use crate::components::sumcheck::multi_dense_eq::{MultiDenseEqSumcheck, MultiPointEvalClaim, MultiPointEvalClaimPart};
use crate::components::sumcheck::sumcheckable::Sumcheckable;
use crate::dialects::dialect::{TArithmeticDialect, TDialectInterface};
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

pub struct Vspark<F: TPrimeField> {
    d: usize,  // matrix number logsize
    h: usize,  // description logsize
    px: usize,
    py: usize,
    x_logsize: usize,
    y_logsize: usize,
    _pd: PhantomData<F>,
}

impl<F: TPrimeField> Vspark<F> {
    fn check_tau(&self, claim: EvalClaim<F>, point: &[F]) {
        todo!()
    }
}

///
///
type VsparkClaimsBefore<F: TPrimeField> = EvalClaim<F>;  // claim of M[t](r_x, r_y) at point (t | r_x | r_y)

pub struct VsparkClaimsAfter<F: TPrimeField> {
    e_claim_old: EvalClaim<F>,
    e_claim_new: EvalClaim<F>,
    c_claim: EvalClaim<F>,
    i_claim: EvalClaim<F>,
    x_claim: EvalClaim<F>,
    y_claim: EvalClaim<F>,
}

pub struct VsparkProverInput<F: TPrimeField> {
    e_poly: Vec<F>,
    c_poly: Vec<F>,
    i_poly: Vec<F>,
    x_poly: Vec<F>,
    y_poly: Vec<F>,
    _pd: PhantomData<F>
}

pub struct VsparkProverOutput<F: TPrimeField> {
    _pd: PhantomData<F>
}

#[derive(Clone)]
pub struct VsparkFinalProd<F>(F);

impl<F: TPrimeField> AlgFnSO<F> for VsparkFinalProd<F> {
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

impl<F: TPrimeField, Dialect: TArithmeticDialect<F>> TProtocol<Dialect> for Vspark<F> {
    type ClaimsBefore = VsparkClaimsBefore<F>;
    type ClaimsAfter = VsparkClaimsAfter<F>;

    fn verify(&self, ctx: &mut Dialect, claims: Self::ClaimsBefore) -> Self::ClaimsAfter {
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

        self.check_tau(tau_x_claim, r_x);
        self.check_tau(tau_y_claim, r_y);

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
        let claims_mess_1 = reducer.verify(ctx, MultiPointEvalClaim::new(
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


        let reducer2 = MultiDenseEqSumcheck::new(self.d);

        let claims_mess_2 = reducer2.verify(ctx, MultiPointEvalClaim::new(
            vec![
                e_claim_lookup.point,
                e_point_old,
                gamma,
                i_acc.point,
            ],
            vec![
                MultiPointEvalClaimPart::new(0, 0, e_claim_lookup.ev),
                MultiPointEvalClaimPart::new(0, 1, e_ev_old),
                MultiPointEvalClaimPart::new(0, 2, e_in_gamma_eval),
                MultiPointEvalClaimPart::new(1, 3, i_acc.ev),
            ],
        ));
        
        // All these claims should be returned.
        // This is a mess. there are actually like 12 of them.
        // Why would we invent a protocol like this?
        claims_mess_1;
        claims_mess_2;
        x_acc;
        y_acc;
        todo!()
    }
}

impl<F: TPrimeField, Dialect: TArithmeticDialect<F>> TProverImpl<Dialect> for Vspark<F> {
    type Verifier = Self;
    type ProverInput = VsparkProverInput<F>;
    type ProverOutput = VsparkProverOutput<F>;

    fn _prove(protocol: &Self::Verifier, ctx: &mut Dialect, claims: <Self::Verifier as TProtocol<Dialect>>::ClaimsBefore, advice: Self::ProverInput) -> (<Self::Verifier as TProtocol<Dialect>>::ClaimsAfter, Self::ProverOutput) {
        todo!()
    }
}

#[cfg(test)]
mod tests {
    use itertools::Itertools;
    use crate::components::vspark::vspark::Pad;

    #[test]
    fn test_pad_iterator() {
        assert_eq!(
            (0..3).collect_vec().into_iter().pad(4, 10).collect_vec(),
            vec![0, 1, 2, 4, 4, 4, 4, 4, 4, 4],
        )
    }
}