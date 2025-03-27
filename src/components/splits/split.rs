use std::marker::PhantomData;
use itertools::Itertools;
use crate::common::claims::SinglePointClaims;
use crate::common::wrapper::PolyOps;
use crate::dialects::dialect::TArithmeticDialect;
use crate::protocol::component::{TProtocol, TProverImpl};

#[derive(Debug, Copy, Clone)]
pub enum SplitIdx {
    LO(usize),
    HI(usize),
}

impl SplitIdx {
    // LO: 7 6 5 4 3 2 1 0
    //     _ _ _ _ _ _ _ _
    // HI: 0 1 2 3 4 5 6 7
    // num_vars = 8

    pub fn to_hi(&self, num_vars: usize) -> Self {
        SplitIdx::HI(match self {
            SplitIdx::LO(lo) => {num_vars - lo - 1}
            SplitIdx::HI(hi) => {*hi}
        })
    }

    pub fn to_lo(&self, num_vars: usize) -> Self {
        SplitIdx::LO(match self {
            SplitIdx::HI(hi) => {num_vars - hi - 1}
            SplitIdx::LO(lo) => {*lo }
        })
    }

    pub fn hi_usize(&self, num_vars: usize) -> usize {
        match self.to_hi(num_vars) {
            SplitIdx::HI(hi) => hi,
            _ => unreachable!(),
        }
    }
    pub fn lo_usize(&self, num_vars: usize) -> usize {
        match self.to_lo(num_vars) {
            SplitIdx::LO(lo) => lo,
            _ => unreachable!(),
        }
    }
}

pub struct SplitAt<F: PolyOps> {
    pub bundle_size: usize,
    pub var_idx: SplitIdx,
    _pd: PhantomData<F>,
}
pub struct SplitAtParams<F> {
    bundle_size: usize,
    var_idx: SplitIdx,
    _pd: PhantomData<F>
}

impl<F: PolyOps> SplitAtParams<F> {
    pub fn set_bundle_size(mut self, bundle_size: usize) -> Self {
        self.bundle_size = bundle_size;
        self
    }
    pub fn set_lo_indexing(mut self) -> Self {
        self.var_idx = SplitIdx::LO(match self.var_idx {
            SplitIdx::HI(x) => {x}
            SplitIdx::LO(x) => {x}
        });
        self
    }

    pub fn set_hi_indexing(mut self) -> Self {
        self.var_idx = SplitIdx::HI(match self.var_idx {
            SplitIdx::HI(x) => {x}
            SplitIdx::LO(x) => {x}
        });
        self
    }

    pub fn set_var_idx(mut self, var_idx: usize) -> Self {
        self.var_idx = match self.var_idx {
            SplitIdx::LO(_) => {SplitIdx::LO(var_idx)}
            SplitIdx::HI(_) => {SplitIdx::HI(var_idx)}
        };
        self
    }
    pub fn end(self) -> SplitAt<F> {
        SplitAt::from_params(self)
    }
}

impl<F: PolyOps> SplitAt<F> {
    pub fn new(var_idx: SplitIdx, bundle_size: usize) -> Self {
        Self {
            bundle_size,
            var_idx,
            _pd: Default::default(),
        }
    }

    pub fn from_params(params: SplitAtParams<F>) -> Self {
        Self {
            bundle_size: params.bundle_size,
            var_idx: params.var_idx,
            _pd: Default::default(),
        }
    }
    pub fn builder() -> SplitAtParams<F> {
        SplitAtParams {
            bundle_size: 1,
            var_idx: SplitIdx::LO(0),
            _pd: PhantomData,
        }
    }
}

impl<F: PolyOps, Dialect: TArithmeticDialect<F>> TProtocol<Dialect> for SplitAt<F> {
    type ClaimsBefore = SinglePointClaims<F>;
    type ClaimsAfter = SinglePointClaims<F>;

    fn verify(&self, ctx: &mut Dialect, claims: Self::ClaimsBefore) -> Self::ClaimsAfter {
        let r = ctx.challenge();
        let SinglePointClaims { mut point, evs } = claims;

        let (iter_l, iter_r) = evs.chunks(self.bundle_size).tee();
        let evs_l = iter_l.step_by(2).flatten();
        let evs_r = iter_r.skip(1).step_by(2).flatten();

        let evs_new = evs_l.zip(evs_r).map(|(x, y)| x.clone() + r.clone() * (y.clone() - x.clone())).collect();

        point.insert(match self.var_idx {
            SplitIdx::LO(x) => {point.len() - x}
            SplitIdx::HI(x) => {x}
        }, r);

        SinglePointClaims{ point, evs: evs_new }
    }
}

impl<F: PolyOps, Dialect: TArithmeticDialect<F>> TProverImpl<Dialect> for SplitAt<F> {
    type Verifier = Self;
    type ProverInput = ();
    type ProverOutput = ();

    fn _prove(protocol: &Self::Verifier, ctx: &mut Dialect, claims: <Self::Verifier as TProtocol<Dialect>>::ClaimsBefore, advice: Self::ProverInput) -> (<Self::Verifier as TProtocol<Dialect>>::ClaimsAfter, Self::ProverOutput) {
        (protocol.verify(ctx, claims), ())
    }

}