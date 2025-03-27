use std::marker::PhantomData;
use ark_ff::PrimeField;
use crate::common::algfn::AlgFnSO;
use crate::common::wrapper::{PolyOps, TPrimeField};
use crate::components::sumcheck::sumcheckable::Sumcheckable;
use crate::dialects::dialect::{TArithmeticDialect, TDialectInterface};
use crate::protocol::component::{TProtocol, TProverImpl};

pub struct Vspark<F: PolyOps> {
    d: usize,
    h: usize,
    _pd: PhantomData<F>,
}

impl<F: PolyOps> Vspark<F> {}

pub struct VsparkClaimsBefore<F: PolyOps> {
    _pd: PhantomData<F>,
}

pub struct VsparkClaimsAfter<F: PolyOps> {
    _pd: PhantomData<F>,
}

pub struct VsparkProverInput<F: PolyOps> {
    _pd: PhantomData<F>
}

pub struct VsparkProverOutput<F: PolyOps> {
    _pd: PhantomData<F>
}

impl<F: PolyOps, Dialect: TArithmeticDialect<F>> TProtocol<Dialect> for Vspark<F> {
    type ClaimsBefore = VsparkClaimsBefore<F>;
    type ClaimsAfter = VsparkClaimsAfter<F>;

    fn verify(&self, ctx: &mut Dialect, claims: Self::ClaimsBefore) -> Self::ClaimsAfter {
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