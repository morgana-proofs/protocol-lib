use std::fmt::Debug;
use std::iter::Sum;
use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign};
use ark_ec::VariableBaseMSM;
use ark_ff::{BigInteger, PrimeField};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use itertools::Itertools;
use serde::{Deserialize, Serialize};

pub trait ComputationalField: TFelt + From<u64> + CanonicalSerialize + CanonicalDeserialize + Send + Sync + PartialEq + Eq + IOSerialisation + ChallengeSerialisation {}
impl<T: TFelt + From<u64> + CanonicalSerialize + CanonicalDeserialize + Send + Sync + PartialEq + Eq + IOSerialisation + ChallengeSerialisation> ComputationalField for T {}

pub trait TFeltUtil : Sized {
    type Constants : ComputationalField;
    fn from_const(value: impl Into<Self::Constants>) -> Self;
    fn static_pow(&self, exp: &[u64]) -> Self;
    /// Asserts that value is zero.
    fn require(&self);
    fn zero() -> Self;
    fn one() -> Self;
}

pub trait IOSerialisation: Sized + CanonicalSerialize + CanonicalDeserialize + Default {
    fn num_bytes() -> usize;
    fn deserialize(reader: &[u8]) -> Self;
    fn serialize(&self, writer: &mut Vec<u8>);
}
pub trait ChallengeSerialisation: Sized{
    const CHALLENGE_BYTES: usize;
    fn deserialize_challenge(reader: &[u8]) -> Self;
}

pub trait TFelt:
    Clone
    + Copy
    + Add<Self, Output = Self>
    + for<'a> Add<&'a Self, Output = Self>
    + for<'a> Add<&'a mut Self, Output = Self>
    + Mul<Self, Output = Self>
    + for<'a> Mul<&'a Self, Output = Self>
    + for<'a> Mul<&'a mut Self, Output = Self>
    + Sub<Self, Output = Self>
    + for<'a> Sub<&'a Self, Output = Self>
    + for<'a> Sub<&'a mut Self, Output = Self>
    + Div<Self, Output = Self>
    + for<'a> Div<&'a Self, Output = Self>
    + for<'a> Div<&'a mut Self, Output = Self>
    + AddAssign<Self>
    + for<'a> AddAssign<&'a Self>
    + for<'a> AddAssign<&'a mut Self>
    + MulAssign<Self>
    + for<'a> MulAssign<&'a Self>
    + for<'a> MulAssign<&'a mut Self>
    + SubAssign<Self>
    + for<'a> SubAssign<&'a Self>
    + for<'a> SubAssign<&'a mut Self>
    + DivAssign<Self>
    + for<'a> DivAssign<&'a Self>
    + for<'a> DivAssign<&'a mut Self>
    + Neg<Output = Self>
    + Invert<Output = Self>
    + Double
    + Debug
    + TFeltUtil
    + Sum
    {}

impl<T: Clone
    + Copy
    + Add<Self, Output = Self>
    + for<'a> Add<&'a Self, Output = Self>
    + for<'a> Add<&'a mut Self, Output = Self>
    + Mul<Self, Output = Self>
    + for<'a> Mul<&'a Self, Output = Self>
    + for<'a> Mul<&'a mut Self, Output = Self>
    + Sub<Self, Output = Self>
    + for<'a> Sub<&'a Self, Output = Self>
    + for<'a> Sub<&'a mut Self, Output = Self>
    + Div<Self, Output = Self>
    + for<'a> Div<&'a Self, Output = Self>
    + for<'a> Div<&'a mut Self, Output = Self>
    + AddAssign<Self>
    + for<'a> AddAssign<&'a Self>
    + for<'a> AddAssign<&'a mut Self>
    + MulAssign<Self>
    + for<'a> MulAssign<&'a Self>
    + for<'a> MulAssign<&'a mut Self>
    + SubAssign<Self>
    + for<'a> SubAssign<&'a Self>
    + for<'a> SubAssign<&'a mut Self>
    + DivAssign<Self>
    + for<'a> DivAssign<&'a Self>
    + for<'a> DivAssign<&'a mut Self>
    + Neg<Output = Self>
    + Invert<Output = Self>
    + Double
    + Debug
    + TFeltUtil
    + Sum
> TFelt for T {}

pub trait Double {
    fn double(&self) -> Self;
}

pub trait Invert {
    type Output;
    fn invert(self) -> Self::Output;
}
// This passthrough WORKS for some reason (and does not conflict with impl for W<T> as long as W<T> is not PrimeField, of course).
// I do not understand why this works, but I'm not complaining.
impl<U: PrimeField> Invert for U {
    type Output = U;

    fn invert(self) -> U {
        self.inverse().unwrap()
    }
}
impl<U: Sized + CanonicalSerialize + CanonicalDeserialize + Default> IOSerialisation for U {
    fn num_bytes() -> usize {
        U::compressed_size(&U::default())
    }

    fn deserialize(reader: &[u8]) -> Self {
        U::deserialize_compressed(reader).unwrap()
    }

    fn serialize(&self, writer: &mut Vec<u8>) {
        self.serialize_compressed(writer).unwrap();
    }
}

impl<U: PrimeField> ChallengeSerialisation for U {
    const CHALLENGE_BYTES: usize = U::BigInt::NUM_LIMBS * 8;

    fn deserialize_challenge(reader: &[u8]) -> Self {
        assert_eq!(reader.len(), Self::CHALLENGE_BYTES, "wrong challenge bytelen");
        U::from_le_bytes_mod_order(&reader)
    }
}

impl<U: PrimeField> Double for U {
    fn double(&self) -> Self {
        self.double()
    }
}

impl<U: PrimeField> TFeltUtil for U {
    type Constants = U;

    fn from_const(value: impl Into<Self::Constants>) -> Self {
        value.into()
    }

    fn static_pow(&self, exp: &[u64]) -> Self {
        self.pow(exp)
    }

    fn require(&self) {
        assert!(self.is_zero())
    }

    fn one() -> Self {
        Self::one()
    }

    fn zero() -> Self {
        Self::zero()
    }
}


pub trait TCurveGrep: Clone
    + Copy
    + Add<Self, Output = Self>
    // + for<'a> Add<&'a Self, Output = Self>
    // + for<'a> Add<&'a mut Self, Output = Self>

    + AddAssign<Self>
    // + for<'a> AddAssign<&'a Self>
    // + for<'a> AddAssign<&'a mut Self>
{
}

impl<G: Clone
    + Copy
    + Add<Self, Output = Self>
    + for<'a> Add<&'a Self, Output = Self>
    + for<'a> Add<&'a mut Self, Output = Self>

    + AddAssign<Self>
    + for<'a> AddAssign<&'a Self>
    + for<'a> AddAssign<&'a mut Self>
> TCurveGrep for G {
}

pub trait CurveGroup: TCurveGrep
    // + From<u64>
    + CanonicalSerialize
    + CanonicalDeserialize
    + Send
    + Sync
    + PartialEq
    + Eq
    + IOSerialisation
{}

impl<
    G: TCurveGrep
        // + From<u64>
        + CanonicalSerialize
        + CanonicalDeserialize
        + Send
        + Sync
        + PartialEq
        + Eq
        + IOSerialisation
> CurveGroup for G {}

pub trait TPairinkStructure {
    type ScalarField: TFelt;
    type G1: TCurveGrep
        + Mul<Self::ScalarField, Output = Self::G1>
        // + for<'a> Mul<&'a Self::ScalarField, Output = Self::G1>
        // + for<'a> Mul<&'a mut Self::ScalarField, Output = Self::G1>
        + MulAssign<Self::ScalarField>
        // + for<'a> MulAssign<&'a Self::ScalarField>
        // + for<'a> MulAssign<&'a mut Self::ScalarField>
    ;
    type G2: TCurveGrep
        + Mul<Self::ScalarField, Output = Self::G2>
        // + for<'a> Mul<&'a Self::ScalarField, Output = Self::G2>
        // + for<'a> Mul<&'a mut Self::ScalarField, Output = Self::G2>
        + MulAssign<Self::ScalarField>
        // + for<'a> MulAssign<&'a Self::ScalarField>
        // + for<'a> MulAssign<&'a mut Self::ScalarField>
    ;
}

pub trait TPairinkUtils: TPairinkStructure {
    fn require_pairing_eq(left_g1: Self::G1, left_g2: Self::G2, right_g1: Self::G1, right_g2: Self::G2);
}

pub trait TPairink: TPairinkStructure + TPairinkUtils {}
impl<T: TPairinkUtils> TPairink for T {}

pub trait PairingStructure: TPairink<ScalarField = <Self as PairingStructure>::ScalarField, G1 = <Self as PairingStructure>::G1, G2 = <Self as PairingStructure>::G2> {
    type ScalarField: ComputationalField;
    type G1: CurveGroup
        + Mul<<Self as PairingStructure>::ScalarField, Output = <Self as PairingStructure>::G1>
        // + for<'a> Mul<&'a <Self as PairingStructure>::ScalarField, Output = <Self as PairingStructure>::G1>
        // + for<'a> Mul<&'a mut <Self as PairingStructure>::ScalarField, Output = <Self as PairingStructure>::G1>
        + MulAssign<<Self as PairingStructure>::ScalarField>
        // + for<'a> MulAssign<&'a <Self as PairingStructure>::ScalarField>
        // + for<'a> MulAssign<&'a mut <Self as PairingStructure>::ScalarField>
    ;
    type G2: CurveGroup
        + Mul<<Self as PairingStructure>::ScalarField, Output = <Self as PairingStructure>::G2>
        // + for<'a> Mul<&'a <Self as PairingStructure>::ScalarField, Output = <Self as PairingStructure>::G2>
        // + for<'a> Mul<&'a mut <Self as PairingStructure>::ScalarField, Output = <Self as PairingStructure>::G2>
        + MulAssign<<Self as PairingStructure>::ScalarField>
        // + for<'a> MulAssign<&'a <Self as PairingStructure>::ScalarField>
        // + for<'a> MulAssign<&'a mut <Self as PairingStructure>::ScalarField>
    ;
}

impl<
    F: ComputationalField,
    G1: CurveGroup
        + Mul<F, Output = G1>
        // + for<'a> Mul<&'a F, Output = G1>
        // + for<'a> Mul<&'a mut F, Output = G1>
        + MulAssign<F>
        // + for<'a> MulAssign<&'a F>
        // + for<'a> MulAssign<&'a mut F>
    ,
    G2: CurveGroup
        + Mul<F, Output = G2>
        // + for<'a> Mul<&'a F, Output = G2>
        // + for<'a> Mul<&'a mut F, Output = G2>
        + MulAssign<F>
        // + for<'a> MulAssign<&'a F>
        // + for<'a> MulAssign<&'a mut F>
    ,
    P: TPairink + TPairinkStructure<ScalarField=F, G1=G1, G2=G2>,
> PairingStructure for P {
    type ScalarField = P::ScalarField;
    type G1 = P::G1;
    type G2 = P::G2;
}

pub trait PairingUtils: PairingStructure + TPairinkUtils {
    fn msm(bases: &[<Self as PairingStructure>::G1], poly: &[<Self as PairingStructure>::ScalarField]) -> <Self as PairingStructure>::G1;
}

pub trait Pairing: PairingStructure + PairingUtils {}
impl<T: PairingUtils> Pairing for T {}

impl<Ctx: ark_ec::pairing::Pairing> TPairinkStructure for Ctx {
    type ScalarField = Ctx::ScalarField;
    type G1 = Ctx::G1;
    type G2 = Ctx::G2;
}

impl<Ctx: ark_ec::pairing::Pairing> TPairinkUtils for Ctx {
    fn require_pairing_eq(left_g1: Self::G1, left_g2: Self::G2, right_g1: Self::G1, right_g2: Self::G2) {
        assert_eq!(
            Ctx::pairing(left_g1, left_g2),
            Ctx::pairing(right_g1, right_g2),
            "require_pairing_eq failed"
        )
    }
}

impl<Ctx: ark_ec::pairing::Pairing> PairingUtils for Ctx
{
    fn msm(bases: &[<Self as PairingStructure>::G1], poly: &[<Self as PairingStructure>::ScalarField]) -> <Self as PairingStructure>::G1 {
        <<Self as PairingStructure>::G1 as VariableBaseMSM>::msm(&bases.iter().map(|x| x.into()).collect_vec(), poly).unwrap()
    }
}