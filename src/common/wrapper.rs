use std::fmt::Debug;
use std::iter::Sum;
use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign};
use ark_ec::CurveGroup;
use ark_ff::{BigInteger, PrimeField};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use num_traits::Zero;
use serde::{Deserialize, Serialize};

pub trait ComputationalField: TFelt + From<u64> + CanonicalSerialize + CanonicalDeserialize + Send + Sync + PartialEq + Eq + IOSerialisation + ChallengeSerialisation {}
impl<T: TFelt + From<u64> + CanonicalSerialize + CanonicalDeserialize + Send + Sync + PartialEq + Eq + IOSerialisation + ChallengeSerialisation> ComputationalField for T {}

pub trait TSigUtil: Sized {
    type Constants : Into<Self>;
    fn from_const(value: impl Into<Self::Constants>) -> Self;
    /// Asserts that value is zero.
    fn require(&self);
    fn zero() -> Self;
}
pub trait TFeltUtil : Sized + TSigUtil {
    fn static_pow(&self, exp: &[u64]) -> Self;
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

impl<U: Zero> TSigUtil for U {
    type Constants = Self;

    fn from_const(value: impl Into<Self::Constants>) -> Self {
        value.into()
    }

    fn require(&self) {
        assert!(self.is_zero())
    }

    fn zero() -> Self {
        Self::zero()
    }
}

impl<U: PrimeField> TFeltUtil for U {
    fn static_pow(&self, exp: &[u64]) -> Self {
        self.pow(exp)
    }
    fn one() -> Self {
        Self::one()
    }
}

pub trait TGroupUtil: TSigUtil {
}
pub trait TGroup: Sized + Clone + Copy
    + TGroupUtil
    + Add
    + AddAssign
    + Sub
    + SubAssign
    + Mul<Self::ScalarField, Output = Self>
{
    type ScalarField: TFelt;
}
pub trait ComputationalGroup: TGroup + CanonicalSerialize + CanonicalDeserialize + Eq + PartialEq where Self::ScalarField: ComputationalField {}

impl<G: TSigUtil> TGroupUtil for G {}

impl<G: CurveGroup> TGroup for G {
    type ScalarField = G::ScalarField;
}