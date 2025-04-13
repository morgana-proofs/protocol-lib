use std::fmt::Debug;
use std::iter::Sum;
use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign};

use ark_ff::{PrimeField, UniformRand};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};

pub trait ComputationalField: TFelt + From<u64> + CanonicalSerialize + CanonicalDeserialize + Send + Sync + PartialEq + Eq + UniformRand {}
impl<T: TFelt + From<u64> + CanonicalSerialize + CanonicalDeserialize + Send + Sync + PartialEq + Eq + UniformRand> ComputationalField for T {}

pub trait TFeltUtil : Sized {
    type Constants : ComputationalField;
    fn from_const(value: impl Into<Self::Constants>) -> Self;
    fn static_pow(&self, exp: &[u64]) -> Self;
    /// Asserts that value is zero.
    fn require(&self);
    fn zero() -> Self;
    fn one() -> Self;
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