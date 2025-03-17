use std::ops::{Add, Mul, Neg, Sub};

use ark_ff::{One, PrimeField, Zero};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use itertools::Itertools;

// #[derive(Clone, PartialEq, Eq)]
// pub struct W<T: ?Sized + Clone>(pub T);

pub trait PolyOpUtil : Sized {
    type Constants : TPrimeField;
    /// This API is ugly as hell, but I need to get the board object from somewhere.
    /// The constant will be allocated in a same board as &self.
    fn from_const(&self, value: Self::Constants) -> Self;
    fn lc(coeffs: &[Self::Constants], sigs: &[Self]) -> Self;
}

pub trait PolyOps:
    Clone
    + Add<Self, Output = Self>
    + for<'a> Add<&'a Self, Output = Self>
    + for<'a> Add<&'a mut Self, Output = Self>
    + Mul<Self, Output = Self>
    + for<'a> Mul<&'a Self, Output = Self>
    + for<'a> Mul<&'a mut Self, Output = Self>
    + Sub<Self, Output = Self>
    + for<'a> Sub<&'a Self, Output = Self>
    + for<'a> Sub<&'a mut Self, Output = Self>
    + Neg<Output = Self>
    + Invert<Output = Self>
    + PartialEq
    + Eq
    + PolyOpUtil {
}

impl<T: Clone
    + Add<Self, Output = Self>
    + for<'a> Add<&'a Self, Output = Self>
    + for<'a> Add<&'a mut Self, Output = Self>
    + Mul<Self, Output = Self>
    + for<'a> Mul<&'a Self, Output = Self>
    + for<'a> Mul<&'a mut Self, Output = Self>
    + Sub<Self, Output = Self>
    + for<'a> Sub<&'a Self, Output = Self>
    + for<'a> Sub<&'a mut Self, Output = Self>
    + Neg<Output = Self>
    + Invert<Output = Self>
    + PartialEq
    + Eq
    + PolyOpUtil
> PolyOps for T {}

pub trait TPrimeField : PolyOps + Copy + Zero + One + From<u64> + 'static + CanonicalSerialize + CanonicalDeserialize {}
impl<T: PolyOps + Copy + Zero + One + From<u64> + 'static + CanonicalSerialize + CanonicalDeserialize> TPrimeField for T {}

pub trait Invert {
    type Output;
    fn invert(self) -> Option<Self::Output>;
}
// This passthrough WORKS for some reason (and does not conflict with impl for W<T> as long as W<T> is not PrimeField, of course).
// I do not understand why this works, but I'm not complaining.
impl<U: PrimeField> Invert for U {
    type Output = U;

    fn invert(self) -> Option<U> {
        self.inverse()
    }
}

impl<U: PrimeField> PolyOpUtil for U {
    type Constants = U;

    fn from_const(&self, value: Self::Constants) -> Self {
        value
    }

    fn lc(coeffs: &[Self::Constants], sigs: &[Self]) -> Self {
        coeffs.iter().zip_eq(sigs.iter()).fold(Self::zero(), |acc, (a, b)| acc + *a * b)
    }
}

// // Probably should write a macro for that.

// impl<T: PolyOps> Add<W<T>> for W<T> {
//     type Output = W<T>;

//     fn add(self, rhs: W<T>) -> Self::Output {
//         W(self.0 + rhs.0)
//     }
// }

// impl<T: PolyOps> Add<&W<T>> for W<T> {
//     type Output = W<T>;

//     fn add(self, rhs: &W<T>) -> Self::Output {
//         W(self.0 + rhs.0.clone())
//     }
// }
// impl<T: PolyOps> Add<&mut W<T>> for W<T> {
//     type Output = W<T>;

//     fn add(self, rhs: &mut W<T>) -> Self::Output {
//         W(self.0 + rhs.0.clone())
//     }
// }

// impl<T: PolyOps> Add<W<T>> for &W<T> {
//     type Output = W<T>;

//     fn add(self, rhs: W<T>) -> Self::Output {
//         W(self.0.clone() + rhs.0)
//     }
// }

// impl<T: PolyOps> Add<W<T>> for &mut W<T> {
//     type Output = W<T>;

//     fn add(self, rhs: W<T>) -> Self::Output {
//         W(self.0.clone() + rhs.0)
//     }
// }

// impl<T: PolyOps> Add<&W<T>> for &W<T> {
//     type Output = W<T>;

//     fn add(self, rhs: &W<T>) -> Self::Output {
//         W(self.0.clone() + rhs.0.clone())
//     }
// }

// impl<T: PolyOps> Add<&mut W<T>> for &W<T> {
//     type Output = W<T>;

//     fn add(self, rhs: &mut W<T>) -> Self::Output {
//         W(self.0.clone() + rhs.0.clone())
//     }
// }

// impl<T: PolyOps> Add<&W<T>> for &mut W<T> {
//     type Output = W<T>;

//     fn add(self, rhs: &W<T>) -> Self::Output {
//         W(self.0.clone() + rhs.0.clone())
//     }
// }

// impl<T: PolyOps> Add<&mut W<T>> for &mut W<T> {
//     type Output = W<T>;

//     fn add(self, rhs: &mut W<T>) -> Self::Output {
//         W(self.0.clone() + rhs.0.clone())
//     }
// }

// impl<T: PolyOps> Mul<W<T>> for W<T> {
//     type Output = W<T>;

//     fn mul(self, rhs: W<T>) -> Self::Output {
//         W(self.0 * rhs.0)
//     }
// }

// impl<T: PolyOps> Mul<&W<T>> for W<T> {
//     type Output = W<T>;

//     fn mul(self, rhs: &W<T>) -> Self::Output {
//         W(self.0 * rhs.0.clone())
//     }
// }
// impl<T: PolyOps> Mul<&mut W<T>> for W<T> {
//     type Output = W<T>;

//     fn mul(self, rhs: &mut W<T>) -> Self::Output {
//         W(self.0 * rhs.0.clone())
//     }
// }

// impl<T: PolyOps> Mul<W<T>> for &W<T> {
//     type Output = W<T>;

//     fn mul(self, rhs: W<T>) -> Self::Output {
//         W(self.0.clone() * rhs.0)
//     }
// }

// impl<T: PolyOps> Mul<W<T>> for &mut W<T> {
//     type Output = W<T>;

//     fn mul(self, rhs: W<T>) -> Self::Output {
//         W(self.0.clone() * rhs.0)
//     }
// }

// impl<T: PolyOps> Mul<&W<T>> for &W<T> {
//     type Output = W<T>;

//     fn mul(self, rhs: &W<T>) -> Self::Output {
//         W(self.0.clone() * rhs.0.clone())
//     }
// }

// impl<T: PolyOps> Mul<&mut W<T>> for &W<T> {
//     type Output = W<T>;

//     fn mul(self, rhs: &mut W<T>) -> Self::Output {
//         W(self.0.clone() * rhs.0.clone())
//     }
// }

// impl<T: PolyOps> Mul<&W<T>> for &mut W<T> {
//     type Output = W<T>;

//     fn mul(self, rhs: &W<T>) -> Self::Output {
//         W(self.0.clone() * rhs.0.clone())
//     }
// }

// impl<T: PolyOps> Mul<&mut W<T>> for &mut W<T> {
//     type Output = W<T>;

//     fn mul(self, rhs: &mut W<T>) -> Self::Output {
//         W(self.0.clone() * rhs.0.clone())
//     }
// }

// impl<T: PolyOps> Sub<W<T>> for W<T> {
//     type Output = W<T>;

//     fn sub(self, rhs: W<T>) -> Self::Output {
//         W(self.0 - rhs.0)
//     }
// }

// impl<T: PolyOps> Sub<&W<T>> for W<T> {
//     type Output = W<T>;

//     fn sub(self, rhs: &W<T>) -> Self::Output {
//         W(self.0 - rhs.0.clone())
//     }
// }
// impl<T: PolyOps> Sub<&mut W<T>> for W<T> {
//     type Output = W<T>;

//     fn sub(self, rhs: &mut W<T>) -> Self::Output {
//         W(self.0 - rhs.0.clone())
//     }
// }

// impl<T: PolyOps> Sub<W<T>> for &W<T> {
//     type Output = W<T>;

//     fn sub(self, rhs: W<T>) -> Self::Output {
//         W(self.0.clone() - rhs.0)
//     }
// }

// impl<T: PolyOps> Sub<W<T>> for &mut W<T> {
//     type Output = W<T>;

//     fn sub(self, rhs: W<T>) -> Self::Output {
//         W(self.0.clone() - rhs.0)
//     }
// }

// impl<T: PolyOps> Sub<&W<T>> for &W<T> {
//     type Output = W<T>;

//     fn sub(self, rhs: &W<T>) -> Self::Output {
//         W(self.0.clone() - rhs.0.clone())
//     }
// }

// impl<T: PolyOps> Sub<&mut W<T>> for &W<T> {
//     type Output = W<T>;

//     fn sub(self, rhs: &mut W<T>) -> Self::Output {
//         W(self.0.clone() - rhs.0.clone())
//     }
// }

// impl<T: PolyOps> Sub<&W<T>> for &mut W<T> {
//     type Output = W<T>;

//     fn sub(self, rhs: &W<T>) -> Self::Output {
//         W(self.0.clone() - rhs.0.clone())
//     }
// }

// impl<T: PolyOps> Sub<&mut W<T>> for &mut W<T> {
//     type Output = W<T>;

//     fn sub(self, rhs: &mut W<T>) -> Self::Output {
//         W(self.0.clone() - rhs.0.clone())
//     }
// }


// impl<T: PolyOps> Neg for W<T> {
//     type Output = W<T>;
    
//     fn neg(self) -> Self::Output {
//         W(-self.0)
//     }
// }

// impl<T: PolyOps> Neg for &W<T> {
//     type Output = W<T>;
    
//     fn neg(self) -> Self::Output {
//         W(-self.0.clone())
//     }
// }

// impl<T: PolyOps> Neg for &mut W<T> {
//     type Output = W<T>;
    
//     fn neg(self) -> Self::Output {
//         W(-self.0.clone())
//     }
// }

// impl<T: TPrimeField> Invert for W<T> {
//     type Output = W<T>;

//     fn invert(self) -> Option<Self::Output> {
//         self.0.invert().map(|x|W(x))
//     }
// }

// impl<T: TPrimeField> Invert for &W<T> {
//     type Output = W<T>;

//     fn invert(self) -> Option<Self::Output> {
//         self.0.invert().map(|x|W(x))
//     }
// }
// impl<T: TPrimeField> Invert for &mut W<T> {
//     type Output = W<T>;

//     fn invert(self) -> Option<Self::Output> {
//         self.0.invert().map(|x|W(x))
//     }
// }

// impl<T: TPrimeField> From<u64> for W<T> {
//     fn from(value: u64) -> Self {
//         W(value.into())
//     }
// }
// impl<T: TPrimeField> Zero for W<T> {
//     fn zero() -> Self {
//         W(T::zero())
//     }
    
//     fn is_zero(&self) -> bool {
//         self.0.is_zero()
//     }
// }
// impl<T: TPrimeField> One for W<T> {
//     fn one() -> Self {
//         W(T::one())
//     }
// }
// impl<T: TPrimeField> Copy for W<T> {}