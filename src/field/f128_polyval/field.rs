use std::{iter::Sum, ops::{Add, AddAssign, BitAnd, BitAndAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign}};
use ark_ff::UniformRand;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Valid};
use ark_std::rand::Rng;
use bytemuck::{cast, Pod, Zeroable};

use crate::common::wrapper::{Double, Invert, TFeltUtil};

use super::{backend::autodetect::*, precompute::{frobenius_table::FROBENIUS, cobasis_table::COBASIS, cobasis_frobenius_table::COBASIS_FROBENIUS}, utils::*};

#[repr(transparent)]
#[derive(Clone, Copy, Debug, PartialEq, Eq, Pod, Zeroable)]
pub struct F128 {
    pub(crate) raw: u128,
}

impl F128 {
    pub fn new(x: bool) -> Self {
        if x {Self::one()} else {Self::zero()}
    }

    pub fn from_raw(raw: u128) -> Self {
        Self{raw}
    }

    pub fn raw(&self) -> u128 {
        self.raw
    }

    pub fn into_raw(self) -> u128 {
        self.raw
    }

    /// This function is not efficient.
    pub fn frob(&self, mut k: i32) -> Self {
        if k < 0 {
            k *= -1;
            k %= 128;
            k *= -1;
            k += 128;
        } else {
            k %= 128
        }
        let matrix = &FROBENIUS[k as usize]; 
        let mut ret = 0;
        let vec_bits = u128_to_bits(self.raw());
        for i in 0..128 {
            if vec_bits[i] {ret ^= matrix[i]}
        }
        F128::from_raw(ret)
    }

    pub fn basis(i: usize) -> Self {
        assert!(i < 128);
        Self::from_raw(1 << i)
    }

    pub fn cobasis(i: usize) -> Self {
        Self::from_raw(COBASIS[i])
    }
}

impl Add<F128> for F128 {
    type Output = F128;

    fn add(self, rhs: Self) -> Self::Output {
        Self{raw: self.into_raw() ^ rhs.into_raw()}
    }
}

impl Add<&F128> for F128 {
    type Output = F128;

    fn add(self, rhs: &F128) -> Self::Output {
        Self{raw: self.into_raw() ^ rhs.raw()}
    }
}

impl Add<&mut F128> for F128 {
    type Output = F128;

    fn add(self, rhs: &mut F128) -> Self::Output {
        Self{raw: self.into_raw() ^ rhs.raw()}
    }
}

impl BitAnd<F128> for F128 {
    type Output = F128;
    
    fn bitand(self, rhs: F128) -> Self::Output {
        Self{raw: self.into_raw() & rhs.into_raw()}
    }
}

impl BitAnd<&F128> for F128 {
    type Output = F128;
    
    fn bitand(self, rhs: &F128) -> Self::Output {
        Self{raw: self.into_raw() & rhs.raw()}
    }
}

impl AddAssign<F128> for F128 {
    fn add_assign(&mut self, rhs: F128) {
        self.raw ^= rhs.into_raw()
    }
}

impl AddAssign<&F128> for F128 {
    fn add_assign(&mut self, rhs: &F128) {
        self.raw ^= rhs.raw()
    }
}

impl AddAssign<&mut F128> for F128 {
    fn add_assign(&mut self, rhs: &mut F128) {
        self.raw ^= rhs.raw()
    }
}

impl BitAndAssign<F128> for F128 {
    fn bitand_assign(&mut self, rhs: F128) {
        self.raw &= rhs.into_raw();
    }
}

impl BitAndAssign<&F128> for F128 {
    fn bitand_assign(&mut self, rhs: &F128) {
        self.raw &= rhs.raw();
    }
}

impl Mul<F128> for F128 {
    type Output = F128;

    fn mul(self, rhs: F128) -> Self::Output {
        Self::from_raw(mul_128(self.raw, rhs.raw))
    }
}

impl Mul<&F128> for F128 {
    type Output = F128;

    fn mul(self, rhs: &F128) -> Self::Output {
        Self::from_raw(mul_128(self.into_raw(), rhs.raw()))
    }
}

impl Mul<&mut F128> for F128 {
    type Output = F128;

    fn mul(self, rhs: &mut F128) -> Self::Output {
        Self::from_raw(mul_128(self.into_raw(), rhs.raw()))
    }
}

impl MulAssign<F128> for F128 {
    fn mul_assign(&mut self, rhs: F128) {
        *self = *self * rhs;
    }
}

impl MulAssign<&F128> for F128 {
    fn mul_assign(&mut self, rhs: &F128) {
        *self = *self * rhs;
    }
}

impl MulAssign<&mut F128> for F128 {
    fn mul_assign(&mut self, rhs: &mut F128) {
        *self = *self * rhs;
    }
}

impl Sub<F128> for F128 {
    type Output = F128;

    fn sub(self, rhs: Self) -> Self::Output {
        Self{raw: self.into_raw() ^ rhs.into_raw()}
    }
}

impl Sub<&F128> for F128 {
    type Output = F128;

    fn sub(self, rhs: &F128) -> Self::Output {
        Self{raw: self.into_raw() ^ rhs.raw()}
    }
}

impl Sub<&mut F128> for F128 {
    type Output = F128;

    fn sub(self, rhs: &mut F128) -> Self::Output {
        Self{raw: self.into_raw() ^ rhs.raw()}
    }
}

impl SubAssign<F128> for F128 {
    fn sub_assign(&mut self, rhs: F128) {
        self.raw ^= rhs.into_raw()
    }
}

impl SubAssign<&F128> for F128 {
    fn sub_assign(&mut self, rhs: &F128) {
        self.raw ^= rhs.raw()
    }
}

impl SubAssign<&mut F128> for F128 {
    fn sub_assign(&mut self, rhs: &mut F128) {
        self.raw ^= rhs.raw()
    }
}

impl Div<F128> for F128 {
    type Output = F128;

    fn div(self, rhs: F128) -> Self::Output {
        todo!()
    }
}

impl Div<&F128> for F128 {
    type Output = F128;

    fn div(self, rhs: &F128) -> Self::Output {
        todo!()
    }
}

impl Div<&mut F128> for F128 {
    type Output = F128;

    fn div(self, rhs: &mut F128) -> Self::Output {
        todo!()
    }
}

impl DivAssign<F128> for F128 {
    fn div_assign(&mut self, rhs: F128) {
        todo!()
    }
}

impl DivAssign<&F128> for F128 {
    fn div_assign(&mut self, rhs: &F128) {
        todo!()
    }
}

impl DivAssign<&mut F128> for F128 {
    fn div_assign(&mut self, rhs: &mut F128) {
        todo!()
    }
}

impl TFeltUtil for F128 {
    type Constants = F128;

    fn from_const(value: impl Into<Self::Constants>) -> Self {
        value.into()
    }

    fn static_pow(&self, exp: &[u64]) -> Self {
        todo!()
    }

    fn require(&self) {
        assert!(*self == F128::zero())
    }

    fn zero() -> Self {
        Self{raw: 0}
    }

    fn one() -> Self {
        Self{raw: 257870231182273679343338569694386847745}
    }
}

impl Double for F128 {
    fn double(&self) -> Self {
        F128 { raw: 0 }
    }
}

impl Invert for F128 {
    type Output = Self;

    fn invert(self) -> Self::Output {
        todo!()
    }
}

impl CanonicalSerialize for F128 {
    fn serialize_with_mode<W: std::io::Write>(
        &self,
        writer: W,
        compress: ark_serialize::Compress,
    ) -> Result<(), ark_serialize::SerializationError> {
        cast::<u128, [u64; 2]>(self.raw()).serialize_with_mode(writer, compress)
    }

    fn serialized_size(&self, compress: ark_serialize::Compress) -> usize {
        cast::<u128, [u64; 2]>(self.raw()).serialized_size(compress)
    }
}

impl Valid for F128 {
    fn check(&self) -> Result<(), ark_serialize::SerializationError> {
        Ok(())
    }
}

impl CanonicalDeserialize for F128 {
    fn deserialize_with_mode<R: std::io::Read>(
        reader: R,
        compress: ark_serialize::Compress,
        validate: ark_serialize::Validate,
    ) -> Result<Self, ark_serialize::SerializationError> {
        match <[u64; 2] as CanonicalDeserialize>::deserialize_with_mode(reader, compress, validate) {
            Ok(x) => Ok(F128 {raw: cast::<[u64; 2], u128>(x)}),
            Err(x) => Err(x)
        }
    }
}

impl From<u64> for F128 {
    fn from(value: u64) -> Self {
        todo!()
    }
}

impl Sum for F128 {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(F128::zero(), |a, b| a + b)
    }
}

impl Neg for F128 {
    type Output = F128;

    fn neg(self) -> Self::Output {
        self
    }
}

impl UniformRand for F128 {
    fn rand<R: Rng + ?Sized>(rng: &mut R) -> Self {
        Self::from_raw(u128_rand(rng))
    }
}


// Computes \sum_j COBASIS[i]^{2^j} twists[j] 
pub fn pi(i: usize, twists: &[F128]) -> F128 {
    assert!(twists.len() == 128);
    let mut ret = F128::zero();
    for j in 0..128 {
        ret += F128::from_raw(COBASIS_FROBENIUS[j][i]) * twists[j];
    }
    ret
}

#[cfg(test)]
mod tests {
    use std::{fs::File, io::Write, path::Path};
    use ark_std::test_rng;

    use super::*;

    #[test]
    fn precompute_frobenius() {
        let path = Path::new("frobenius_table.txt");
        if path.is_file() {return};
        let mut file = File::create(path).unwrap();
        let mut basis = Matrix::diag();
        let mut ret = Vec::with_capacity(128);
        for _ in 0..128 {
            ret.push(basis.cols.clone());
            for j in 0..128 {
                let x = F128::from_raw(basis.cols[j]);
                basis.cols[j] = (x * x).raw();
            }
        }
        assert_eq!(basis, Matrix::diag());

        file.write_all("pub const FROBENIUS : [[u128; 128]; 128] =\n".as_bytes()).unwrap();
        file.write_all(format!("{:?}", ret).as_bytes()).unwrap();
        file.write_all(";".as_bytes()).unwrap();
    }

    #[test]
    fn precompute_cobasis_frobenius() {
        let path = Path::new("cobasis_frobenius_table.txt");
        if path.is_file() {return};
        let mut file = File::create(path).unwrap();
        let mut cobasis = Matrix::new(COBASIS.to_vec());
        let mut ret = Vec::with_capacity(128);
        for _ in 0..128 {
            ret.push(cobasis.cols.clone());
            for j in 0..128 {
                let x = F128::from_raw(cobasis.cols[j]);
                cobasis.cols[j] = (x * x).raw();
            }
        }
        file.write_all("pub const COBASIS_FROBENIUS : [[u128; 128]; 128] =\n".as_bytes()).unwrap();
        file.write_all(format!("{:?}", ret).as_bytes()).unwrap();
        file.write_all(";".as_bytes()).unwrap();

    }

    #[test]
    fn precompute_cobasis() {
        let path = Path::new("cobasis_table.txt");
        if path.is_file() {return};
        let mut file = File::create(path).unwrap();
        let mut matrix = vec![vec![false; 128]; 128];        
        for i in 0..128 {
            // compute pi_i linear function
            for j in 0..128 {
                let b_j = F128::basis(j);
                let b_i = F128::basis(i);
                let mut x = b_j * b_i;

                let mut s = F128::zero();
                for k in 0..128 {
                    s += x;
                    x *= x;
                }

                if s == F128::zero() {
                } else if s == F128::one() {
                        matrix[i][j] = true;
                } else {panic!()}

            }
        }
        let matrix = matrix.iter().map(|v| _u128_from_bits(v)).collect();
        let matrix = Matrix::new(matrix);
        let ret = matrix.inverse().unwrap().cols;
        file.write_all("pub const COBASIS : [u128; 128] =\n".as_bytes()).unwrap();
        file.write_all(format!("{:?}", ret).as_bytes()).unwrap();
        file.write_all(";".as_bytes()).unwrap();
    }

    #[test]
    fn f128_is_field() {
        let rng = &mut test_rng();
        let a = F128::rand(rng);
        let b = F128::rand(rng);
        let c = F128::rand(rng);

        let one = F128::one();

        assert_eq!(a * one, a);

        assert_eq!(a + b, b + a);
        assert_eq!(a * b, b * a);
        assert_eq!((a + b) * c, a * c + b * c);
        assert_eq!((a * b) * c, a * (b * c));

        let fr = |x: F128| {x * x};

        assert_eq!(fr(a) + fr(b), fr(a + b));

        let mut x = a;
        for _ in 0..128 {
            x = fr(x);    
        }
        assert_eq!(a, x);
    }

    #[test]
    fn frobenius() {
        let rng = &mut test_rng();
        let a = F128::rand(rng);
        let mut apow = a;
        for i in 0..128 {
            assert_eq!(a.frob(i), apow);
            apow *= apow;
        }
    }

    #[test]
    fn pi_as_expected() {
        let rng = &mut test_rng();
        let mut r = F128::rand(rng);
        let mut orbit = vec![];
        for _ in 0..128 {
            orbit.push(r);
            r *= r;
        }

        for i in 0..128 {
            let lhs;
            let bit = pi(i, &orbit);
            if bit == F128::zero() {
                lhs = 0;
            } else if bit == F128::one() {
                lhs = 1;
            } else {
                panic!();
            }
            let rhs = (r.raw >> i) % 2;
            assert!(lhs == rhs);
        }
    }

    #[test]
    fn twists_logic_and() {
        let rng = &mut test_rng();
        let a = F128::rand(rng);
        let b = F128::rand(rng);
        let mut _a = a;
        let mut _b = b;
        let mut a_orbit = vec![];
        let mut b_orbit = vec![];
        for _ in 0..128 {
            a_orbit.push(_a);
            b_orbit.push(_b);
            _a *= _a;
            _b *= _b;
        }
        let mut answer = F128::zero();
        for i in 0..128 {
            let pi_i_a = pi(i, &a_orbit);
            let pi_i_b = pi(i, &b_orbit);
            answer += F128::basis(i) * pi_i_a * pi_i_b;
        }
        let expected_answer = a & b;
        assert_eq!(answer, expected_answer);
    }
}