use std::iter::{once, repeat};
use itertools::Itertools;
use rayon::prelude::*;
use super::wrapper::{ComputationalField, TFelt, TSigUtil};

/// Computes polynomial coefficients from values in points 0, 1, 2, ..., n
pub fn from_evals<F: ComputationalField>(evals: &[F]) -> Vec<F> where <F as TSigUtil>::Constants: From<u64> {
    vandermonde_interpolation(evals)
}


pub fn evaluate_univar<F: TFelt>(poly: &[F], x: &F) -> F {
    let l = poly.len();
    assert!(l > 0);
    let mut run = poly[l - 1].clone();
    for i in 0 .. l - 1 {
        run = run.clone() * x;
        run = run.clone() + &poly[l - i - 2];
    }
    run
}

/// Returns p(0) + p(1) and all coefficients but the 1st one.
pub fn compress<F: TFelt>(coeffs: &[F]) -> (F, Vec<F>) {
    let sum = coeffs.iter().fold(coeffs[0], |acc, upd| acc + upd); // add with coefficients 2, 1, 1, 1, 1 ...
    let coeffs_without_1st : Vec<F> = once(&coeffs[0]).chain(coeffs[2..].iter()).map(|x| x.clone()).collect();
    (sum, coeffs_without_1st)
}

/// Reverts compression
pub fn decompress<F: TFelt>(sum: &F, coeffs_without_1st: &[F]) -> Vec<F> {
    let first_coeff = coeffs_without_1st.iter().fold(*sum - coeffs_without_1st[0], |acc, upd| acc - upd); // sum - 2 * coeff[0] - coeff[1] - coeff[2] ...
    once(&coeffs_without_1st[0]).chain(once(&first_coeff)).chain(coeffs_without_1st[1..].iter()).map(|x| x.clone()).collect()
}

pub fn bind_dense_poly<F: TFelt>(poly: &mut Vec<F>, t: F) {
    let half = poly.len() / 2;
    *poly = (0..half).into_iter().map(|i| poly[2*i] + t * (poly[2*i + 1] - poly[2*i])).collect();
}
// Vandermonde interpolation shamelessly stolen from liblasso.

pub fn vandermonde_interpolation<F: ComputationalField>(evals: &[F]) -> Vec<F> where <F as TSigUtil>::Constants: From<u64> {
    let n = evals.len();
    let xs: Vec<F> = (0..n).map(|x| F::from_const(x as u64)).collect();

    let mut vandermonde: Vec<Vec<F>> = Vec::with_capacity(n);
    for i in 0..n {
        let mut row = Vec::with_capacity(n);
        let x = xs[i];
        row.push(F::one());
        row.push(x);
        for j in 2..n {
        row.push(row[j - 1] * x);
        }
        row.push(evals[i]);
        vandermonde.push(row);
    }

    gaussian_elimination(&mut vandermonde)
}


pub fn gaussian_elimination<F: ComputationalField>(matrix: &mut [Vec<F>]) -> Vec<F> {
let size = matrix.len();
assert_eq!(size, matrix[0].len() - 1);

for i in 0..size - 1 {
    for j in i..size - 1 {
    echelon(matrix, i, j);
    }
}

for i in (1..size).rev() {
    eliminate(matrix, i);
}

// Disable cargo clippy warnings about needless range loops.
// Checking the diagonal like this is simpler than any alternative.
#[allow(clippy::needless_range_loop)]
for i in 0..size {
    if matrix[i][i] == F::zero() {
    println!("Infinitely many solutions");
    }
}

let mut result: Vec<F> = vec![F::zero(); size];
for i in 0..size {
    result[i] = matrix[i][size] * matrix[i][i].invert();
}
result
}

fn echelon<F: ComputationalField>(matrix: &mut [Vec<F>], i: usize, j: usize) {
    let size = matrix.len();
    if matrix[i][i] == F::zero() {
    } else {
        let factor = matrix[j + 1][i] * matrix[i][i].invert();
        (i..size + 1).for_each(|k| {
            let tmp = matrix[i][k];
            matrix[j + 1][k] = matrix[j + 1][k] - factor * tmp;
        });
    }
  }
  
fn eliminate<F: ComputationalField>(matrix: &mut [Vec<F>], i: usize) {
    let size = matrix.len();
    if matrix[i][i] == F::zero() {
    } else {
        for j in (1..i + 1).rev() {
        let factor = matrix[j - 1][i] * matrix[i][i].invert();
        for k in (0..size + 1).rev() {
            let tmp = matrix[i][k];
            matrix[j - 1][k] = matrix[j - 1][k] - factor * tmp;
        }
        }
    }
}

// EQ poly evals
struct EQPolyEvaluator<F: TFelt> {
    padding_size: usize,
    multiplier: F,
}

impl<F: TFelt> EQPolyEvaluator<F> {
    fn new() -> Self {
        Self {
            padding_size: 0,
            multiplier: F::one(),
        }
    }

    fn from_multiplier(multiplier: F) -> Self {
        Self {
            padding_size: 0,
            multiplier,
        }
    }

    fn from_padding(padding_size: usize) -> Self {
        Self {
            padding_size,
            multiplier: F::one(),
        }
    }

    fn with_multiplier(mut self, poly: &F) -> Self {
        self.multiplier = *poly;
        self
    }

    fn with_padding(mut self, padding_size: usize) -> Self {
        self.padding_size = padding_size;
        self
    }
    fn seq(self, pt: &[F]) -> Vec<Vec<F>> {
        let Self{  padding_size, multiplier } = self;
        let l = pt.len();
        let mut ret = Vec::with_capacity(l + 1);
        ret.push(vec![multiplier]);
        for i in 1..=padding_size {
            ret.push(vec![ret[i - 1][0] * (F::one() - pt[i - 1])]);
        }

        for i in (padding_size + 1)..=l {
            let last = &ret[i - 1];
            let multiplier = &pt[i - 1];

            let mut incoming = vec![F::zero(); 1 << (i - padding_size)];
            for j in (0..1 << (i - 1 - padding_size)) {
                let w = &last[j];
                let m = *multiplier * w;
                incoming[2 * j] = *w - m;
                incoming[2 * j + 1] = m;
            }
            ret.push(incoming);

            // let mut incoming = UninitArr::<F>::new(1 << (i - padding_size));
            // unsafe {
            //     let ptr = incoming.as_shared_mut_ptr();
            //     #[cfg(not(feature = "parallel"))]
            //     let iter = (0 .. (1 << (i - 1 - padding_size))).into_iter();
            //
            //     #[cfg(feature = "parallel")]
            //     let iter = (0 .. (1 << (i - 1 - padding_size))).into_par_iter();
            //
            //     iter.map(|j|{
            //         let w = &last[j];
            //         let m = *multiplier * w;
            //         *ptr.get_mut(2 * j) = *w - m;
            //         *ptr.get_mut(2 * j + 1) = m;
            //     }).count();
            //     ret.push(incoming.assume_init());
            // }
        }

        ret
    }

    fn last(self, pt: &[F]) -> Option<Vec<F>> {
        self.seq(pt).pop()
    }
}
pub fn padded_eq_poly_sequence<F: TFelt>(padding_size: usize, pt: &[F]) -> Vec<Vec<F>> {
    EQPolyEvaluator::from_padding(padding_size).seq(pt)
}

pub fn eq_poly_sequence<F: TFelt>(pt: &[F]) -> Vec<Vec<F>> {
    EQPolyEvaluator::new().seq(pt)
}

fn eq_poly_sequence_last<F: TFelt>(pt: &[F]) -> Option<Vec<F>> {
    EQPolyEvaluator::new().last(pt)
}

pub fn eq_poly_sequence_from_multiplier_last<F: TFelt>(mul: F, pt: &[F]) -> Option<Vec<F>> {
    EQPolyEvaluator::from_multiplier(mul).last(pt)
}

// multivar poly
pub fn evaluate_multivar<F: ComputationalField>(poly: &[F], pt: &[F]) -> F {
    let e_p = eq_poly(pt);
    poly.par_iter().zip_eq(e_p.par_iter()).map(|(&a, b)| a * b).sum()
    
}

pub fn evaluate_index_poly<F: TFelt>(pt: &[F]) -> F {
    let mut c = F::one();
    pt.iter().map(|x| {
        let res = *x * c;
        c = c.double();
        res
    }).fold(F::zero(), |x, y| x + y)
    
}

pub fn eq_poly<F: ComputationalField>(pt: &[F]) -> Vec<F> {
    let mut pt = pt.to_vec();
    pt.reverse();
    eq_poly_sequence_last(&pt).unwrap()
}


pub fn top_bind_multivar<F: ComputationalField>(poly: &[F], t: F) -> Vec<F> {
    let mut res = poly[..poly.len() / 2].to_vec();
    for i in 0..res.len() {
        res[i] += t * (poly[poly.len() / 2 + i] - poly[i]);
    }
    res
}

pub fn top_bind_multivar_point<F: ComputationalField>(poly: &[F], pt: &[F]) -> Vec<F> {
    let mut res = poly.to_vec();
    for t in pt {
        res = top_bind_multivar(&res, *t);
    }
    res
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bn254::Fq as F;
    use ark_std::{test_rng, UniformRand};
    #[test]
    fn test_from_evals() {
        let rng = &mut test_rng();
        let evals = (0..16).map(|_| F::rand(rng)).collect_vec();
        let poly = from_evals(&evals);
        for i in 0..16 {
            assert!(evaluate_univar(&poly, &F::from(i as u64)) == evals[i]);
        }
    }
}