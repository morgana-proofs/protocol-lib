use std::iter::{once, repeat};

use super::wrapper::{PolyOps, TPrimeField};

/// Computes polynomial coefficients from values in points 0, 1, 2, ..., n
pub fn from_evals<F: TPrimeField>(evals: &[F]) -> Vec<F> {
    vandermonde_interpolation(evals)
}


pub fn evaluate_univar<F: PolyOps>(poly: &[F], x: &F) -> F {
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
/// Only uses PolyOps
pub fn compress<F: PolyOps>(coeffs: &[F]) -> (F, Vec<F>) {
    let lc_with : Vec<_> = once(2).chain(repeat(1)).take(coeffs.len()).map(|x| F::Constants::from(x)).collect(); // 2, 1, 1, 1 ...
    let sum = F::lc(&lc_with, coeffs);
    let coeffs_without_1st : Vec<F> = once(&coeffs[0]).chain(coeffs[2..].iter()).map(|x| x.clone()).collect();
    (sum, coeffs_without_1st)
}

/// Reverts compression
pub fn decompress<F: PolyOps>(sum: &F, coeffs_without_1st: &[F]) -> Vec<F> {
    let joined: Vec<F> = once(sum).chain(coeffs_without_1st.iter()).map(|x|x.clone()).collect(); // sum, coeff0, coeff2, coeff3 ...
    let lc_with : Vec<F::Constants> = once(F::Constants::from(1)).chain(once(-F::Constants::from(2))).chain(repeat(-F::Constants::from(1))).take(joined.len()).collect(); // 1, -2, -1, -1, -1, ...
    let first_coeff = F::lc(&lc_with, &joined);
    once(&coeffs_without_1st[0]).chain(once(&first_coeff)).chain(coeffs_without_1st[1..].iter()).map(|x| x.clone()).collect()
}

// Vandermonde interpolation shamelessly stolen from liblasso.

pub fn vandermonde_interpolation<F: TPrimeField>(evals: &[F]) -> Vec<F> {
    let n = evals.len();
    let xs: Vec<F> = (0..n).map(|x| F::from(x as u64)).collect();

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


pub fn gaussian_elimination<F: TPrimeField>(matrix: &mut [Vec<F>]) -> Vec<F> {
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
    result[i] = matrix[i][size] * matrix[i][i].invert().unwrap();
}
result
}

fn echelon<F: TPrimeField>(matrix: &mut [Vec<F>], i: usize, j: usize) {
    let size = matrix.len();
    if matrix[i][i] == F::zero() {
    } else {
        let factor = matrix[j + 1][i] * matrix[i][i].invert().unwrap();
        (i..size + 1).for_each(|k| {
            let tmp = matrix[i][k];
            matrix[j + 1][k] = matrix[j + 1][k] - factor * tmp;
        });
    }
  }
  
fn eliminate<F: TPrimeField>(matrix: &mut [Vec<F>], i: usize) {
    let size = matrix.len();
    if matrix[i][i] == F::zero() {
    } else {
        for j in (1..i + 1).rev() {
        let factor = matrix[j - 1][i] * matrix[i][i].invert().unwrap();
        for k in (0..size + 1).rev() {
            let tmp = matrix[i][k];
            matrix[j - 1][k] = matrix[j - 1][k] - factor * tmp;
        }
        }
    }
}