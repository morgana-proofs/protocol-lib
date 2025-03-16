use crate::common::wrapper::TPrimeField;

/// Represents prover view of multivariate polynomial that is being sumchecked.
pub trait Sumcheckable<F: TPrimeField> {
    /// Binds the polynomial on the coordinate t. Might be fallible unless unipoly() method was called.
    fn bind(&mut self, t: F);
    /// Returns the sum along all coordinates but the 0-th one.
    fn unipoly(&mut self) -> Vec<F>;
    /// Returns the evaluations of multilinear polynomials in a final challenge point.
    /// Opaque because some evals can be skipped if recoverable by verifier itself.
    fn final_evals(&self) -> Vec<F>;
    fn challenges(&self) -> &[F];
}

