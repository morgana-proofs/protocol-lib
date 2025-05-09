// This implements non-hiding KZG commitments (in a form typically used in PlonK, i.e. powers of tau in first group, and
// only a single power of tau in a second group).

// Lagrange form is unimplemented, as we will not need it.

use std::fs::File;

use ark_ec::{CurveGroup, VariableBaseMSM};
use ark_ff::PrimeField;
use ark_std::{One, UniformRand};
use ark_std::rand::{Rng, RngCore};
use rayon::iter::IntoParallelIterator;
use rayon::iter::ParallelIterator;
use crate::common::wrapper::{TPairink, TFeltUtil, Pairing, PairingStructure};

#[derive(Clone)]
pub struct KzgProvingKey<Ctx: Pairing> {
    ptau_1: Vec<Ctx::G1>,
    h0: Ctx::G2,
    h1: Ctx::G2,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct KzgVerifyingKey<Ctx: TPairink> {
    tau0: Ctx::G1,
    h0: Ctx::G2,
    h1: Ctx::G2,
}

impl<Ctx: TPairink> KzgVerifyingKey<Ctx> {

    /// Directly verifies KZG opening proof.
    pub fn verify_directly(
        &self,
        poly_commitment: Ctx::G1,
        quotient_commitment: Ctx::G1,
        opening_at: Ctx::ScalarField,
        opening: Ctx::ScalarField,
    ) {
        Ctx::require_pairing_eq(
            poly_commitment + self.tau0 * (-opening), self.h0,
            quotient_commitment, self.h1 + self.h0 * (-opening_at),
        )
    }

    /// Transforms proof into pair with verifiying equation <pair.0, h0> == <pair.1, h1>.
    /// Useful in batching, because such pairs can be randomly combined.
    pub fn verify_reduce_to_pair(
        &self,
        poly_commitment: impl Into<Ctx::G1>,
        quotient_commitment: impl Into<Ctx::G1>,
        opening_at: Ctx::ScalarField,
        opening: Ctx::ScalarField,
    ) -> (Ctx::G1, Ctx::G1) {
        // e<[P] - b * G0, H0> == e<[Q], H1 - a H0>
        // e<[P] + a * [Q] - b * G0, H0> = e<[Q], H1>
        let quotient_commitment = quotient_commitment.into();
        ((quotient_commitment * opening_at + self.tau0 * (-opening) + poly_commitment.into()).into(), quotient_commitment.into())
    }

    /// Verifies <pair.0, h0> == <pair.1, h1>
    pub fn verify_pair(&self, pair: (Ctx::G1, Ctx::G1)) {
        Ctx::require_pairing_eq(
            pair.0, self.h0,
            pair.1, self.h1,
        );
    }

}

/// Computes quotient and remainder of division of p(x)/(x-a)
pub fn div_by_linear<F: PrimeField>(poly: &[F], pt: F) -> (Vec<F>, F) {
    let mut quotient = vec![F::zero(); poly.len()-1];
    let mut rem = poly[poly.len()-1];
    for i in (0..quotient.len()).rev() {
        quotient[i] = rem;
        rem = poly[i] + rem*pt;
    }
    (quotient, rem)
}

impl<Ctx: Pairing> KzgProvingKey<Ctx> {
    pub fn mock_setup(tau: <Ctx as PairingStructure>::ScalarField, g0: <Ctx as PairingStructure>::G1, h0: <Ctx as PairingStructure>::G2, size: usize) -> Self {
        let mut powers_of_tau = Vec::with_capacity(size);
        let mut p = <Ctx as PairingStructure>::ScalarField::one();
        for _ in 0..size {
            powers_of_tau.push(p);
            p *= tau;
        }

        let h1 : <Ctx as PairingStructure>::G2 = (h0 * tau).into();

        let ptau1_proj : Vec<<Ctx as PairingStructure>::G1> = powers_of_tau.into_par_iter().map(|sc| g0 * sc).collect();

        Self{ptau_1: <Ctx as PairingStructure>::G1::normalize_batch(&ptau1_proj), h0, h1}
    }

    pub fn load(file: &mut File) -> Self {
        todo!()
    }

    pub fn dump(&self, file: &mut File) {
        todo!()
    }

    pub fn ptau_1(&self) -> &[<Ctx as PairingStructure>::G1] {
        &self.ptau_1
    }

    pub fn h0(&self) -> &<Ctx as PairingStructure>::G2 {
        &self.h0
    }

    pub fn h1(&self) -> &<Ctx as PairingStructure>::G2 {
        &self.h1
    }

    pub fn verifying_key(&self) -> KzgVerifyingKey<Ctx> {
        KzgVerifyingKey { tau0: self.ptau_1[0], h0: self.h0, h1: self.h1 }
    }

    pub fn commit(&self, poly: &[<Ctx as PairingStructure>::ScalarField]) -> <Ctx as PairingStructure>::G1 {
        assert!(poly.len() <= self.ptau_1.len(), "Vector is too large.");
        Ctx::msm(&self.ptau_1[..poly.len()], poly)
    }

    /// Given a polynomial, returns a commitment to its quotient by x-pt, and the univariate opening.
    pub fn open(&self, poly: &[<Ctx as PairingStructure>::ScalarField], pt: <Ctx as PairingStructure>::ScalarField) -> (<Ctx as PairingStructure>::G1, <Ctx as PairingStructure>::ScalarField) {
        let (a, b) = div_by_linear(poly, pt);
        (self.commit(&a), b)
    }
}

pub fn random_kzg_pk<Ctx: Pairing>(size: usize, rng: &mut impl Rng) -> KzgProvingKey<Ctx> {
    let tau = <Ctx as PairingStructure>::ScalarField::from(rng.next_u64());
    let g0 = <Ctx as PairingStructure>::G1::from(rng.next_u64());
    let h0 = <Ctx as PairingStructure>::G2::from(rng.next_u64());
    KzgProvingKey::mock_setup(tau, g0, h0, size)
}

pub fn ev<F: PrimeField>(poly : &[F], x: F) -> F {
    let mut power = F::one();
    let mut acc = F::zero();
    for i in 0..poly.len() {
        acc += poly[i]*power;
        power *= x;
    }
    acc
}

#[cfg(test)]
mod tests {
    use ark_bn254::Bn254 as Ctx;
    use ark_bn254::Fr;
    use ark_std::{test_rng, UniformRand};
    use ark_std::rand::Rng;

    use super::*;

    fn random_poly(size: usize, rng: &mut impl Rng) -> Vec<Fr> {
        (0..size).map(|_|Fr::rand(rng)).collect()
    }

    #[test]
    fn quotient() {
        let poly : Vec<Fr> = vec![1, 3, 3, 7, 2, 0, 2, 4].into_iter().map(|x|Fr::from(x)).collect();
        let pt = Fr::from(322);
        let (quotient, remainder) = div_by_linear(&poly, pt);
        assert!(ev(&poly, pt) == remainder);
        assert!(ev(&poly, Fr::from(500)) == ev(&quotient, Fr::from(500)) * (Fr::from(500-322)) + remainder);
    }

    #[test]
    fn poly_open() {
        let rng = &mut test_rng();
        let poly = random_poly(97, rng);
        let srs : KzgProvingKey<Ctx> = random_kzg_pk(128, rng);
        let vkey = srs.verifying_key();

        let opening_at = Fr::rand(rng);

        let poly_commitment = srs.commit(&poly);
        let opening_proof = srs.open(&poly, opening_at);
        let (quotient_commitment, opening) = opening_proof;

        vkey.verify_directly(poly_commitment, quotient_commitment, opening_at, opening);
        vkey.verify_pair(vkey.verify_reduce_to_pair(poly_commitment, quotient_commitment, opening_at, opening));
    }

}