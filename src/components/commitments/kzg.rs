// This implements non-hiding KZG commitments (in a form typically used in PlonK, i.e. powers of tau in first group, and
// only a single power of tau in a second group).

// Lagrange form is unimplemented, as we will not need it.

use std::fs::File;
use std::marker::PhantomData;
use ark_bn254::G1Affine;
use ark_ec::{CurveGroup, VariableBaseMSM};
use ark_ec::pairing::Pairing;
use ark_ff::PrimeField;
use ark_std::{One, UniformRand};
use ark_std::rand::Rng;
use rayon::iter::IntoParallelIterator;
use rayon::iter::ParallelIterator;
use crate::common::claims::UnivarEvalClaim;
use crate::common::wrapper::TFelt;
use crate::components::commitments::scheme::{CommitmentMode, CommitmentSchemeMode, OpeningMode, TPairVerifier};
use crate::protocol::component::{TProtocol, TProverImpl};
use crate::transcript::transcript::{TArithmeticTranscript, TTranscriptSupportsIO};

#[derive(Clone)]
pub struct KzgProvingKey<Ctx: Pairing, Mode: CommitmentSchemeMode> {
    ptau_1: Vec<Ctx::G1Affine>,
    h0: Ctx::G2Affine,
    h1: Ctx::G2Affine,
    _pd: PhantomData<Mode>,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct KzgVerifyingKey<Ctx: Pairing, Mode: CommitmentSchemeMode> {
    tau0: Ctx::G1Affine,
    h0: Ctx::G2Affine,
    h1: Ctx::G2Affine,
    _pd: PhantomData<Mode>,
}
impl<Ctx: Pairing, Mode: CommitmentSchemeMode> KzgVerifyingKey<Ctx, Mode> {
    pub(crate) fn commitment(self) -> KzgVerifyingKey<Ctx, CommitmentMode> {
        KzgVerifyingKey {
            tau0: self.tau0,
            h0: self.h0,
            h1: self.h1,
            _pd: Default::default(),
        }
    }
    pub(crate) fn opening(self) -> KzgVerifyingKey<Ctx, OpeningMode> {
        KzgVerifyingKey {
            tau0: self.tau0,
            h0: self.h0,
            h1: self.h1,
            _pd: Default::default(),
        }
    }
}

impl<Ctx: Pairing, Mode: CommitmentSchemeMode> KzgProvingKey<Ctx, Mode> {
    pub(crate) fn commitment(self) -> KzgProvingKey<Ctx, CommitmentMode> {
        KzgProvingKey {
            ptau_1: self.ptau_1,
            h0: self.h0,
            h1: self.h1,
            _pd: Default::default(),
        }
    }
    pub(crate) fn opening(self) -> KzgProvingKey<Ctx, OpeningMode> {
        KzgProvingKey {
            ptau_1: self.ptau_1,
            h0: self.h0,
            h1: self.h1,
            _pd: Default::default(),
        }
    }
}

impl<Ctx: Pairing> KzgVerifyingKey<Ctx, OpeningMode> {

    /// Directly verifies KZG opening proof.
    pub fn verify_directly(
        &self,
        poly_commitment: Ctx::G1,
        quotient_commitment: Ctx::G1,
        opening_at: Ctx::ScalarField,
        opening: Ctx::ScalarField,
    ) {
        assert_eq!(
            Ctx::pairing(Into::<Ctx::G1>::into(poly_commitment) - self.tau0 * opening, self.h0),
            Ctx::pairing(quotient_commitment, Into::<Ctx::G2>::into(self.h1) - self.h0 * opening_at)
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
        ((quotient_commitment * opening_at - self.tau0 * opening + poly_commitment.into()), quotient_commitment)
    }
}

impl<Ctx: Pairing, Mode: CommitmentSchemeMode> TPairVerifier for KzgVerifyingKey<Ctx, Mode> {
    type G1 = Ctx::G1;

    fn verify_pair(&self, a: Self::G1, b: Self::G1) {
        assert_eq!(
            Ctx::pairing(a.into(), self.h0),
            Ctx::pairing(b.into(), self.h1)
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

impl<Ctx: Pairing> KzgProvingKey<Ctx, CommitmentMode> {
    pub fn mock_setup(tau: Ctx::ScalarField, g0: Ctx::G1Affine, h0: Ctx::G2Affine, size: usize) -> Self {
        let mut powers_of_tau = Vec::with_capacity(size);
        let mut p = Ctx::ScalarField::one();
        for _ in 0..size {
            powers_of_tau.push(p);
            p *= tau;
        }

        let h1: Ctx::G2Affine = (h0 * tau).into();

        let ptau1_proj: Vec<Ctx::G1> = powers_of_tau.into_par_iter().map(|sc| g0 * sc).collect();

        Self { ptau_1: Ctx::G1::normalize_batch(&ptau1_proj), h0, h1, _pd: Default::default()}
    }
    pub fn load(file: &mut File) -> Self {
        todo!()
    }
}
impl<Ctx: Pairing, Mode: CommitmentSchemeMode> KzgProvingKey<Ctx, Mode> {


    pub fn dump(&self, file: &mut File) {
        todo!()
    }

    pub fn ptau_1(&self) -> &[Ctx::G1Affine] {
        &self.ptau_1
    }

    pub fn h0(&self) -> &Ctx::G2Affine {
        &self.h0
    }

    pub fn h1(&self) -> &Ctx::G2Affine {
        &self.h1
    }

    pub fn verifying_key(&self) -> KzgVerifyingKey<Ctx, Mode> {
        KzgVerifyingKey { tau0: self.ptau_1[0], h0: self.h0, h1: self.h1, _pd: Default::default() }
    }

    pub fn commit(&self, poly: &[Ctx::ScalarField]) -> Ctx::G1 {
        assert!(poly.len() <= self.ptau_1.len(), "Vector is too large.");
        <Ctx::G1 as VariableBaseMSM>::msm(&self.ptau_1[..poly.len()], poly).unwrap()
    }

    /// Given a polynomial, returns a commitment to its quotient by x-pt, and the univariate opening.
    pub fn open(&self, poly: &[Ctx::ScalarField], pt: Ctx::ScalarField) -> (Ctx::G1, Ctx::ScalarField) {
        let (a, b) = div_by_linear(poly, pt);
        (self.commit(&a), b)
    }
}

pub fn random_kzg_pk<Ctx: Pairing>(size: usize, rng: &mut impl Rng) -> KzgProvingKey<Ctx, CommitmentMode> {
    let tau = <Ctx as Pairing>::ScalarField::rand(rng);
    let g0 = <Ctx as Pairing>::G1Affine::rand(rng);
    let h0 = <Ctx as Pairing>::G2Affine::rand(rng);
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

impl<F: TFelt, Transcript: TArithmeticTranscript<F> + TTranscriptSupportsIO<P::G1>, P: Pairing<ScalarField=F>> TProtocol<Transcript> for KzgVerifyingKey<P, CommitmentMode> {
    type ClaimsBefore = ();
    type ClaimsAfter = <Self as TPairVerifier>::G1;

    fn verify(&self, ctx: &mut Transcript, claims: Self::ClaimsBefore) -> Self::ClaimsAfter {
        ctx.read()
    }
}

impl<F: TFelt, Transcript: TArithmeticTranscript<F> + TTranscriptSupportsIO<P::G1>, P: Pairing<ScalarField=F>> TProtocol<Transcript> for KzgVerifyingKey<P, OpeningMode> {
    type ClaimsBefore = (UnivarEvalClaim<F>, <Self as TPairVerifier>::G1);
    type ClaimsAfter = ();

    fn verify(&self, ctx: &mut Transcript, claims: Self::ClaimsBefore) -> Self::ClaimsAfter {
        let (eval_claim, commitment) = claims;
        let quotient_commitment: <Self as TPairVerifier>::G1 = ctx.read();
        let (left, right) = self.verify_reduce_to_pair(commitment, quotient_commitment, eval_claim.point, eval_claim.ev);
        self.verify_pair(left, right);
    }
}

impl<F: TFelt, Transcript: TArithmeticTranscript<F> + TTranscriptSupportsIO<P::G1>, P: Pairing<ScalarField=F>> TProverImpl<Transcript> for KzgProvingKey<P, OpeningMode> {
    type Verifier = KzgVerifyingKey<P, OpeningMode>;
    type ProverInput = Vec<F>;
    type ProverOutput = ();

    fn prove(&self, ctx: &mut Transcript, claims: <Self::Verifier as TProtocol<Transcript>>::ClaimsBefore, advice: Self::ProverInput) -> (<Self::Verifier as TProtocol<Transcript>>::ClaimsAfter, Self::ProverOutput) {
        let (eval_claim, commitment) = claims;
        let (quotient_commitment, div_eval) = self.open(&advice, eval_claim.ev);
        ctx.write(&quotient_commitment);

        ((),())
    }
}

impl<F: TFelt, Transcript: TArithmeticTranscript<F> + TTranscriptSupportsIO<P::G1>, P: Pairing<ScalarField=F>> TProverImpl<Transcript> for KzgProvingKey<P, CommitmentMode> {
    type Verifier = KzgVerifyingKey<P, CommitmentMode>;
    type ProverInput = Vec<F>;
    type ProverOutput = ();

    fn prove(&self, ctx: &mut Transcript, claims: <Self::Verifier as TProtocol<Transcript>>::ClaimsBefore, advice: Self::ProverInput) -> (<Self::Verifier as TProtocol<Transcript>>::ClaimsAfter, Self::ProverOutput) {
        let commitment = self.commit(&advice);
        ctx.write(&commitment);
        (commitment, ())
    }
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
        let srs : KzgProvingKey<Ctx, _> = random_kzg_pk(128, rng);
        let vkey = srs.verifying_key().opening();

        let opening_at = Fr::rand(rng);

        let poly_commitment = srs.commit(&poly);
        let opening_proof = srs.open(&poly, opening_at);
        let (quotient_commitment, opening) = opening_proof;

        vkey.verify_directly(poly_commitment, quotient_commitment, opening_at, opening);
        let (left, right) = vkey.verify_reduce_to_pair(poly_commitment, quotient_commitment, opening_at, opening);
        vkey.verify_pair(left, right);
    }

}