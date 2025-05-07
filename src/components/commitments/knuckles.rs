use std::fs::File;

use ark_ec::pairing::Pairing;
use ark_ff::{batch_inversion, Field};


use crate::components::commitments::kzg::ev;
use rayon::prelude::*;

use super::kzg::{KzgProvingKey, KzgVerifyingKey};
use ark_std::{Zero, One};
use crate::common::wrapper::{ComputationalField, TFelt};
use crate::transcript::transcript::{TArithmeticTranscript, TTranscriptSupportsIO};

#[derive(Clone)]
pub struct KnucklesProvingKey<Ctx: Pairing> {
    pub kzg_pk: KzgProvingKey<Ctx>,
    pub num_vars: usize, // N = 2^num_vars, kzg_pk must have size at least 2N.
    pub k: Ctx::ScalarField, // Taking k = 2 should work in most cases.
    pub inverses: Vec<Ctx::ScalarField> // Precomputed inverses of (k^s - k^N), except for s = N (where it can be anything).
}

#[derive(Clone)]
pub struct KnucklesProof<Ctx: Pairing> {
    pub t_comm: Ctx::G1Affine,
    pub t_x: Ctx::ScalarField,
    pub p_x: Ctx::ScalarField,
    pub p_lt_x_proof: Ctx::G1Affine,
    pub t_kx: Ctx::ScalarField,
    pub t_kx_proof: Ctx::G1Affine,

}

impl<Ctx: Pairing> KnucklesProvingKey<Ctx> {
    pub fn new(kzg_pk: KzgProvingKey<Ctx>, num_vars: usize, k: Ctx::ScalarField) -> Self {
        let n = 1 << num_vars;
        assert!(kzg_pk.ptau_1().len() >= 2 * n - 1, "SRS is too short.");
        let mut k_pows = Vec::<Ctx::ScalarField>::with_capacity(2 * n - 1);
        let mut power = Ctx::ScalarField::one();
        for _ in 0..2 * n - 1 {
            k_pows.push(power);
            power *= k;
        };
        let k_n = k_pows[n -1];

        (&mut k_pows).par_iter_mut().map(|x| *x -= k_n ).count();
        k_pows[n - 1] += Ctx::ScalarField::one(); // so inversion doesn't fail
        batch_inversion(&mut k_pows);

        Self { kzg_pk, num_vars, k, inverses: k_pows }
    }

    pub fn num_vars(&self) -> usize {
        self.num_vars
    }

    pub fn load(file: &mut File) -> Self {
        todo!()
    }

    pub fn dump(&self, file: &mut File) {
        todo!()
    }

    pub fn verifying_key(&self) -> KnucklesVerifyingKey<Ctx> {
        let kzg_vk = self.kzg_pk.verifying_key();
        KnucklesVerifyingKey { kzg_vk, num_vars: self.num_vars, k: self.k }
    }

    pub fn commit(&self, poly: &[Ctx::ScalarField]) -> Ctx::G1Affine {
        assert!(poly.len() <= 1 << self.num_vars);
        self.kzg_pk.commit(poly)
    }

    pub fn kzg_basis(&self) -> &[Ctx::G1Affine] {
        self.kzg_pk.ptau_1()
    }

    /// Returns polynomial T and an opening c, such that T(kx) - k^{N-1}T(x) + c = P(x)E_r(x)
    /// This equation then can be checked by normal KZG means.
    pub fn compute_t(&self, poly: &[Ctx::ScalarField], point: &[Ctx::ScalarField]) -> (Vec<Ctx::ScalarField>, Ctx::ScalarField) {
        assert_eq!(point.len(), self.num_vars);

        let mut pt = point.to_vec();

        let n = 1 << self.num_vars;
        assert!(poly.len() <= n);

        let mut t : Vec<Ctx::ScalarField> = Vec::with_capacity(2 * n - 1);
        let mut t_scaled = vec![Ctx::ScalarField::zero(); 2 * n - 1];

        let pt_rev : Vec<_> = pt.par_iter().map(|x| Ctx::ScalarField::one() - *x).collect();
        // It is more convenient to multiply by 1-pt.

        t.extend(poly.iter().map(|x| *x).chain(std::iter::repeat(Ctx::ScalarField::zero())).take(2 * n - 1));

        let mut curr_size = n; // This will hold the size of our data
        for i in 0..self.num_vars {
            t_scaled[0..curr_size]
                .par_iter_mut()
                .enumerate()
                .map(|(idx, x)| *x = t[idx] * pt_rev[i]).count();

            let offset = 1 << i;
            curr_size += offset;
            t[0..curr_size].par_iter_mut().enumerate().map(|(idx, x)| {
                if idx < offset {
                    *x -= t_scaled[idx]; // x -= x*pt_rev[i], which is x -= (1-pt[i])x, which is x = pt[i] x
                } else {
                    *x -= t_scaled[idx];
                    *x += t_scaled[idx - offset];
                }
            }).count();
        }

        let opening = t[n - 1];
        t[n - 1] = Ctx::ScalarField::zero();

        t.par_iter_mut()
            .enumerate()
            .map(|(idx, x)| *x *= self.inverses[idx]).count();
        (t, opening)
    }

    /// Creates Knuckles proof. Takes as an input a polynomial, a point to open, and an opening.
    /// All three must be already committed to the transcript, or derived deterministically from other
    /// prover messages. (we do not add them to transcript manually to accomodate for possibility
    /// of the commitment being derived as linear combination of other commitments).
    /// This is somewhat similar to our protocol API, with commitment having a role of a "claim",
    /// though we do not implement it for now.
    pub fn prove<
        Transcript: TArithmeticTranscript<Ctx::ScalarField> + TTranscriptSupportsIO<Ctx::G1Affine>,
    >(
        &self,
        poly: &[Ctx::ScalarField],
        point: &[Ctx::ScalarField],
        claimed_opening: Ctx::ScalarField,
        transcript: &mut Transcript,
    ) -> KnucklesProof<Ctx> {
        let a = self.compute_t(poly, point);
        let (t, opening) = a;
        assert!(opening == claimed_opening, "Incorrect opening claim.");
        let t_comm = self.kzg_pk.commit(&t);
        transcript.write(&t_comm);
        let x = transcript.challenge();

        let kx = x * self.k;
        let t_x = ev(&t, x);
        let p_x = ev(&poly, x);

        transcript.write(&t_x);
        transcript.write(&p_x);

        let lambda: Ctx::ScalarField = transcript.challenge();

        let poly_iter_padded = poly
            .par_iter()
            .map(|x|*x)
            .chain(
                rayon::iter::repeat(Ctx::ScalarField::zero()).take(t.len()-poly.len())
            );

        let p_lt : Vec<_> = poly_iter_padded
            .zip(t.par_iter())
            .map(|(a, b)| lambda * b + a)
            .collect();

        let (p_lt_x_proof, _) = self.kzg_pk.open(&p_lt, x);
        transcript.write(&p_lt_x_proof); // probably unnecessary. will do it anyway

        let (t_kx_proof, t_kx) = self.kzg_pk.open(&t, kx);

        transcript.write(&t_kx);
        transcript.write(&t_kx_proof);

        // We are adding these challenges to transcript so that verifier can sample randomness for
        // proof combination for it. (otherwise, it would not be necessary, as we are not making new claims
        // - but if we want verifier's randomness for final check to be deterministic, it should be done).

        let _: Ctx::ScalarField = transcript.challenge();

        KnucklesProof{ t_comm, t_x, p_x, p_lt_x_proof, t_kx, t_kx_proof }

    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct KnucklesVerifyingKey<Ctx: Pairing> {
    pub kzg_vk: KzgVerifyingKey<Ctx>,
    pub num_vars: usize,
    pub k: Ctx::ScalarField,
}

impl<Ctx: Pairing> KnucklesVerifyingKey<Ctx> {

    /// Reduces a proof to deferred pair (a, b), allegedly satisfying <a, h0> == <b, h1>.
    /// poly_comm, point and opening MUST already be in transcript (they are not added
    /// to give user opportunity to derive them deterministically from other components of the protocol).
    /// This is in line with our general convention of ClaimsToReduce being added to transcript outside
    /// of the function.
    pub fn verify_reduce_to_pair<
        Transcript: TArithmeticTranscript<Ctx::ScalarField> + TTranscriptSupportsIO<Ctx::G1Affine>
    > (
        &self,
        poly_comm: Ctx::G1Affine,
        point: &[Ctx::ScalarField],
        claimed_opening: Ctx::ScalarField,
        transcript: &mut Transcript,
    ) -> (Ctx::G1Affine, Ctx::G1Affine) {
        let t_comm: Ctx::G1Affine = transcript.read();
        let x: Ctx::ScalarField = transcript.challenge();

        let kx = x * self.k;
        let t_x: Ctx::ScalarField = transcript.read();
        let p_x: Ctx::ScalarField = transcript.read();
        let lambda: Ctx::ScalarField = transcript.challenge();

        let p_lt_comm = t_comm * lambda + poly_comm;
        let p_lt_open = t_x * lambda + p_x;

        let p_lt_x_proof: Ctx::G1Affine = transcript.read();

        let (a0, b0) = self.kzg_vk.verify_reduce_to_pair(p_lt_comm, p_lt_x_proof, x, p_lt_open);

        let t_kx: Ctx::ScalarField = transcript.read();
        let t_kx_proof: Ctx::G1Affine = transcript.read();

        let (a1, b1) = self.kzg_vk.verify_reduce_to_pair(t_comm, t_kx_proof, kx, t_kx);


        let k_pow_n_1 = self.k.pow([(1 << self.num_vars) - 1]); // Can  be precomputed if necessary.

        let mut xpow = x;
        let eq_ev = (0..self.num_vars).map(|i| {
            let r = point[i];
            let ret = r + (Ctx::ScalarField::one() - r) * xpow;
            xpow *= xpow;
            ret
        }).fold(Ctx::ScalarField::one(), |a, b| a*b);

        let x_pow_n = xpow;

        let lhs = x * (t_kx - k_pow_n_1 * t_x) + x_pow_n * claimed_opening; // x(T(kx) - k^{N-1} T(x) + x^{N-1} * claim)

        let rhs = x * p_x * eq_ev; // x * P(x) Eq_point (x)


        assert!(lhs == rhs);

        let fin: Ctx::ScalarField = transcript.challenge();

        ((a0 + a1 * fin).into(), (b0 + b1 * fin).into())

    }

    pub fn verify_directly<
        Transcript: TArithmeticTranscript<Ctx::ScalarField> + TTranscriptSupportsIO<Ctx::G1Affine>
    > (
        &self,
        poly_comm: Ctx::G1Affine,
        point: &[Ctx::ScalarField],
        claimed_opening: Ctx::ScalarField,
        transcript: &mut Transcript,
    ) -> () {
        let pair = self.verify_reduce_to_pair(poly_comm, point, claimed_opening, transcript);
        self.kzg_vk.verify_pair(pair);
    }
}





#[cfg(test)]
mod tests {
    use std::iter::repeat_with;

    use ark_bn254::Bn254 as Ctx;
    use ark_bn254::Fr;
    use ark_std::{test_rng, UniformRand};
    use crate::common::math::{evaluate_multivar, evaluate_univar};
    use crate::components::commitments::kzg::{ev, random_kzg_pk};
    use crate::components::commitments::kzg::KzgProvingKey;
    use crate::transcript::transcript::{ProofTranscript, TTranscriptInterface};
    use super::*;

    #[test]
    fn knuckles_prove_and_verify () {
        let rng = &mut test_rng();
        let k = Fr::from(2);
        let num_vars = 10;
        let N = 1 << num_vars;
        let kzg_pk : KzgProvingKey<Ctx>  = random_kzg_pk(2*N - 1, rng);
        let knuckles_pk = KnucklesProvingKey::new(kzg_pk, num_vars, k);

        let poly : Vec<_> = repeat_with(||Fr::rand(rng)).take(1 << num_vars).collect();
        let point : Vec<_> = repeat_with(||Fr::rand(rng)).take(num_vars).collect();

        let (t, opening) = knuckles_pk.compute_t(&poly, &point);

        assert_eq!(evaluate_multivar(&poly, &point), opening, "evaluate_multivar(&poly, &point) == opening"); // Check that opening is correct.


        let mut p_transcript = ProofTranscript::start_prover(b"test knuckles") ;
        let poly_comm = knuckles_pk.commit(&poly);
        p_transcript.write(&poly_comm);
        p_transcript.write(&opening);

        let proof = knuckles_pk.prove(&poly, &point, opening, &mut p_transcript);

        let proof = p_transcript.end();

        let knuckles_vk = knuckles_pk.verifying_key();

        let mut v_transcript = ProofTranscript::start_verifier(b"test knuckles", proof) ;
        let v_poly_comm: <Ctx as Pairing>::G1Affine = v_transcript.read();
        assert_eq!(v_poly_comm, poly_comm);
        let v_opening: <Ctx as Pairing>::ScalarField = v_transcript.read();
        assert_eq!(v_opening, opening);

        knuckles_vk.verify_directly(poly_comm, &point, opening, &mut v_transcript);

    }

}