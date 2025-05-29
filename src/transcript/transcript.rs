// use crate::common::wrapper::{TFelt, TPrimeField};

// use super::board::{Sig, TSupportsFormalArithOps, TSupportsFormalType, TSupportsFormalVTranscript};

use std::thread;
use ark_ec::short_weierstrass::{Affine, SWCurveConfig};
use ark_ff::{BigInteger, PrimeField};
use ark_std::iterable::Iterable;
use merlin::Transcript;
use crate::common::wrapper::{ComputationalField, IOSerialisation, TFelt, TFeltUtil};

// /// Entry point trait that passes through all interesting operations (so they can be conveniently called without fully qualified syntax).
// /// Due to "where" semantics, methods are unavailable unless an actual implementor trait is present.
pub trait TTranscriptInterface {
    /// squeezes new challenge
    fn challenge<F>(&mut self) -> F where Self: TTranscriptSupportsChallenges<F> {
        self._challenge()
    }

    /// reads from transcript (or allocates this operation); fails for prover dialects - they write and do not read
    fn read<F>(&mut self) -> F where Self: TTranscriptSupportsIO<F> {
        self._read()
    }

    /// writes to transcript (or allocates this operation); fails for verifier dialects - they read and do not write
    fn write<F>(&mut self, value: &F) where Self: TTranscriptSupportsIO<F> {
        self._write(value)
    }

    /// same as read, but does not invoke sponge
    fn unconstrained_read<F>(&mut self) -> F where Self: TTranscriptSupportsIO<F> {
        self._unconstrained_read()
    }

    /// same as write, but does not invoke sponge
    fn unconstrained_write<F>(&mut self, value: &F) where Self: TTranscriptSupportsIO<F> {
        self._unconstrained_write(value)
    }
}


// /// Trait for general interactions with transcript. Operations from it are passed to TDialectInterface, because otherwise
// /// we would need fully qualified syntax to run them.
// /// Methods in this trait are generally fallible - prover is unable to use read methods, verifier is unable to use write
// /// methods, and some challenges can be unsupported. This is completely OK and much better than having separate traits for
// /// each of these concepts. 
pub trait TTranscriptSupportsIO<T> {
    /// reads from transcript (or allocates this operation); fails for prover dialects - they write and do not read
    fn _read(&mut self) -> T;
    /// writes to transcript (or allocates this operation); fails for verifier dialects - they read and do not write
    fn _write(&mut self, value: &T);
    /// same as read, but does not invoke sponge
    fn _unconstrained_read(&mut self) -> T;
    /// same as write, but does not invoke sponge
    fn _unconstrained_write(&mut self, value: &T); 
}
pub trait TTranscriptSupportsChallenges<T> {
    /// squeezes new challenge
    fn _challenge(&mut self) -> T;
}
pub trait TTranscriptSupports<T>: TTranscriptSupportsChallenges<T> + TTranscriptSupportsIO<T> {}

// /// A verifier that is capable of field element manipulation
// pub trait TFormalArithmeticDialect<F: TPrimeField>: TDialectInterface + TSupportsFormalType<F> + TSupportsFormalArithOps<F> + TSupportsFormalVTranscript<F> + TTranscriptSupports<Sig<F, Self>>{}

pub trait TArithmeticTranscript<F: TFelt> : TTranscriptInterface + TTranscriptSupports<F> {}

// impl<F: TPrimeField, Dialect: TFormalArithmeticDialect<F>> TArithmeticDialect<Sig<F, Dialect>> for Dialect {}

#[derive(Debug, Eq, PartialEq, Copy, Clone)]
enum ProofTranscriptMode {
    Prover,
    Verifier,
}
pub struct ProofTranscript {
    merlin_transcript: Transcript,
    proof: Option<Vec<u8>>,
    ctr: usize,
    mode: ProofTranscriptMode,
}

impl ProofTranscript {
    pub fn start_prover(sep: &'static[u8]) -> Self {
        let merlin_transcript = Transcript::new(sep);
        let proof = vec![];
        Self { merlin_transcript, proof: Some(proof), ctr: 0, mode: ProofTranscriptMode::Prover }
    }
    pub fn end(mut self) -> Vec<u8> {
        assert_eq!(self.mode, ProofTranscriptMode::Prover);
        self.proof.take().unwrap()
    }
    pub fn start_verifier(sep: &'static[u8], proof: Vec<u8>) -> Self {
        let merlin_transcript = Transcript::new(sep);
        Self { merlin_transcript, proof: Some(proof), ctr: 0, mode: ProofTranscriptMode::Verifier }
    }
}

impl Drop for ProofTranscript {
    fn drop(&mut self) {
        if !thread::panicking() {
            match self.mode {
                ProofTranscriptMode::Prover => {
                    assert!(self.proof.is_none());
                }
                ProofTranscriptMode::Verifier => {
                    assert_eq!(self.ctr, self.proof.as_ref().unwrap().len());
                }
            }
        }
    }
}

impl TTranscriptInterface for ProofTranscript {}

impl <F: ComputationalField> TTranscriptSupportsChallenges<F> for ProofTranscript {
    fn _challenge(&mut self) -> F {
        let mut ret = vec![0u8; F::CHALLENGE_BYTES];
        self.merlin_transcript.challenge_bytes(&[], &mut ret);
        F::deserialize_challenge(&ret)
    }

}

impl<F: IOSerialisation> TTranscriptSupportsIO<F> for ProofTranscript {
    fn _read(&mut self) -> F {
        let bytesize = F::num_bytes();
        match self.mode {
            ProofTranscriptMode::Prover => panic!(),
            ProofTranscriptMode::Verifier => {
                assert!(self.ctr + bytesize <= self.proof.as_ref().unwrap().len(), "Out of bounds");
                let msg = &self.proof.as_ref().unwrap()[self.ctr .. self.ctr + bytesize];
                self.ctr += bytesize;
                self.merlin_transcript.append_message(&[], msg);
                F::deserialize(msg)
            }
        }
    }

    fn _write(&mut self, value: &F) {
        let mult = F::num_bytes();
        let mut writer = Vec::with_capacity(mult);
        value.serialize(&mut writer);
        match self.mode {
            ProofTranscriptMode::Verifier => panic!(),
            ProofTranscriptMode::Prover => {
                self.merlin_transcript.append_message(&[], &writer);
                self.proof.as_mut().unwrap().extend_from_slice(&writer);
            }
        }
    }

    fn _unconstrained_read(&mut self) -> F {
        let bytesize = F::num_bytes();
        match self.mode {
            ProofTranscriptMode::Prover => panic!(),
            ProofTranscriptMode::Verifier => {
                assert!(self.ctr + bytesize <= self.proof.as_ref().unwrap().len(), "Out of bounds");
                let msg = &self.proof.as_ref().unwrap()[self.ctr .. self.ctr + bytesize];
                self.ctr += bytesize;
                F::deserialize(msg)
            }
        }
    }

    fn _unconstrained_write(&mut self, value: &F) {
        let mult = F::num_bytes();
        let mut writer = Vec::with_capacity(mult);
        value.serialize(&mut writer);
        match self.mode {
            ProofTranscriptMode::Verifier => panic!(),
            ProofTranscriptMode::Prover => {
                self.proof.as_mut().unwrap().extend_from_slice(&writer);
            }
        }
    }
}
impl<F: ComputationalField> TTranscriptSupports<F> for ProofTranscript {}

impl<F: ComputationalField> TArithmeticTranscript<F> for ProofTranscript {}


#[cfg(test)]
pub mod tests {
    use crate::common::wrapper::{IOSerialisation, TSigUtil};
    use super::*;
    #[test]
    fn test_serialization() {
        use ark_bn254::Fq as F;
        let mult = F::num_bytes();
        let mut writer = Vec::with_capacity(mult);
        F::zero().serialize(&mut writer);
        assert_eq!(F::deserialize(&writer), F::zero());

        use ark_bn254::Bn254 as Ctx;
        use ark_ec::pairing::Pairing;;
        let mult = <Ctx as Pairing>::G1::num_bytes();

        let mut writer = Vec::with_capacity(mult);
        <Ctx as Pairing>::G1::zero().serialize(&mut writer);
        assert_eq!(<Ctx as Pairing>::G1::deserialize(&writer), <Ctx as Pairing>::G1::zero());
    }
}