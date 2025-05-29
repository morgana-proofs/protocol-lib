use crate::common::claims::EvalClaim;
use crate::common::wrapper::{ComputationalField, IOSerialisation, TFelt, TGroup};
use crate::protocol::component::{TProtocol, TProverImpl};
use crate::transcript::transcript::{TArithmeticTranscript, TTranscriptSupportsIO};
use ark_ec::pairing::Pairing;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};

pub trait TCommitmentEngineVerifier<
    F: TFelt,
>: Clone {
    type Commitment: IOSerialisation;
    type Claim;
    type MultiCommitment: IOSerialisation;
    type MultiClaim;
    type MultiConfig;
    fn open<
        Transcript: TArithmeticTranscript<F>
        + TTranscriptSupportsIO<Self::Commitment>
        + TTranscriptSupportsIO<Self::MultiCommitment>,
    >(&self, ctx: &mut Transcript, commitment: Self::Commitment, claim: Self::Claim) -> ();
    fn commit<
        Transcript: TArithmeticTranscript<F>
        + TTranscriptSupportsIO<Self::Commitment>
        + TTranscriptSupportsIO<Self::MultiCommitment>,
    >(&self, ctx: &mut Transcript) -> Self::Commitment;
    fn multi_open<
        Transcript: TArithmeticTranscript<F>
        + TTranscriptSupportsIO<Self::Commitment>
        + TTranscriptSupportsIO<Self::MultiCommitment>,
    >(&self, ctx: &mut Transcript, commitment: Self::MultiCommitment, claim: Self::MultiClaim, cfg: Self::MultiConfig) -> ();
    fn multi_commit<
        Transcript: TArithmeticTranscript<F>
        + TTranscriptSupportsIO<Self::Commitment>
        + TTranscriptSupportsIO<Self::MultiCommitment>,
    >(&self, ctx: &mut Transcript, cfg: Self::MultiConfig) -> Self::MultiCommitment;
}

pub trait TCommitmentEngineProver<
    F: ComputationalField,
>: Clone
{
    type Verifier: TCommitmentEngineVerifier<F>;
    type OpeneingAdvice;
    type MultiOpeneingAdvice;
    type CommitmentAdvice;
    type MultiCommitmentAdvice;
    fn verifier(&self) -> Self::Verifier;

    fn open<
        Transcript: TArithmeticTranscript<F>
        + TTranscriptSupportsIO<<Self::Verifier as TCommitmentEngineVerifier<F>>::Commitment>
        + TTranscriptSupportsIO<<Self::Verifier as TCommitmentEngineVerifier<F>>::MultiCommitment>,
    >(&self, ctx: &mut Transcript, commitment: <Self::Verifier as TCommitmentEngineVerifier<F>>::Commitment, claim: <Self::Verifier as TCommitmentEngineVerifier<F>>::Claim, advice: Self::OpeneingAdvice) -> ();
    fn commit<
        Transcript: TArithmeticTranscript<F>
        + TTranscriptSupportsIO<<Self::Verifier as TCommitmentEngineVerifier<F>>::Commitment>
        + TTranscriptSupportsIO<<Self::Verifier as TCommitmentEngineVerifier<F>>::MultiCommitment>,
    >(&self, ctx: &mut Transcript, advice: Self::CommitmentAdvice) -> <Self::Verifier as TCommitmentEngineVerifier<F>>::Commitment;
    fn multi_open<
        Transcript: TArithmeticTranscript<F>
        + TTranscriptSupportsIO<<Self::Verifier as TCommitmentEngineVerifier<F>>::Commitment>
        + TTranscriptSupportsIO<<Self::Verifier as TCommitmentEngineVerifier<F>>::MultiCommitment>,
    >(&self, ctx: &mut Transcript, commitment: <Self::Verifier as TCommitmentEngineVerifier<F>>::MultiCommitment, claim: <Self::Verifier as TCommitmentEngineVerifier<F>>::MultiClaim, advice: Self::MultiOpeneingAdvice, cfg: <Self::Verifier as TCommitmentEngineVerifier<F>>::MultiConfig) -> ();
    fn multi_commit<
        Transcript: TArithmeticTranscript<F>
        + TTranscriptSupportsIO<<Self::Verifier as TCommitmentEngineVerifier<F>>::Commitment>
        + TTranscriptSupportsIO<<Self::Verifier as TCommitmentEngineVerifier<F>>::MultiCommitment>,
    >(&self, ctx: &mut Transcript, advice: Self::MultiCommitmentAdvice, cfg: <Self::Verifier as TCommitmentEngineVerifier<F>>::MultiConfig) -> <Self::Verifier as TCommitmentEngineVerifier<F>>::MultiCommitment;
}

pub trait TPairVerifier {
    type G1: TGroup;
    fn verify_pair(&self, a: Self::G1, b: Self::G1);
}