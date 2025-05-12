use crate::common::claims::EvalClaim;
use crate::common::wrapper::{ComputationalField, TFelt, TGroup};
use crate::protocol::component::{TProtocol, TProverImpl};
use crate::transcript::transcript::TArithmeticTranscript;


#[derive(Copy, Clone)]
pub struct OpeningMode {}

#[derive(Copy, Clone)]
pub struct CommitmentMode {}
pub trait CommitmentSchemeMode: Sized + Send + Sync + Clone + 'static {}
impl CommitmentSchemeMode for CommitmentMode {}
impl CommitmentSchemeMode for OpeningMode {}

pub trait TCommitmentEngineVerifier: Clone {
    fn opening(self) -> impl TCommitmentEngineVerifier;
    fn commitment(self) -> impl TCommitmentEngineVerifier;
}

pub trait TCommitmentEngineProver: Clone {
    type Verifier: TCommitmentEngineVerifier;
    fn verifier(&self) -> Self::Verifier;
    fn opening(self) -> impl TCommitmentEngineProver;
    fn commitment(self) -> impl TCommitmentEngineProver;
}

pub trait TPairVerifier {
    type G1: TGroup;
    fn verify_pair(&self, a: Self::G1, b: Self::G1);
}
