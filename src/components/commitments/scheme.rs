use crate::common::claims::EvalClaim;
use crate::common::wrapper::{ComputationalField, TFelt, TGroup};
use crate::transcript::transcript::TArithmeticTranscript;


pub struct OpeningMode {}
pub struct CommitmentMode {}
pub trait CommitmentSchemeMode: Sized + Send + Sync + 'static {}
impl CommitmentSchemeMode for CommitmentMode {}
impl CommitmentSchemeMode for OpeningMode {}

pub trait TPairVerifier {
    type G1: TGroup;
    fn verify_pair(&self, a: Self::G1, b: Self::G1);
}
