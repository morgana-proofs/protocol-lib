use crate::common::wrapper::{ComputationalField, TFelt};
use crate::transcript::transcript::TArithmeticTranscript;

pub trait CommitmentOpener<F: TFelt, Transcript: TArithmeticTranscript<F>> {
    fn v_open(&self, transcript: &mut Transcript, point: &[F]) -> F;
}

pub trait CommitmentScheme<F: ComputationalField, Transcript: TArithmeticTranscript<F>> {
    fn commit(&mut self, transcript: &mut Transcript, poly: &[F]);
    fn p_open(&self, transcript: &mut Transcript, poly: &[F], point: &[F]) -> F;
}