use std::ops::Mul;
use crate::common::wrapper::{ComputationalField, TFelt, TCurveGrep};
use crate::transcript::transcript::TArithmeticTranscript;

pub trait CommitmentOpener<F: TFelt, Transcript: TArithmeticTranscript<F>> {
    fn v_open(&self, transcript: &mut Transcript, point: &[F]) -> F;
}

pub trait CommitmentScheme {
    type Commitment;
    type ScalarField: ComputationalField;
    fn commit<Transcript: TArithmeticTranscript<Self::ScalarField>>(&mut self, transcript: &mut Transcript, poly: &[Self::ScalarField]) -> Self::Commitment;
}