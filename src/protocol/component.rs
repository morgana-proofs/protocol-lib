pub trait TProtocol<Transcript> {
    type ClaimsBefore;
    type ClaimsAfter;

    fn verify(&self, transcript: &mut Transcript, claims: Self::ClaimsBefore) -> Self::ClaimsAfter;
    fn prove<Prover>(&self, transcript: &mut Transcript, claims: Self::ClaimsBefore, advice: Prover::ProverInput) -> (Self::ClaimsAfter, Prover::ProverOutput) where Prover: TProverImpl<Transcript, Verifier = Self> {
        Prover::_prove(&self, transcript, claims, advice)
    }
}

pub trait TProverImpl<Transcript> {
    type Verifier : TProtocol<Transcript>;
    type ProverInput;
    type ProverOutput;
    fn _prove(protocol: &Self::Verifier, transcript: &mut Transcript, claims: <Self::Verifier as TProtocol<Transcript>>::ClaimsBefore, advice: Self::ProverInput) -> (<Self::Verifier as TProtocol<Transcript>>::ClaimsAfter, Self::ProverOutput);
}