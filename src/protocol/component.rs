pub trait TProtocol<Dialect> {
    type ClaimsBefore;
    type ClaimsAfter;

    fn verify(&self, ctx: &mut Dialect, claims: Self::ClaimsBefore) -> Self::ClaimsAfter;
    fn prove<Prover>(&self, ctx: &mut Dialect, claims: Self::ClaimsBefore, advice: Prover::ProverInput) -> (Self::ClaimsAfter, Prover::ProverOutput) where Prover: TProverImpl<Dialect, Verifier = Self> {
        Prover::_prove(&self, ctx, claims, advice)
    }
}

pub trait TProverImpl<Dialect> {
    type Verifier : TProtocol<Dialect>;
    type ProverInput;
    type ProverOutput;
    fn _prove(protocol: &Self::Verifier, ctx: &mut Dialect, claims: <Self::Verifier as TProtocol<Dialect>>::ClaimsBefore, advice: Self::ProverInput) -> (<Self::Verifier as TProtocol<Dialect>>::ClaimsAfter, Self::ProverOutput);
}