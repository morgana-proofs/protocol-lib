pub trait TProtocol<Dialect> {
    type ClaimsBefore;
    type ClaimsAfter;

    fn verify(&self, ctx: &mut Dialect, claims: Self::ClaimsBefore) -> Self::ClaimsAfter;
}

pub trait TProverImpl<Dialect> {
    type Verifier : TProtocol<Dialect>;
    type ProverInput;
    type ProverOutput;
    fn prove(&self, ctx: &mut Dialect, claims: <Self::Verifier as TProtocol<Dialect>>::ClaimsBefore, advice: Self::ProverInput) -> (<Self::Verifier as TProtocol<Dialect>>::ClaimsAfter, Self::ProverOutput);
}