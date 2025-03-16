use crate::dialects::dialect::TDialectInterface;

pub trait TSupportsVDialect<D: TDialectInterface> : ProtocolComponent {
    fn _verify(&self, transcript: &mut D, claims: Self::ClaimsBefore<D>) -> Self::ClaimsAfter<D>;
}

pub trait TSupportsPDialect<D: TDialectInterface> : ProtocolComponent {
    fn _prove(&self, transcript: &mut D, claims: Self::ClaimsBefore<D>, input: Self::ProverInput<D>) -> (Self::ClaimsAfter<D>, Self::ProverOutput<D>);
}

pub trait ProtocolComponent {
    type ClaimsBefore<Dialect>;
    type ClaimsAfter<Dialect>;
    type ProverInput<Dialect>;
    type ProverOutput<Dialect>;

    fn verify<D>(&self, transcript: &mut D, claims: Self::ClaimsBefore<D>) -> Self::ClaimsAfter<D> where D: TDialectInterface, Self: TSupportsVDialect<D> {
        self._verify(transcript, claims)
    }

    fn prove<D>(&self, transcript: &mut D, claims: Self::ClaimsBefore<D>, input: Self::ProverInput<D>) -> (Self::ClaimsAfter<D>, Self::ProverOutput<D>)
        where D: TDialectInterface, Self: TSupportsPDialect<D>{
        self._prove(transcript, claims, input)
    }
}