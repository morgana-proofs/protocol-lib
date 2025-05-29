use std::io::{Read, Write};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Compress, SerializationError, Valid, Validate};
use crate::common::wrapper::{ComputationalField, TFelt};

#[derive(Clone, Eq, PartialEq, Debug)]
pub struct SumClaim<F>(pub F);


#[derive(Clone, Eq, PartialEq, Debug)]
pub struct UnivarEvalClaim<F> {
    pub ev: F,
    pub point: F,
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub struct EvalClaim<F> {
    pub ev: F,
    pub point: Vec<F>,
}

impl<F: ComputationalField> CanonicalSerialize for EvalClaim<F> {
    fn serialize_with_mode<W: Write>(&self, mut writer: W, compress: Compress) -> Result<(), SerializationError> {
        self.ev.serialize_with_mode(&mut writer, compress)?;
        self.point.serialize_with_mode(&mut writer, compress)?;
        Ok(())
    }

    fn serialized_size(&self, compress: Compress) -> usize {
        self.ev.serialized_size(compress) + self.point.serialized_size(compress)
    }
}

impl<F: ComputationalField> Valid for EvalClaim<F> {
    fn check(&self) -> Result<(), SerializationError> {
        self.ev.check()?;
        self.point.check()?;
        Ok(())
    }
}

impl<F: ComputationalField> CanonicalDeserialize for EvalClaim<F> {
    fn deserialize_with_mode<R: Read>(mut reader: R, compress: Compress, validate: Validate) -> Result<Self, SerializationError> {
        Ok(Self {
            ev: F::deserialize_with_mode(&mut reader, compress, validate)?,
            point: Vec::<F>::deserialize_with_mode(&mut reader, compress, validate)?,
        })
    }
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub struct SinglePointClaims<F> {
    pub evs: Vec<F>,
    pub point: Vec<F>,
}

impl<F> From<SinglePointClaims<F>> for EvalClaim<F> {
    fn from(mut claims: SinglePointClaims<F>) -> Self {
        assert!(claims.evs.len() == 1);
        EvalClaim{ ev: claims.evs.pop().unwrap(), point: claims.point }
    }
}

impl<F> From<EvalClaim<F>> for SinglePointClaims<F> {
    fn from(claim: EvalClaim<F>) -> Self {
        SinglePointClaims{ evs: vec![claim.ev], point: claim.point }
    }
}

impl<F> From<EvalClaim<F>> for SumClaim<F> {
    fn from(claim: EvalClaim<F>) -> Self {
        assert!(claim.point.len() == 0);
        SumClaim(claim.ev)
    }
}

impl<F> From<SumClaim<F>> for EvalClaim<F> {
    fn from(claim: SumClaim<F>) -> Self {
        EvalClaim{ ev: claim.0, point: vec![] }
    }
}