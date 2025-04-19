use std::marker::PhantomData;
use itertools::Itertools;
use tracing::instrument;
use crate::common::algfn::AlgFnSO;
use crate::common::claims::{EvalClaim, SinglePointClaims, SumClaim};
use crate::common::wrapper::{ComputationalField, TFelt};
use crate::components::sumcheck::dense_eq::DenseSumcheckableSO;
use crate::components::sumcheck::generic::{SumcheckGenericProverImpl, SumcheckProtocol};
use crate::transcript::transcript::TArithmeticTranscript;
use crate::protocol::component::{TProtocol, TProverImpl};

pub struct DenseSumcheck<F: TFelt, Fun: AlgFnSO<F>> {
    f: Fun,
    pub num_vars: usize,
    _pd: PhantomData<F>,
}

impl<F: TFelt, Fun: AlgFnSO<F>> DenseSumcheck<F, Fun> {
    pub fn new(f: Fun, num_vars: usize) -> Self {
        Self {f, num_vars, _pd: PhantomData}
    }
}

impl<F: TFelt, Fun: AlgFnSO<F>, Transcript: TArithmeticTranscript<F>> TProtocol<Transcript> for DenseSumcheck<F, Fun> {
    type ClaimsBefore = SumClaim<F>;
    type ClaimsAfter = SinglePointClaims<F>;

    fn verify(&self, ctx: &mut Transcript, claims: Self::ClaimsBefore) -> Self::ClaimsAfter {
        let generic_protocol_config = SumcheckProtocol::<F, _>::new(self.f.clone(), self.num_vars);

        let EvalClaim {ev, point} = generic_protocol_config.verify(ctx, claims);

        let poly_evs = (0..self.f.n_ins()).map(|_| ctx.read()).collect_vec();

        (self.f.exec(&poly_evs) - ev).require();
        SinglePointClaims {point, evs: poly_evs}
    }
}

impl<F: ComputationalField, Fun: AlgFnSO<F>, Transcript: TArithmeticTranscript<F>> TProverImpl<Transcript> for DenseSumcheck<F, Fun> {
    type Verifier = Self;
    type ProverInput = Vec<Vec<F>>;
    type ProverOutput = ();

    #[instrument(name="DenseSumCheck::prove", level="info", skip_all)]
    fn _prove(protocol: &Self::Verifier, ctx: &mut Transcript, claims: <Self::Verifier as TProtocol<Transcript>>::ClaimsBefore, advice: Self::ProverInput) -> (<Self::Verifier as TProtocol<Transcript>>::ClaimsAfter, Self::ProverOutput) {
        let generic_protocol_config = SumcheckProtocol::new(protocol.f.clone(), protocol.num_vars);

        let so = DenseSumcheckableSO::new(advice, protocol.f.clone(),  protocol.num_vars, claims.0.clone());

        let (EvalClaim {ev, point}, poly_evs) = generic_protocol_config.prove::<SumcheckGenericProverImpl<_, _, _>>(ctx, claims, so);

        poly_evs.iter().for_each(|ev| ctx.write(ev));

        (SinglePointClaims {point, evs: poly_evs}, ())
    }
}


#[cfg(test)]
mod tests {
    use std::ops::Index;
    use super::*;
    use crate::{common::wrapper::TFeltUtil, transcript::transcript::tests::ManualTestTranscript};
    use ark_bn254::Fq as F;
    use ark_std::{test_rng, UniformRand};
    //use num_traits::One;
    use crate::common::math::evaluate_multivar;

    #[derive(Clone, Copy)]
    pub struct TestFunction {}

    impl AlgFnSO<F> for TestFunction {
        fn exec(&self, args: &impl Index<usize, Output = F>) -> F {
            args[0] * args[1] - F::one()
        }

        fn deg(&self) -> usize {
            2
        }

        fn n_ins(&self) -> usize {
            2
        }
    }

    #[test]
    fn dense_sumcheck_with_verifier_accepts_prover() {
        let rng = &mut test_rng();
        let logsize = 6;
        let polys : Vec<Vec<F>> = (0..2).map(|_| (0 .. 1 << logsize).map(|_|F::rand(rng)).collect()).collect();

        let f = TestFunction{};

        let mut output = vec![];

        for i in 0 .. 1 << logsize {
            let args : Vec<F> = polys.iter().map(|poly| poly[i]).collect();
            output.push(f.exec(&args));
        }

        let mut transcript_p = ManualTestTranscript::new((0..1000).map(|_| F::rand(rng)).collect_vec());

        let claim = SumClaim(output.iter().sum());
        let sumcheck = DenseSumcheck::new(f, logsize);
        let (output_claims, _) = sumcheck.prove::<DenseSumcheck<_,_,>>(&mut transcript_p, claim.clone(), polys.clone());
        let _proof = transcript_p.end();
        let mut transcript_v = transcript_p;

        let expected_output_claims = sumcheck.verify(&mut transcript_v, claim);
        assert_eq!(output_claims, expected_output_claims);

        let SinglePointClaims { point : new_point, evs } = output_claims;
        assert_eq!(polys.iter().map(|poly| evaluate_multivar(poly, &new_point)).collect_vec(), evs);
    }
}