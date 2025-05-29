use std::marker::PhantomData;
use itertools::Itertools;
use tracing::instrument;
use crate::common::algfn::AlgFnSO;
use crate::common::claims::{EvalClaim, SinglePointClaims, SumClaim};
use crate::common::wrapper::{ComputationalField, TFelt, TSigUtil};
use crate::components::sumcheck::dense_eq::DenseSumcheckableSO;
use crate::components::sumcheck::generic::{SumcheckGenericProverImpl, SumcheckOutput, SumcheckProtocol};
use crate::transcript::transcript::TArithmeticTranscript;
use crate::protocol::component::{TProtocol, TProverImpl};

pub struct DenseSumcheck<F: TFelt, Fun: AlgFnSO<F>> {
    f: Fun,
    pub num_vars: usize,
    pub num_rounds: usize,
    _pd: PhantomData<F>,
}

impl<F: TFelt, Fun: AlgFnSO<F>> DenseSumcheck<F, Fun> {
    pub fn new(f: Fun, num_vars: usize) -> Self {
        Self::new_partial(f, num_vars, num_vars)
    }
    pub fn new_partial(f: Fun, num_vars: usize, num_rounds: usize) -> Self {
        Self {f, num_vars, num_rounds, _pd: PhantomData}
    }
}

impl<F: TFelt, Fun: AlgFnSO<F>, Transcript: TArithmeticTranscript<F>> TProtocol<Transcript> for DenseSumcheck<F, Fun> {
    type ClaimsBefore = EvalClaim<F>;
    type ClaimsAfter = SinglePointClaims<F>;

    fn verify(&self, ctx: &mut Transcript, claims: Self::ClaimsBefore) -> Self::ClaimsAfter {
        let generic_protocol_config = SumcheckProtocol::<F, _>::new(self.f.clone(), self.num_vars);

        let EvalClaim {ev, point} = generic_protocol_config.verify(ctx, claims);

        let poly_evs = (0..self.f.n_ins()).map(|_| ctx.read()).collect_vec();

        (self.f.exec(&poly_evs) - ev).require();
        SinglePointClaims {point, evs: poly_evs}
    }
}

impl<F: ComputationalField, Fun: AlgFnSO<F>, Transcript: TArithmeticTranscript<F>> TProverImpl<Transcript> for DenseSumcheck<F, Fun> where <F as TSigUtil>::Constants: From<u64>  {
    type Verifier = Self;
    type ProverInput = Vec<Vec<F>>;
    type ProverOutput = ();

    #[instrument(name="DenseSumCheck::prove", level="info", skip_all)]
    fn prove(&self, ctx: &mut Transcript, claims: <Self::Verifier as TProtocol<Transcript>>::ClaimsBefore, advice: Self::ProverInput) -> (<Self::Verifier as TProtocol<Transcript>>::ClaimsAfter, Self::ProverOutput) {
        let generic_protocol_config = SumcheckGenericProverImpl::new_partial(self.f.clone(), self.num_vars, self.num_rounds);

        let so = DenseSumcheckableSO::new(advice, self.f.clone(),  self.num_vars, claims.ev.clone());

        let (EvalClaim {ev, point}, poly_evs) = generic_protocol_config.prove(ctx, claims, so);
        let SumcheckOutput::Final(poly_evs) = poly_evs else { unreachable!() };

        poly_evs.iter().for_each(|ev| ctx.write(ev));

        (SinglePointClaims {point, evs: poly_evs}, ())
    }
}


#[cfg(test)]
mod tests {
    use std::ops::Index;
    use super::*;
    use crate::common::wrapper::TFeltUtil;
    use ark_bn254::Fq as F;
    use ark_std::{test_rng, UniformRand};
    //use num_traits::One;
    use crate::common::math::evaluate_multivar;
    use crate::transcript::transcript::ProofTranscript;

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

        let mut transcript_p = ProofTranscript::start_prover(b"test");

        let claim = SumClaim(output.iter().sum());
        let sumcheck = DenseSumcheck::new(f, logsize);
        let (output_claims, _) = sumcheck.prove(&mut transcript_p, claim.clone().into(), polys.clone());
        let proof = transcript_p.end();
        let mut transcript_v = ProofTranscript::start_verifier(b"test", proof);

        let expected_output_claims = sumcheck.verify(&mut transcript_v, claim.into());
        assert_eq!(output_claims, expected_output_claims);

        let SinglePointClaims { point : new_point, evs } = output_claims;
        assert_eq!(polys.iter().map(|poly| evaluate_multivar(poly, &new_point)).collect_vec(), evs);
    }
}