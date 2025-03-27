use std::marker::PhantomData;
use std::ops::Index;
use crate::common::algfn::{AlgFn, AlgFnSO};
use crate::common::wrapper::PolyOps;

#[derive(Clone)]
pub struct EqWrapper<F: PolyOps, Fun: AlgFnSO<F>> {
    f: Fun,
    _pd: PhantomData<F>,
}

impl<F: PolyOps, Fun: AlgFnSO<F>> EqWrapper<F, Fun> {
    pub fn new(f: Fun) -> Self {
        Self {
            f,
            _pd: Default::default(),
        }
    }
}

impl <F: PolyOps, Fun: AlgFnSO<F>> AlgFnSO<F> for EqWrapper<F, Fun> {
    fn exec(&self, args: &impl Index<usize, Output = F>) -> F {
        self.f.exec(args) * args[self.f.n_ins()].clone()
    }

    fn deg(&self) -> usize {
        self.f.deg() + 1
    }

    fn n_ins(&self) -> usize {
        self.f.n_ins() + 1
    }
}

#[derive(Clone)]
pub struct GammaWrapper<F: PolyOps, Fun: AlgFn<F>> {
    f: Fun,
    gamma_pows: Vec<F>,
}

impl<F: PolyOps, Fun: AlgFn<F>> GammaWrapper<F, Fun> {
    pub fn new(f: Fun, gamma: F) -> Self {
        assert!(f.n_outs() > 1);
        let mut gamma_pows = Vec::with_capacity(f.n_outs() - 1);
        gamma_pows.push(gamma.clone());
        for _ in 0..f.n_outs() - 2 {
            let tmp = gamma_pows.last().unwrap();
            gamma_pows.push(gamma.clone() * tmp);
        }

        Self {f, gamma_pows}
    }
}

impl <F: PolyOps, Fun: AlgFn<F>> AlgFnSO<F> for GammaWrapper<F, Fun> {
    fn exec(&self, args: &impl Index<usize, Output = F>) -> F {
        let mut out = self.f.exec(args);
        let mut ret = out.next().unwrap();
        out.zip(self.gamma_pows.iter()).map(|(a, b)| a * b).map(|x| ret = ret.clone() + x.clone()).count();
        ret
    }

    fn deg(&self) -> usize {
        self.f.deg()
    }

    fn n_ins(&self) -> usize {
        self.f.n_ins()
    }
}
