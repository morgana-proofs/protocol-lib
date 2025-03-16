use std::ops::Index;

use super::wrapper::PolyOps;

pub trait AlgFnSO<F: PolyOps> : Clone {
    /// Executes function.
    fn exec(&self, args: &impl Index<usize, Output = F>) -> F;
    /// Declares the degree.
    fn deg(&self) -> usize;
    /// Declares the expected number of inputs.
    fn n_ins(&self) -> usize;
}

pub trait AlgFn<F: PolyOps> : Clone {
    /// Executes function
    fn exec(&self, args: &impl Index<usize, Output = F>) -> impl Iterator<Item = F>;
    /// Declares the degree.
    fn deg(&self) -> usize;
    /// Declares the expected number of inputs.
    fn n_ins(&self) -> usize;
    /// Declares the expected number of outputs.
    fn n_outs(&self) -> usize;
}

#[derive(Clone)]
pub struct FoldedAlgFn<F: PolyOps, Fun: AlgFn<F>> {
    f: Fun,
    gamma: F,
}

impl<F: PolyOps, Fun: AlgFn<F>> AlgFnSO<F> for FoldedAlgFn<F, Fun> {
    fn exec(&self, args: &impl Index<usize, Output = F>) -> F {
        let mut gamma_pow = self.gamma.clone();
        let mut it = self.f.exec(args);
        let mut ret = it.next().unwrap();
        while let Some(v) = it.next() {
            ret = ret + v * &gamma_pow;
            gamma_pow = gamma_pow * &self.gamma;
        }
        ret
    }

    fn deg(&self) -> usize {
        self.f.deg()
    }

    fn n_ins(&self) -> usize {
        self.f.n_ins()
    }
}