use std::marker::PhantomData;
use std::ops::Index;
use crate::common::algfn::AlgFnSO;
use crate::common::wrapper::TFelt;

#[derive(Clone)]
pub struct Mul2AlgFn<F> {
    _pd: PhantomData<F>,
}

impl<F> Mul2AlgFn<F> {
    pub fn new() -> Self {
        Self {
            _pd: Default::default(),
        }
    }
}

impl<F: TFelt> AlgFnSO<F> for Mul2AlgFn<F> {
    fn exec(&self, args: &impl Index<usize, Output = F>) -> F {
        args[0] * args[1]
    }

    fn deg(&self) -> usize {
        2
    }

    fn n_ins(&self) -> usize {
        2
    }
}