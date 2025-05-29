use std::marker::PhantomData;
use std::ops::Index;
use itertools::Itertools;
use crate::common::algfn::{AlgFn, AlgFnSO};
use crate::common::wrapper::TFelt;

#[derive(Clone)]
pub struct EqWrapper<F: TFelt, Fun: AlgFnSO<F>> {
    f: Fun,
    _pd: PhantomData<F>,
}

impl<F: TFelt, Fun: AlgFnSO<F>> EqWrapper<F, Fun> {
    pub fn new(f: Fun) -> Self {
        Self {
            f,
            _pd: Default::default(),
        }
    }
}

impl <F: TFelt, Fun: AlgFnSO<F>> AlgFnSO<F> for EqWrapper<F, Fun> {
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
pub struct GammaWrapper<F: TFelt, Fun: AlgFn<F>> {
    f: Fun,
    gamma_pows: Vec<F>,
}

impl<F: TFelt, Fun: AlgFn<F>> GammaWrapper<F, Fun> {
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

impl <F: TFelt, Fun: AlgFn<F>> AlgFnSO<F> for GammaWrapper<F, Fun> {
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

struct OffsetIndexer<'a, F: TFelt, T: Index<usize, Output=F>> {
    index: &'a T,
    offset: usize,
}

impl<'a, F: TFelt, T: Index<usize, Output=F>> OffsetIndexer<'a, F, T> {
    fn new(index: &'a T, offset: usize) -> Self {
        Self { offset, index }
    }
}

impl<'a, F: TFelt, T: Index<usize, Output=F>> Index<usize> for OffsetIndexer<'a, F, T> {
    type Output = F;

    fn index(&self, index: usize) -> &Self::Output {
        self.index.index(index + self.offset)
    }
}


#[derive(Clone)]
pub struct RepeatedAlgFn<F: TFelt, Fun: AlgFn<F>> {
    fun: Fun,
    count: usize,
    _pd: PhantomData<F>
}

impl<F: TFelt, Fun: AlgFn<F>> RepeatedAlgFn<F, Fun> {
    pub fn new(fun: Fun, count: usize) -> Self {
        Self { fun, count, _pd: Default::default() }
    }
}

impl<F: TFelt, Fun: AlgFn<F>> AlgFn<F> for RepeatedAlgFn<F, Fun> {
    fn exec(&self, args: &impl Index<usize, Output=F>) -> impl Iterator<Item=F> {
        (0..self.count)
            .map(|i|
                self.fun.exec(&OffsetIndexer::new(args, i * self.fun.n_ins())).collect_vec()
            )
            .flatten()
    }

    fn deg(&self) -> usize {
        self.fun.deg()
    }

    fn n_ins(&self) -> usize {
        self.fun.n_ins() * self.count
    }

    fn n_outs(&self) -> usize {
        self.fun.n_outs() * self.count
    }
}

#[derive(Clone)]
pub struct StackedAlgFn<F: TFelt, Fun1: AlgFn<F>, Fun2: AlgFn<F>> {
    fun1: Fun1,
    fun2: Fun2,
    _pd: PhantomData<F>
}

impl<F: TFelt, Fun1: AlgFn<F>, Fun2: AlgFn<F>> StackedAlgFn<F, Fun1, Fun2> {
    pub fn new(fun1: Fun1, fun2: Fun2) -> Self {
        Self { fun1, fun2, _pd: Default::default() }
    }
}
impl<F: TFelt, Fun1: AlgFn<F>, Fun2: AlgFn<F>> AlgFn<F> for StackedAlgFn<F, Fun1, Fun2> {
    fn exec(&self, args: &impl Index<usize, Output=F>) -> impl Iterator<Item=F> {
        self.fun1.exec(args).chain(self.fun2.exec(&OffsetIndexer::new(args, self.fun1.n_ins())).collect_vec().into_iter())
    }

    fn deg(&self) -> usize {
        self.fun1.deg().max(self.fun2.deg())
    }

    fn n_ins(&self) -> usize {
        self.fun1.n_ins() + self.fun2.n_ins()
    }

    fn n_outs(&self) -> usize {
        self.fun1.n_outs() + self.fun2.n_outs()
    }
}

#[derive(Clone)]
pub struct RLCAlgFn<F: TFelt, Fun: AlgFnSO<F>> {
    f: Fun,
    pub size: usize,
    pub coeffs: Vec<F>,
}

impl<F: TFelt, Fun: AlgFnSO<F>> RLCAlgFn<F, Fun> {
    pub fn new(f: Fun) -> Self {
        Self {
            f,
            size: 1,
            coeffs: vec![],
        }
    }

    pub fn extend(&mut self, coeff: F) {
        self.size += 1;
        self.coeffs.push(coeff);
    }
}

impl<F: TFelt, Fun: AlgFnSO<F>> AlgFnSO<F> for RLCAlgFn<F, Fun> {
    fn exec(&self, args: &impl Index<usize, Output=F>) -> F {
        let mut val = self.f.exec(&OffsetIndexer::new(args, 0));
        for (i, coeff) in self.coeffs.iter().enumerate() {
            val += self.f.exec(&OffsetIndexer::new(args, self.f.n_ins() * (i + 1))) * coeff;
        }
        val
    }

    fn deg(&self) -> usize {
        self.f.deg()
    }

    fn n_ins(&self) -> usize {
        self.f.n_ins() * self.size
    }
}


#[cfg(test)]
mod tests {
    use super::*;
    use ark_bn254::Fq as F;
    use ark_ff::Field;
    use ark_std::{test_rng, UniformRand};
    use itertools::Itertools;
    use num_traits::One;

    #[derive(Clone, Copy)]
    pub struct TestFunction {}

    impl AlgFn<F> for TestFunction {
        fn exec(&self, args: &impl Index<usize, Output = F>) -> impl Iterator<Item = F> {
            [args[0] * args[1] - F::one(), args[0]*args[2], (args[0] + args[2]).pow([4]), (args[1] - F::one()).pow([3])].into_iter()
        }

        fn deg(&self) -> usize {
            4
        }

        fn n_ins(&self) -> usize {
            3
        }

        fn n_outs(&self) -> usize {
            4
        }
    }
    #[test]
    fn gamma_wrapper_works() {
        let f = TestFunction{};
        let rng = &mut test_rng();
        let input = (0..3).map(|_| F::rand(rng)).collect_vec();
        let gamma = F::rand(rng);
        let output = f.exec(&input);
        let f_folded = GammaWrapper::new(f, gamma);
        let folded_output = f_folded.exec(&input);
        let expected_folded_output = output.enumerate().map(|(i, x)| gamma.pow([i as u64]) * x).sum::<F>();

        assert_eq!(folded_output, expected_folded_output);
    }

}