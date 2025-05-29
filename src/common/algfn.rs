use std::marker::PhantomData;
use std::ops::Index;
use itertools::Itertools;
use crate::components::vspark::sqrt_vspark::VsparkFinalProd;
use super::wrapper::{TFelt, TSigUtil};

pub trait AlgFnSO<F: TFelt> : Clone {
    /// Executes function.
    fn exec(&self, args: &impl Index<usize, Output = F>) -> F;
    /// Declares the degree.
    fn deg(&self) -> usize;
    /// Declares the expected number of inputs.
    fn n_ins(&self) -> usize;
}

pub trait AlgFn<F: TFelt> : Clone {
    /// Executes function
    fn exec(&self, args: &impl Index<usize, Output = F>) -> impl Iterator<Item = F>;
    /// Declares the degree.
    fn deg(&self) -> usize;
    /// Declares the expected number of inputs.
    fn n_ins(&self) -> usize;
    /// Declares the expected number of outputs.
    fn n_outs(&self) -> usize;
}

pub struct VerticalIndexing<'a, T> {
    pub vecs: &'a [&'a [T]],
    pub place: usize,
}

impl<'a, T> Index<usize> for VerticalIndexing<'a, T> {
    type Output = T;

    fn index(&self, index: usize) -> &Self::Output {
        &self.vecs[index][self.place]
    }
}

pub trait AlgFnSoUtils<F: TFelt>: AlgFnSO<F> {
    fn map_so(&self, args: &[&[F]]) -> Vec<F>;
}

impl<F: TFelt, Fun: AlgFnSO<F>> AlgFnSoUtils<F> for Fun {
    fn map_so(&self, args: &[&[F]]) -> Vec<F> {
        let n_ins = self.n_ins();
        let n_outs = 1;

        assert!(args.len() == n_ins);
        let l = args[0].len();
        for i in 1..n_ins {
            assert_eq!(args[i].len(), l, "args[i].len() == l")
        }

        let output = (0..l).map(|place|
            self.exec(&VerticalIndexing{vecs: &args, place})
        )
            .collect_vec();
        output
    }
}

pub trait AlgFnUtils<F: TFelt> : AlgFn<F> {
    fn map(&self, args: &[&[F]]) -> Vec<Vec<F>>;
    fn map_split_hi(&self, args: &[&[F]]) -> [Vec<Vec<F>>; 2];
}

impl<F: TFelt, Fun: AlgFn<F>> AlgFnUtils<F> for Fun {
    fn map(&self, args: &[&[F]]) -> Vec<Vec<F>> {
        let n_ins = self.n_ins();
        let n_outs = self.n_outs();

        assert!(args.len() == n_ins);
        let l = args[0].len();
        for i in 1..n_ins {
            assert!(args[i].len() == l)
        }

        let mut output = vec![];
        for _ in 0..n_outs {
            output.push(vec![]);
        }
        for place in 0..l {
            let mut res = self.exec(&VerticalIndexing{vecs: &args, place}).map(|x| Some(x)).collect_vec();
            for s in 0..n_outs {
                output[s].push(res[s].take().unwrap());
                assert_eq!(output[s].len(), place + 1);
            }
        }

        output
        // todo: this ⤵ will require some persuasion, it attempts to move ptr, which is unmovable for some reason.
        // for i in 0..n_outs {
        //     output.push(UninitArr::<F>::new(l))
        // }
        //
        // let mut output_ptrs : Vec<_> = output.iter_mut().map(|o| o.as_shared_mut_ptr()).collect();
        // let ptr = output_ptrs.as_shared_mut_ptr();
        //
        // (0..l).into_par_iter().for_each(|place| {
        //     self.exec(&VerticalIndexing{vecs: &args, place}).zip(0 .. n_outs).for_each(|(x, s)| {
        //         unsafe{*(*ptr.get_mut(s)).get_mut(place) = x;}
        //     });
        // });
        //
        // output.into_iter().map(|arr| unsafe{arr.assume_init()}).collect()
    }

    fn map_split_hi(&self, args: &[&[F]]) -> [Vec<Vec<F>>; 2] {
        let l = args[0].len();
        assert!(l % 2 == 0);
        let half = l / 2;

        let (args_l, args_r): (Vec<_>, Vec<_>) = args.iter().map(|slice| slice.split_at(half)).unzip();
        [self.map(&args_l), self.map(&args_r)]
    }
}


#[derive(Clone)]
pub struct RLC<F> {
    coefs: Vec<F>
}

impl<F: TFelt> RLC<F> {
    pub fn new(coef: F, num_polys: usize) -> Self {
        let mut coefs = Vec::with_capacity(num_polys);
        coefs.push(F::one());
        for _ in 1..num_polys {
            coefs.push(coef * coefs.last().unwrap());
        }
        Self {
            coefs
        }
    }
}
impl<F: TFelt> AlgFnSO<F> for RLC<F> {
    fn exec(&self, args: &impl Index<usize, Output = F>) -> F {
        self.coefs.iter().enumerate().map(|(i, coef)| {*coef * args[i]}).sum()
    }

    fn deg(&self) -> usize {
        1
    }

    fn n_ins(&self) -> usize {
        self.coefs.len()
    }
}