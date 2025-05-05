use std::fmt::{Display, Formatter};
use std::iter::once;
use std::ops::{BitXor, Index};
use ark_std::iterable::Iterable;
use ark_std::{log2, UniformRand};
use ark_std::rand::{Rng, RngCore};
use itertools::Itertools;
use tracing::instrument;
use crate::common::algfn::AlgFnUtils;
use crate::common::math::{eq_poly, evaluate_multivar, evaluate_univar};
use crate::common::wrapper::{ComputationalField, TFelt};
use crate::components::sumcheck::dense_eq::eq_eval;

pub struct Padded<T: Clone, It: Iterator<Item = T>> {
    inner: It,
    len: usize,
    up_to: usize,
    pad: T
}

impl<T: Clone, It: Iterator<Item=T>> Iterator for Padded<T, It> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        self.len += 1;
        self.inner.next().or_else(|| {
            if self.len <= self.up_to {
                Some(self.pad.clone())
            } else {
                None
            }
        })
    }
}

pub trait Pad<T: Clone>: Sized
where Self: Iterator<Item = T> {
    fn pad(self, elt: T, up_to: usize) -> Padded<T, Self>;
}

impl<T: Clone, It: Iterator<Item=T>> Pad<T> for It {
    fn pad(self, elt: T, up_to: usize) -> Padded<T, Self> {
        Padded {
            inner: self,
            len: 0,
            up_to,
            pad: elt,
        }
    }
}

#[derive(Debug, Default, Copy, Clone)]
pub struct AdmSubset {
    p: usize,  // page logsize
    a: usize,  // page offset
    k: usize,  // log(number of full pages)
    u: usize,  // in-page offset
    a_width: usize,  // bit size of a
}

#[derive(Debug, Default, Copy, Clone)]
pub struct _AdmSubset {
    p: usize,
    a: usize,
    k: usize,
    u: usize,
    a_width: usize,
}

macro_rules! AdmSubset {
    {$($field:ident: $value:expr),* $(,)?} => {
        {
        let $crate::components::vspark::matrix::_AdmSubset{p, a, k, u, a_width} = $crate::components::vspark::matrix::_AdmSubset {
            $(
                $field: $value,
            )*
            // ..Default::default()
        };
        $crate::components::vspark::matrix::AdmSubset::new(p, a, k, u, a_width)
        }
    }
}

impl AdmSubset {
    pub fn new_unchecked(p: usize, a: usize, k: usize, u: usize, a_width: usize) -> Self {
        Self {p, a, k, u, a_width}
    }
    pub fn new(p: usize, a: usize, k: usize, u: usize, a_width: usize) -> Self {
        assert!(
            (u == 0) || (k == 0)
        );
        Self::new_unchecked(p, a, k, u, a_width)
    }

    pub fn starting_at(p: usize, start: usize, len: usize, a_width: usize) -> Self {
        let page = 1 << p;
        let k = if len >= page {
            log2(len) as usize - p
        } else {
            0
        };
        let a = start / (page << k);
        let u = start % page;
        assert_eq!(a * (page << k) + u, start);
        Self::new(
            p,
            a,
            k,
            u,
            a_width,
        )
    }

    pub fn fill(l: &AdmLen) -> Self {
        Self{
            p: l.p,
            a: 0,
            k: (log2(l.length()) as usize).max(l.p) - l.p,
            u: 0,
            a_width: 0,
        }
    }

    pub fn start(&self) -> Result<usize, String> {
        let Self{p, a, k, u, a_width} = self;
        if (*u == 0) {
            Ok(a * (1 << (k + p)))
        } else if (*k == 0) {
            Ok(a * (1usize << p) + u)
        } else {
            Err("Unsound data".to_string())
        }
    }
    fn valid(&self) -> bool {
        self.k == 0 || self.u == 0
    }

    fn encode(&self) -> usize {
        let Self{p, a, u, k, a_width} = self; // l is not needed
        (2 * ((1usize << (p - k.min(p))) * ((1usize << a_width) + a) + u) + 1) * (1usize << k)
    }

    pub fn decode(n: usize, p: usize, mut code: usize) -> Option<Self> {
        if code == 0 {
            None
        } else {
            let k = code.trailing_zeros() as usize;
            let u_width = p - k.min(p);

            let a_widht_compl = code.leading_zeros() as usize;
            if usize::BITS as usize <= k + a_widht_compl + 1 + u_width {
                return None;
            }
            code ^= 1 << (usize::BITS as usize - 1 - a_widht_compl);

            let a_width = usize::BITS as usize - k - a_widht_compl - 2 - u_width;
            if k + u_width + 1 > n + 1 {
                return None;
            }
            code >>= k + 1;

            let a = code >> u_width;
            let u = code & ((1 << p) - 1);
            if k != 0 && u != 0 {
                return None;
            }
            Some(Self {
                p,
                a,
                k,
                u,
                a_width
            })
        }
    }
}

pub mod tau {
    pub mod no_decomposition {
        use itertools::Itertools;
        use tracing::instrument;
        use crate::common::wrapper::{ComputationalField, TFelt, TFeltUtil};
        use crate::components::sumcheck::dense_eq::{eq_eval, eq_eval_single};
        use crate::components::vspark::matrix::{assert_r_size, extend_r, hybrid_eq_eval, point_from_usize, AdmSubset};

        pub fn for_subset<F: ComputationalField>(n: usize, s: AdmSubset, r: &[F]) -> F {
            let mut partial =  F::one();
            if s.k == 0 {
                partial = r[0].static_pow(&[s.u as u64]);
            }

            let trailing_width = n - s.k - (s.p - s.p.min(s.k));
            let full = eq_eval(
                &r[(r.len() - trailing_width)..(r.len()- trailing_width + s.a_width)],
                &(0..s.a_width).map(|i| F::from_const(((s.a >> i) & 1) as u64)).collect_vec()
            );
            partial * full
        }

        #[instrument(level = "debug", skip_all)]
        pub fn table<F: ComputationalField>(n: usize, p: usize, r: &[F]) -> Vec<F> {
            assert_r_size(n, p, r);
            (0usize..(1 << (n + 2)))
                .map(|i|
                    AdmSubset::decode(n, p, i).map_or_else(|| at_point(n, p, &point_from_usize(n, i), r), |s| for_subset(n, s, r))
                )
                .collect_vec()
        }


        pub fn at_point<F: TFelt>(n: usize, p: usize, x: &[F], r: &[F]) -> F {
            assert!(x.len() == n + 2);
            let r = extend_r(n, p, r);
            assert_eq!(r.len(), n);

            let mut total = F::zero();
            for k in 0..n + 1 {
                for m in k + 1..n + 2 {

                    let mut term = F::one();
                    for i in 0..k {
                        term *= F::one() - x[i];
                    }
                    term *= x[k];

                    for i in k + 1..m {
                        term *= if i < p + 1 {
                            r[i - 1] * x[i] + F::one() - x[i]
                        } else {
                            eq_eval_single(&x[i], &r[i - 1])
                        };
                    }
                    term *= x[m];
                    for i in m + 1..n + 2 {
                        term *= F::one() - x[i];
                    }
                    total += term;
                }
            }
            total
        }
    }
    pub mod sqrt_decomposition {
        use std::ops::Index;
        use itertools::Itertools;
        use tracing::instrument;
        use crate::common::wrapper::{ComputationalField, TFelt};
        use crate::components::vspark::matrix::IndexTable;

        pub(crate) mod parts {
            use itertools::Itertools;
            use crate::common::wrapper::{ComputationalField, TFelt};
            use crate::components::sumcheck::dense_eq::{eq_eval, eq_eval_single};
            use crate::components::vspark::matrix::{extend_r, hybrid_eq_eval, point_from_usize, IndexTable};

            fn delta<F: TFelt>(x: &[F]) -> F {
                eq_eval(&vec![F::zero(); x.len()], &x)
            }

            fn delta_table<F: TFelt>(logsize: usize) -> Vec<F> {
                let mut ret = vec![F::zero(); 1 << logsize];
                ret[0] = F::one();
                ret
            }

            pub fn left_table<F: ComputationalField>(n: usize, p: usize, mid: usize, r: &[F], f: impl Fn(usize, usize, usize, &[F], &[F]) -> F) -> Vec<F> {
                (0..(1 << mid)).map(|i| {
                    f(n, p, mid, &point_from_usize(n, i)[..mid], &r)
                }).collect_vec()
            }

            pub fn right_table<F: ComputationalField>(n: usize, p: usize, mid: usize, r: &[F], f: impl Fn(usize, usize, usize, &[F], &[F]) -> F) -> Vec<F> {
                (0..(1 << (n + 2 - mid))).map(|i| {
                    f(n, p, mid, &point_from_usize(n, i << mid)[mid..], &r)
                }).collect_vec()
            }

            pub fn leq_l_table<F: ComputationalField>(n: usize, p: usize, mid: usize, r: &[F]) -> Vec<F> {
                delta_table(mid)
            }

            pub fn leq_r_table<F: ComputationalField>(n: usize, p: usize, mid: usize, r: &[F]) -> Vec<F> {
                right_table(n, p, mid, r, leq_r)
            }

            pub fn mid_l_table<F: ComputationalField>(n: usize, p: usize, mid: usize, r: &[F]) -> Vec<F> {
                left_table(n, p, mid, r, mid_l)
            }

            pub fn mid_r_table<F: ComputationalField>(n: usize, p: usize, mid: usize, r: &[F]) -> Vec<F> {
                right_table(n, p, mid, r, mid_r)
            }

            pub fn ge_l_table<F: ComputationalField>(n: usize, p: usize, mid: usize, r: &[F]) -> Vec<F> {
                left_table(n, p, mid, r, ge_l)
            }

            pub fn ge_r_table<F: ComputationalField>(n: usize, p: usize, mid: usize, r: &[F]) -> Vec<F> {
                delta_table(n + 2 - mid)
            }

            pub fn leq_l<F: TFelt>(n: usize, p: usize, mid: usize, x: &[F], r: &[F]) -> F {
                delta(&x)
            }
            pub fn leq_r<F: TFelt>(n: usize, p: usize, mid: usize, x: &[F], r: &[F]) -> F {
                assert_eq!(x.len(), n + 2 - mid, "x.len() == n + 2 - mid");
                let r = extend_r(n, p, r);
                assert_eq!(r.len(), n);

                let mut total = F::zero();
                for k in mid..n + 1 {
                    for m in k + 1..n + 2 {
                        let mut term = F::one();
                        for i in mid..n + 2 {
                            if 0 <= i && i < k {
                                term *= F::one() - x[i - mid];
                            } else if i == k {
                                term *= x[k - mid];
                            } else if k < i && i < m {
                                term *= if i < p + 1 {
                                    r[i - 1] * x[i - mid] + F::one() - x[i - mid]
                                } else {
                                    eq_eval_single(&x[i - mid], &r[i - 1])
                                };
                            } else if i == m {
                                term *= x[m - mid];
                            } else if m < i && i < n + 2 {
                                term *= F::one() - x[i - mid];
                            } else {
                                unreachable!();
                            }
                        }
                        total += term;
                    }
                }
                total
            }
            pub fn mid_l<F: TFelt>(n: usize, p: usize, mid: usize, x: &[F], r: &[F]) -> F {
                assert_eq!(x.len(), mid, "x.len() == mid");
                let r = extend_r(n, p, r);
                assert_eq!(r.len(), n, "r.len() == n");

                let mut total = F::zero();
                for k in 0..mid {
                    let mut term = F::one();
                    for i in 0..mid {
                        if 0 <= i && i < k {
                            term *= F::one() - x[i];
                        } else if i == k {
                            term *= x[k];
                        } else if k < i && i < mid {
                            term *= if i < p + 1 {
                                r[i - 1] * x[i] + F::one() - x[i]
                            } else {
                                eq_eval_single(&x[i], &r[i - 1])
                            };
                        } else {
                            unreachable!();
                        }
                    }
                    total += term;
                }
                total
            }
            pub fn mid_r<F: TFelt>(n: usize, p: usize, mid: usize, x: &[F], r: &[F]) -> F {
                assert!(x.len() == n + 2 - mid);
                let r = extend_r(n, p, r);
                assert_eq!(r.len(), n);

                let mut total = F::zero();
                for m in mid..n + 2 {
                    let mut term = F::one();
                    for i in mid..n + 2 {
                        if mid <= i && i < m {
                            term *= if i < p + 1 {
                                r[i - 1] * x[i - mid] + F::one() - x[i - mid]
                            } else {
                                eq_eval_single(&x[i - mid], &r[i - 1])
                            };
                        } else if i == m {
                            term *= x[m - mid];
                        } else if m < i && i < n + 2 {
                            term *= F::one() - x[i - mid];
                        } else {
                            unreachable!();
                        }
                    }
                    total += term;
                }
                total
            }
            pub fn ge_l<F: TFelt>(n: usize, p: usize, mid: usize, x: &[F], r: &[F]) -> F {
                assert!(x.len() == mid);
                let r = extend_r(n, p, r);
                assert_eq!(r.len(), n);

                let mut total = F::zero();
                for k in 0..n + 1 {
                    for m in k + 1..mid {
                        let mut term = F::one();
                        for i in 0..mid {
                            if 0 <= i && i < k {
                                term *= F::one() - x[i];
                            } else if i == k {
                                term *= x[k];
                            } else if k < i && i < m {
                                term *= if i < p + 1 {
                                    r[i - 1] * x[i] + F::one() - x[i]
                                } else {
                                    eq_eval_single(&x[i], &r[i - 1])
                                };
                            } else if i == m {
                                term *= x[m];
                            } else if m < i && i < n + 2 {
                                term *= F::one() - x[i];
                            } else {
                                unreachable!();
                            }
                        }
                        total += term;
                    }
                }
                total
            }
            pub fn ge_r<F: TFelt>(n: usize, p: usize, mid: usize, x: &[F], r: &[F]) -> F {
                delta(&x)
            }


            #[cfg(test)]
            mod tests {
                use crate::components::vspark::matrix::tau::{no_decomposition, sqrt_decomposition};
                use ark_bn254::Fq as F;
                use ark_std::{test_rng, UniformRand};
                use itertools::Itertools;
                use crate::common::math::evaluate_multivar;
                use crate::common::wrapper::TFeltUtil;
                use crate::components::vspark::matrix::r_size;
                use crate::components::vspark::matrix::tau::sqrt_decomposition::parts;

                #[test]
                fn test_leq() {
                    let rng = &mut test_rng();
                    let n = 6;
                    let p = 2;
                    for mid in 1..n + 2 {
                        for k in 0..n + 2 {
                            for m in 0..n + 2 {
                                if mid <= k && k < m {
                                    let x = (0..n + 2).map(|i| {
                                        if i < k || i > m {
                                            F::zero()
                                        } else if i == k || i == m {
                                            F::one()
                                        } else {
                                            F::rand(rng)
                                        }
                                    }).collect_vec();
                                    let r = (0..r_size(n, p)).map(|_| F::rand(rng)).collect_vec();
                                    let expected = no_decomposition::at_point(n, p, &x, &r);
                                    let left = parts::leq_l(n, p, mid, &x[..mid], &r);
                                    let right = parts::leq_r(n, p, mid, &x[mid..], &r);
                                    let result = left * right;
                                    assert_eq!(result, expected, "k: {}, m: {}, mid: {}, x: {:?}, left: {}, right: {}", k, m, mid, x, left, right);
                                }
                            }
                        }
                    }
                }

                #[test]
                fn test_ge() {
                    let rng = &mut test_rng();
                    let n = 6;
                    let p = 2;
                    for mid in 1..n + 2 {
                        for k in 0..n + 2 {
                            for m in 0..n + 2 {
                                if k < m && m < mid {
                                    let x = (0..n + 2).map(|i| {
                                        if i < k || i > m {
                                            F::zero()
                                        } else if i == k || i == m {
                                            F::one()
                                        } else {
                                            F::rand(rng)
                                        }
                                    }).collect_vec();
                                    let r = (0..r_size(n, p)).map(|_| F::rand(rng)).collect_vec();
                                    let expected = no_decomposition::at_point(n, p, &x, &r);
                                    let left = parts::ge_l(n, p, mid, &x[..mid], &r);
                                    let right = parts::ge_r(n, p, mid, &x[mid..], &r);
                                    let result = left * right;
                                    assert_eq!(result, expected, "k: {}, m: {}, mid: {}, x: {:?}, left: {}, right: {}", k, m, mid, x, left, right);
                                }
                            }
                        }
                    }
                }

                #[test]
                fn test_mid() {
                    let rng = &mut test_rng();
                    let n = 6;
                    let p = 2;
                    for mid in 1..n + 2 {
                        for k in 0..n + 2 {
                            for m in 0..n + 2 {
                                if k < m {
                                    let x = (0..n + 2).map(|i| {
                                        if i < k || i > m {
                                            F::zero()
                                        } else if i == k || i == m {
                                            F::one()
                                        } else {
                                            F::rand(rng)
                                        }
                                    }).collect_vec();
                                    let r = (0..r_size(n, p)).map(|_| F::rand(rng)).collect_vec();
                                    if k < mid && mid <= m {
                                        let expected = no_decomposition::at_point(n, p, &x, &r);
                                        let left = parts::mid_l(n, p, mid, &x[..mid], &r);
                                        let right = parts::mid_r(n, p, mid, &x[mid..], &r);
                                        let result = left * right;
                                        assert_eq!(result, expected, "k: {}, m: {}, mid: {}, x: {:?}, left: {}, right: {}", k, m, mid, x, left, right);
                                    } else {
                                        let expected = F::zero();
                                        let left = parts::mid_l(n, p, mid, &x[..mid], &r);
                                        let right = parts::mid_r(n, p, mid, &x[mid..], &r);
                                        let result = left * right;
                                        assert_eq!(result, expected, "k: {}, m: {}, mid: {}, x: {:?}, left: {}, right: {}", k, m, mid, x, left, right);
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        pub fn at_point<F: TFelt>(n: usize, p: usize, mid: usize, x: &[F], r: &[F]) -> F {

            let leq = parts::leq_l(n, p, mid, &x[..mid], r) * parts::leq_r(n, p, mid, &x[mid..], r);
            let middle = parts::mid_l(n, p, mid, &x[..mid], r) * parts::mid_r(n, p, mid, &x[mid..], r);
            let ge = parts::ge_l(n, p, mid, &x[..mid], r) * parts::ge_r(n, p, mid, &x[mid..], r);
            #[cfg(test)]
            {
                println!("{:?} {:?} {:?}", leq, middle, ge);
            }
            leq + middle + ge
        }

        pub struct SqrtSplitTauTable<F> {
            mid: usize,
            pub parts: [[Vec<F>; 2]; 3]
        }

        impl<F: ComputationalField> IndexTable for SqrtSplitTauTable<F> {
            type Output = F;

            fn at(&self, index: usize) -> Self::Output {
                let l_idx = index % (1 << self.mid);
                let r_idx = index >> self.mid;
                self.parts.iter().map(|pair| {
                    pair[0][l_idx] * pair[1][r_idx]
                }).sum()
            }
        }

        #[instrument(level = "debug", skip_all)]
        pub fn tables<F: ComputationalField>(n: usize, p: usize, mid: usize, r: &[F]) -> SqrtSplitTauTable<F> {
            SqrtSplitTauTable {
                mid,
                parts: [
                    [
                        parts::leq_l_table(n, p, mid, r),
                        parts::leq_r_table(n, p, mid, r),
                    ],
                    [
                        parts::mid_l_table(n, p, mid, r),
                        parts::mid_r_table(n, p, mid, r),
                    ],
                    [
                        parts::ge_l_table(n, p, mid, r),
                        parts::ge_r_table(n, p, mid, r),
                    ],
                ]
            }
        }

        #[cfg(test)]
        mod tests {
            use ark_bn254::Fq as F;
            use ark_std::{test_rng, UniformRand};
            use itertools::Itertools;
            use crate::common::wrapper::TFeltUtil;
            use crate::components::vspark::matrix::{r_size, AdmSubset};
            use crate::components::vspark::matrix::tau::no_decomposition;
            use crate::components::vspark::matrix::tau::sqrt_decomposition;

            #[test]
            fn test_at_encoding_point() {
                let rng = &mut test_rng();
                let n = 6;
                let p = 0;
                for mid in 1..n + 2 {
                    for k in 0..n + 2 {
                        for m in 0..n + 2 {
                            if k < m {
                                let x = (0..n + 2).map(|i| {
                                    if i < k || i > m {
                                        F::zero()
                                    } else if i == k || i == m {
                                        F::one()
                                    } else {
                                        F::rand(rng)
                                    }
                                }).collect_vec();
                                let r = (0..r_size(n, p)).map(|_| F::rand(rng)).collect_vec();
                                let expected = no_decomposition::at_point(n, p, &x, &r);
                                let result = sqrt_decomposition::at_point(n, p, mid, &x, &r);
                                assert_eq!(result, expected, "k: {}, m: {}, mid: {}, x: {:?}", k, m, mid, x);
                            }
                        }
                    }
                }
            }

            #[test]
            fn test_at_01point() {
                let rng = &mut test_rng();
                let n = 6;
                let p = 0;
                for mid in 1..n + 2 {
                    for _x in 0..(1 << (n + 2)) {
                        let x = (0..n + 2).map(|i| {
                            F::from(((_x >> i) & 1) as u64)
                        }).collect_vec();
                        let r = (0..r_size(n, p)).map(|_| F::rand(rng)).collect_vec();
                        let expected = no_decomposition::at_point(n, p, &x, &r);
                        let result = sqrt_decomposition::at_point(n, p, mid, &x, &r);
                        assert_eq!(result, expected, "x: {:#018b} mid: {}", _x, mid);
                    }
                }
            }

            #[test]
            fn test_at_point() {
                let rng = &mut test_rng();
                let n = 6;
                let p = 0;
                for mid in 1..n + 2 {
                    let x = (0..n + 2).map(|i| {
                        F::rand(rng)
                    }).collect_vec();

                    let r = (0..r_size(n, p)).map(|_| F::rand(rng)).collect_vec();

                    for _x in 0..(1 << (n + 2)) {
                        let x = (0..n + 2).map(|i| {
                            F::from(((_x >> i) & 1) as u64)
                        }).collect_vec();
                    }




                    let expected = no_decomposition::at_point(n, p, &x, &r);
                    let result = sqrt_decomposition::at_point(n, p, mid, &x, &r);
                    assert_eq!(result, expected, "mid: {}", mid);
                }
            }
        }
    }
}



pub fn r_size(n: usize, p: usize) -> usize {
    if p == 0 {
        n
    } else {
        n + 1 - p
    }
}

fn assert_r_size<T>(n: usize, p: usize, r: &[T]) {
    assert!(r_size(n, p) == r.len());
}


pub fn hybrid_eq_eval<F: TFelt>(r: &[F], x: &[F]) -> F {
    r.iter().zip_eq(x)
        .map(|(r, x)| {
            *x * r + (F::one() - x)
        }).fold(F::one(), |acc, x| acc * x)
}

fn extend_r<F: TFelt>(n: usize, p: usize, r: &[F]) -> Vec<F> {
    let mut r = r.to_vec();
    if p != 0 {
        let mut powers = vec![r[0]];
        for _ in 1..p {
            let tmp = powers.last().unwrap();
            powers.push(*tmp * tmp);
        }
        powers.extend_from_slice(&r[1..]);
        r = powers;
    }
    r
}


impl Display for AdmSubset{
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("AdmSubset<{}>(a: {}, k: {}, u: {})", self.p, self.a, self.k, self.u))
    }
}

#[derive(Debug, Default, Ord, PartialOrd, Eq, PartialEq, Copy, Clone)]
pub struct AdmLen {
    n: usize,
    p: usize,
    l: usize,
}

impl AdmLen {
    pub fn new(n: usize, p: usize, l: usize) -> Self {
        assert!(l <= (1 << p) || l % (1 << p) == 0);
        Self{n, p, l}
    }
    pub fn length(&self) -> usize {
        self.l
    }

    pub fn can_start_at(&self, pos: AdmSubset) -> bool {
        assert!(self.p == pos.p);
        let start = pos.start().unwrap();
        let ret  = match pos.k {
            0 => {
                pos.u + self.l <= (1 << self.p)
            }
            _ => {
                start % self.l == 0
            }
        };
        ret
    }
}

impl Display for AdmLen {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("AdmLen<{}>({})", self.p, self.l))
    }
}

#[derive(Debug, Default)]
pub struct VsparkRecDescr<F: TFelt> {
    id: usize,
    coeff: F,
    x: AdmSubset,
    y: AdmSubset,
}

impl<F: TFelt> VsparkRecDescr<F> {
    pub fn new(id: usize, coeff: F, x: AdmSubset, y: AdmSubset) -> Self {
        Self {id, coeff, x, y}
    }
}

#[derive(Debug, Default)]
pub struct VsparkMatrix<F: TFelt> {
    px: usize,
    x: AdmLen,
    py: usize,
    y: AdmLen,
    submatrices: Vec<VsparkRecDescr<F>>,
}

impl <F: TFelt> VsparkMatrix<F> {
    pub fn new(px: usize, x: AdmLen, py: usize, y: AdmLen, submatrices: Vec<VsparkRecDescr<F>>) -> Self {
        assert!(px == x.p && py == y.p);
        Self { px, py, x, y, submatrices }
    }
}

#[derive(Debug, Default)]
pub struct VsparkMatrixGroup<F: TFelt> {
    m: Vec<VsparkMatrix<F>>,
}

impl <F: TFelt> VsparkMatrixGroup<F> {
    pub fn new(m: Vec<VsparkMatrix<F>>) -> Self {
        Self {
            m,
        }
    }

    pub fn trivial(nx: usize, px: usize, ny: usize, py: usize, h: usize) -> Self {
        Self::new(
            vec![VsparkMatrix::<F> {
                px,
                x: AdmLen::new(nx, px, 1),
                py,
                y: AdmLen::new(ny, py, 1),
                submatrices: vec![],
            }],
        )
    }

    pub fn valid(&self) -> bool {
        for (i, matrix) in self.m.iter().enumerate() {
            for (subm_idx, subm) in self.m[i].submatrices.iter().enumerate() {
                assert!(subm.id < i, "Invalid submatrix reference; matrix: {}, submatrix loc {}, ref {}", i, subm_idx, subm.id);
                let subm_descr = &self.m[subm.id];
                
                let subm_x_start = subm.x.start();
                assert!(subm_x_start.is_ok(), "Invalid submatrix x region; matrix: {}, submatrix loc {}, subset: {:?}", i, subm_idx, subm.x);
                let subm_x_start = subm_x_start.unwrap();
                assert!(subm_descr.x.can_start_at(subm.x), "Invalid submatrix x start; matrix: {}, submatrix loc {}, subset: {:?}, descr: {:?}, start: {:?}", i, subm_idx, subm.x, subm_descr, subm_x_start);
                assert!(matrix.x.l >= subm_x_start + subm_descr.x.l, "Invalid submatrix x start; matrix: {}, submatrix loc {}, subset: {:?}, {} >= {} + {}", i, subm_idx, subm.x, matrix.x.l, subm_x_start, subm_descr.x.l);
                
                let subm_y_start = subm.y.start();
                assert!(subm_y_start.is_ok(), "Invalid submatrix y region; matrix: {}, submatrix loc {}, subset: {:?}", i, subm_idx, subm.y);
                let subm_y_start = subm_y_start.unwrap();
                assert!(subm_descr.y.can_start_at(subm.y), "Invalid submatrix y start; matrix: {}, submatrix loc {}, subset: {:?}", i, subm_idx, subm.x);
                assert!(matrix.y.l >= subm_y_start + subm_descr.y.l);

                assert!(matrix.x.p == subm.x.p);
                assert!(matrix.x.p == subm_descr.x.p);
                assert!(matrix.y.p == subm.y.p);
                assert!(matrix.y.p == subm_descr.y.p);


                matrix.x.l;
                subm_descr.x.l;
                if matrix.x.l <= (1 << matrix.x.p) {
                    assert!(subm.x.a_width == 0, "Invalid submatrix x a_widht; matrix: {}, submatrix loc {}, n: {}, p: {}, subset: {:?}", i, subm_idx, matrix.x.n, matrix.x.p, subm.x);
                } else {
                    assert!(subm.x.a_width + subm.x.k + matrix.x.p == matrix.x.l.trailing_zeros() as usize, "Invalid submatrix x a_widht; matrix: {}, submatrix loc {}, n: {}, p: {}, subset: {:?}", i, subm_idx, matrix.x.n, matrix.x.p, subm.x);
                }
            }
        }
        true
    }

    pub fn push(&mut self, matrix: VsparkMatrix<F>) {
        self.m.push(matrix);
    }

    pub fn len(&self) -> usize {
        self.m.len()
    }

    pub fn as_rowwise_dense(&self, id: usize) -> Vec<Vec<F>> {
        if id == 0 {
            return vec![vec![F::zero()]];
        }
        let matrix = &self.m[id];
        let mut res = vec![vec![F::zero(); matrix.x.length()]; matrix.y.length()];
        matrix.submatrices.iter().enumerate().for_each(|(_id, submat)| {
            let d = if submat.id == 0 {
                vec![vec![F::one()]]
            } else {
                self.as_rowwise_dense(submat.id)
            };
            let xl = submat.x.start().unwrap();
            let yl = submat.y.start().unwrap();
            for (sr, r) in (yl..yl + d.len()).enumerate() {
                for (sc, c) in (xl..xl + d[0].len()).enumerate() {
                    res[r][c] = res[r][c] + d[sr][sc] * submat.coeff;
                }
            }
        });

        res
    }

    /// Slices big descriptions into several of size <= 2^h
    /// The exact algorithm can change
    /// Current algorithm takes last 2^h entries, puts them into another matrix and adds reference to this new matrix back.
    pub fn slice(self, h: usize) -> Self {
        let mut result_positions = (0..self.m.len()).collect_vec();
        let mut result = VsparkMatrixGroup::new(vec![]);
        for (idx, mut matrix) in self.m.into_iter().enumerate() {
            matrix.submatrices.iter_mut().for_each(|m| {
                m.id = result_positions[m.id];
            });

            while matrix.submatrices.len() > (1 << h) {
                let submatrix_chunk = matrix.submatrices.split_off(matrix.submatrices.len() - (1 << h));
                let addition = VsparkMatrix {
                    px: matrix.px,
                    x: matrix.x,
                    py: matrix.py,
                    y: matrix.y,
                    submatrices: submatrix_chunk,
                };
                matrix.submatrices.push(VsparkRecDescr {
                    id: result.len(),
                    coeff: F::one(),
                    x: AdmSubset::fill(&matrix.x),
                    y: AdmSubset::fill(&matrix.y),
                });
                result.push(addition);
            }
            result_positions[idx] = result.len();
            result.push(matrix);
        }
        result
    }
}

pub trait IndexTable {
    type Output;
    fn at(&self, idx: usize) -> Self::Output;
}

impl<F: Clone> IndexTable for Vec<F> {
    type Output = F;
    fn at(&self, idx: usize) -> Self::Output {
        self[idx].clone()
    }
}

impl <F: ComputationalField> VsparkMatrixGroup<F> {
    pub fn e_poly(&self, taus_x: &impl IndexTable<Output=F>, taus_y: &impl IndexTable<Output=F>, d: usize) -> Vec<F> {
        let mut ret = vec![];

        for i in 0..self.m.len() {
            ret.push(self.m[i].submatrices.iter().map(|sm| {
                taus_x.at(sm.x.encode()) * taus_y.at(sm.y.encode()) * sm.coeff * (
                    ret[sm.id] + if sm.id == 0 {
                        F::one()
                    } else {
                        F::zero()
                    }
                )
            }).fold(F::zero(), |acc, x| acc + x));
        }

        ret.into_iter().pad(F::zero(), 1 << d).collect_vec()
    }

    pub fn i_poly(&self, h: usize, d: usize) -> Vec<usize> {
        let ret: Vec<usize> = self.m.iter().map(|matrix| matrix.submatrices.iter()
            .map(|subm| subm.id)
            .pad(0, (1 << h))
        )
            .flatten()
            .pad(0, (1 << (h + d)))
            .collect();
        assert_eq!(ret.len(), 1 << (h + d));
        ret
    }

    pub fn x_poly(&self, h: usize, d: usize) -> Vec<usize> {
        self.m.iter().map(|matrix| matrix.submatrices.iter()
            .map(|subm| subm.x.encode()).pad(0, (1 << h))).flatten().pad(0, (1 << (h + d))).collect()
    }

    pub fn y_poly(&self, h: usize, d: usize) -> Vec<usize> {
        self.m.iter().map(|matrix| matrix.submatrices.iter()
            .map(|subm| subm.y.encode()).pad(0, (1 << h))).flatten().pad(0, (1 << (h + d))).collect()
    }

    pub fn c_poly(&self, h: usize, d: usize) -> Vec<F> {
        self.m.iter().map(|matrix| matrix.submatrices.iter()
            .map(|subm| subm.coeff).pad(F::zero(), (1 << h))).flatten().pad(F::zero(), (1 << (h + d))).collect()
    }
}

fn hybrid_evals<F: ComputationalField>(p: usize, r: &[F]) -> Vec<F> {
    if p == 0 {
        eq_poly(&r)
    } else {
        let mut powers = vec![r[0]];
        for _ in 1..(1 << p) {
            let tmp = powers.last().unwrap();
            powers.push(*tmp * r[0]);
        }
        let eq = eq_poly(&r[1..]);
        eq.iter().map(|x| powers.iter().map(|p| *p * *x)).flatten().collect()
    }
}

#[cfg(test)]
impl <F: ComputationalField> VsparkMatrixGroup<F> {
    pub fn tests_to_e_poly(&self, nx: usize, px: usize, rx: &[F], ny: usize, py: usize, ry: &[F], d: usize) -> Vec<F> {
        assert_r_size(nx, px, rx);
        assert_r_size(ny, py, ry);

        let ret = (0..self.m.len()).map(|i| {
            let lx = log2(self.m[i].x.l) as usize;
            let ly = log2(self.m[i].y.l) as usize;
            let rx_ = &rx[..lx];
            let ry_ = &ry[..ly];
            let evx = hybrid_evals(px, rx_);
            let evy = hybrid_evals(py, ry_);
    
            let y_size = self.m[i].y.l;
            let x_size = self.m[i].x.l;
            
            let dense = self.as_rowwise_dense(i);

            dense.iter().map(|row| {
                row.into_iter().zip_eq(evx[0..x_size].iter()).map(|(a, b)| {*a * b}).fold(F::zero(), |a, b| a + b)
            }).zip_eq(evy[0..y_size].iter()).map(|(a, b)| {a * b}).fold(F::zero(), |a, b| {a + b})
        }).collect_vec();


        ret.into_iter().pad(F::zero(), 1 << d).collect_vec()
    }
}

impl AdmLen {
    pub fn rand<RNG: Rng>(rng: &mut RNG, n: usize, p: usize) -> Self {
        let number_of_partial_subset_lens = 1 << p;
        let total_number_of_subset_lens = number_of_partial_subset_lens + n + 1 - p;
        let subset_idx = rng.next_u64() as usize % total_number_of_subset_lens;
        match subset_idx < number_of_partial_subset_lens {
            true => {
                Self {
                    n,
                    p,
                    l: subset_idx,
                }
            }
            false => {
                Self {
                    n,
                    p,
                    l: 1 << (p + (subset_idx - number_of_partial_subset_lens)),
                }
            }
        }
    }
}

impl AdmSubset {
    pub fn rand<RNG: Rng>(rng: &mut RNG, parent: AdmLen, len: AdmLen) -> Self {
        let AdmLen {p, l, .. } = len;
        let n = parent.l.trailing_zeros() as usize;

        match l >= 1 << p {
            true => {  // full
                let k = (l >> p).trailing_zeros() as usize;
                let a = rng.next_u64() as usize % (1 << (n - k - p));
                Self {
                    p,
                    a,
                    k,
                    u: 0,
                    a_width: n - k - p
                }
            }
            false => {  // partial
                let a = 0;
                // let a = rng.next_u64() as usize % (1 << (n - p));
                let u = rng.next_u64() as usize % (parent.l.min(1 << p) - l).max(1);
                Self {
                    p,
                    a,
                    k: 0,
                    u,
                    a_width: n.max(p) - p,
                }
            }
        }
    }
}

impl <F: TFelt + UniformRand> VsparkMatrixGroup<F> {
    pub fn rand<RNG: Rng>(rng: &mut RNG, nx: usize, px: usize, ny: usize, py: usize, h: usize, d: usize) -> Self {
        let mut res = Self::trivial(nx, px, ny, py, h);
        let additional_count = rng.next_u64() as usize % (1 << d);
        for _ in 0..additional_count {

            let mut m = loop {
                let m = VsparkMatrix::<F> {
                    px,
                    x: AdmLen::rand(rng, nx, px),
                    py,
                    y: AdmLen::rand(rng, ny, py),
                    submatrices: vec![],
                };
                if m.x.l != 0 && m.y.l != 0 {
                    break m;
                }
            };

            let n_recur = rng.next_u64() as usize % (1 << h) + 1;
            for _ in 0..n_recur {
                let mut retry_times = 10;
                let r_idx = loop {
                    let r_idx = rng.next_u64() as usize % res.len();
                    if res.m[r_idx].x.l < m.x.l && res.m[r_idx].y.l < m.y.l {
                        break r_idx;
                    }
                    retry_times -= 1;
                    if retry_times == 0 {
                        break 0;
                    }
                };
                let r = VsparkRecDescr::new(
                    r_idx,
                    F::one(),
                    // if r_idx == 0 {F::rand(rng)} else {F::one()},
                    AdmSubset::rand(rng, m.x, res.m[r_idx].x),
                    AdmSubset::rand(rng, m.y, res.m[r_idx].y),
                );
                m.submatrices.push(r)
            }
            res.push(m);
        }
        res
    }
}

pub fn point_from_usize<F: ComputationalField>(n: usize, idx: usize) -> Vec<F> {
    (0..n + 2).map(|i| F::from((idx as u64 >> i) & 1)).collect_vec()
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bn254::Fq as F;
    use ark_std::{test_rng, UniformRand};
    use itertools::{assert_equal, repeat_n};
    use crate::common::algfn::AlgFnSO;
    use crate::common::math::{evaluate_multivar, evaluate_univar};
    use crate::common::wrapper::TFeltUtil;
    use crate::components::vspark::vspark::VsparkFinalProd;

    #[test]
    fn test_pad_iterator() {
        assert_eq!(
            (0..3).collect_vec().into_iter().pad(4, 10).collect_vec(),
            vec![0, 1, 2, 4, 4, 4, 4, 4, 4, 4],
        )
    }
    #[test]
    fn test_as_rowwise_dense() {
        let nx = 4;
        let ny = 4;
        let px = 0;
        let py = 0;
        let grp = VsparkMatrixGroup::<F>::new(vec![
            VsparkMatrix{
                px,
                x: AdmLen::new(nx, px, 1),
                py,
                y: AdmLen::new(ny, py, 1),
                submatrices: vec![],
            },
            VsparkMatrix{
                px,
                x: AdmLen::new(nx, px,2),
                py,
                y: AdmLen::new(ny, py, 2),
                submatrices: vec![
                    VsparkRecDescr{
                        id: 0,
                        coeff: <F as From<u64>>::from(1),
                        x: AdmSubset::starting_at(px, 0, 1, 1),
                        y: AdmSubset::starting_at(py, 0, 1, 1),
                    },
                    VsparkRecDescr{
                        id: 0,
                        coeff: <F as From<u64>>::from(1),
                        x: AdmSubset::starting_at(px, 1, 1, 1),
                        y: AdmSubset::starting_at(py, 0, 1, 1),
                    },
                    VsparkRecDescr{
                        id: 0,
                        coeff: <F as From<u64>>::from(2),
                        x: AdmSubset::starting_at(px, 1, 1, 1),
                        y: AdmSubset::starting_at(py, 1, 1, 1),
                    }
                ],
            },
            VsparkMatrix{
                px,
                x: AdmLen::new(nx, px, 4),
                py,
                y: AdmLen::new(ny, py, 2),
                submatrices: vec![
                    VsparkRecDescr{
                        id: 1,
                        coeff: <F as From<u64>>::from(3),
                        x: AdmSubset::starting_at(px,0, 2, 1),
                        y: AdmSubset::starting_at(py, 0, 2, 0),
                    },
                    VsparkRecDescr{
                        id: 1,
                        coeff: <F as From<u64>>::from(4),
                        x: AdmSubset::starting_at(px, 2, 2, 1),
                        y: AdmSubset::starting_at(py, 0, 2, 0),
                    },
                ],
            },
            VsparkMatrix{
                px,
                x: AdmLen::new(nx, px, 8),
                py,
                y: AdmLen::new(ny, py, 8),
                submatrices: vec![
                    VsparkRecDescr{
                        id: 2,
                        coeff: <F as From<u64>>::from(5),
                        x: AdmSubset::starting_at(px, 0, 4, 1),
                        y: AdmSubset::starting_at(py, 0, 2, 2),
                    },
                    VsparkRecDescr{
                        id: 2,
                        coeff: <F as From<u64>>::from(6),
                        x: AdmSubset::starting_at(px, 4, 4, 1),
                        y: AdmSubset::starting_at(py, 4, 2, 2),
                    },
                    VsparkRecDescr{
                        id: 2,
                        coeff: <F as From<u64>>::from(7),
                        x: AdmSubset::starting_at(px, 4, 4, 1),
                        y: AdmSubset::starting_at(py, 6, 2, 2),
                    },
                ],
            }
        ]);

        grp.valid();
        let dense = grp.as_rowwise_dense(3);
        println!("{}", dense.iter().map(|row| {row.iter().map(|e| format!("{: >4}", format!("{:?}", e))).join(", ")}).join("\n"));
        assert_eq!(dense.into_iter().flatten().collect_vec(), vec![
              15,   15,   20,   20,    0,    0,    0,    0,
               0,   30,    0,   40,    0,    0,    0,    0,
               0,    0,    0,    0,    0,    0,    0,    0,
               0,    0,    0,    0,    0,    0,    0,    0,
               0,    0,    0,    0,   18,   18,   24,   24,
               0,    0,    0,    0,    0,   36,    0,   48,
               0,    0,    0,    0,   21,   21,   28,   28,
               0,    0,    0,    0,    0,   42,    0,   56,
        ].into_iter().map(|x| <F as From<u64>>::from(x as u64)).collect_vec());
    }

    #[test]
    fn test_slicing_matrix() {
        fn build_test(logsize: usize) -> VsparkMatrixGroup::<F> {
            let size = 1 << logsize;
            let nx = logsize;
            let ny = logsize;
            let px = 4;
            let py = 4;
            let mut res = VsparkMatrixGroup::<F>::trivial(nx, px, ny, py, 100);
            res.push(VsparkMatrix{
                px,
                x: AdmLen::new(nx, px, size),
                py,
                y: AdmLen::new(ny, py, size),
                submatrices: (0..size).map(|i| (0..size).map(move |j| VsparkRecDescr{
                    id: 0,
                    coeff: <F as From<u64>>::from((i * size + j) as u64),
                    x: AdmSubset::starting_at(px, j, 1, nx - px),
                    y: AdmSubset::starting_at(py, i, 1, ny - py),
                })).flatten().collect_vec(),
            });
            res
        }
    
        let grp = build_test(4);
        assert!(grp.valid());
        let dense = grp.as_rowwise_dense(grp.len() - 1);
        let sliced = grp.slice(2);
        assert!(sliced.valid());
        let dense_sliced = sliced.as_rowwise_dense(sliced.len() - 1);
        assert_eq!(dense_sliced, dense);
    }
    
    
    #[test]
    fn test_slicing_rand_matrix() {
        let rng = &mut test_rng();
        for _ in 0..10 {
            let grp = VsparkMatrixGroup::<F>::rand(
                rng,
                10,
                3,
                10,
                3,
                4,
                4,
            );
            assert!(grp.valid());
            let dense = grp.as_rowwise_dense(grp.len() - 1);
            let sliced = grp.slice(2);
            assert!(sliced.valid());
            let dense_sliced = sliced.as_rowwise_dense(sliced.len() - 1);
            assert_eq!(dense_sliced, dense);
        }
    }


    #[test]
    fn test_encodings() {
        for p in 0..3 {
            for i in 0usize..100 {
                AdmSubset::decode(5, p, i).map(|x| {
                    assert!(x.valid());
                    let res = x.encode();
                    assert_eq!(i, res, "i: {}, x: {}, res: {}, p: {}", i, x, res, p);
                });
            }
        }
    }

    #[test]
    fn test_tau() {
        let n = 5;
        let p = 1;
        let r = vec![
            F::from(1012),
            F::from(1123),
            F::from(3121),
            F::from(21231),
            F::from(12312),
        ];
        let mut err = (vec![], vec![], vec![]);
        for idx in (0..(1 << (n + 2))) {
            let decode = AdmSubset::decode(n, p, idx as usize);
            let mut res1 = F::zero();
            if let Some(s) = decode {
                res1 = tau::no_decomposition::for_subset(n, s, &r);

                let x = point_from_usize(n, idx);
                let res2 = tau::no_decomposition::at_point(n, p, &x, &r);
                if res1 != res2 {
                    if decode.is_some() {
                        err.2.push("adm")
                    } else {
                        err.2.push("not")
                    }
                    err.0.push(idx);
                    err.1.push((res1, res2));
                }
            }
        }

        println!("err idxes: {:?}", err.0);
        for ((a, b), tag) in err.1.iter().zip(err.2.iter()) {
            println!("err val: {} {} {}", tag, a, b);
        }
        assert_eq!(err.0, vec![]);

        let rng = &mut test_rng();
        let tbl = tau::no_decomposition::table(n, p, &r);
        let x = (0..7).map(|_| F::rand(rng)).collect_vec();

        let prover_evaluation = evaluate_multivar(&tbl, &x.clone().into_iter().collect_vec());
        let verifier_evaluation = tau::no_decomposition::at_point(n, p, &x, &r);
        assert_eq!(prover_evaluation, verifier_evaluation);
    }

    #[test]
    fn test_e_poly() {
        let rng = &mut test_rng();
        for _ in 0..10 {
            let (nx, px, ny, py, h, d) = (
                4,
                0,
                4,
                0,
                3,
                3,
            );
            let grp = VsparkMatrixGroup::<F>::rand(
                rng,
                nx,
                px,
                ny,
                py,
                h,
                d,
            );

            // let (nx, px, ny, py, h, d) = (2, 0, 2, 0, 3, 3);
            //
            // let grp = VsparkMatrixGroup::<F>::new(vec![
            //     VsparkMatrix{
            //         px,
            //         x: AdmLen::new(nx, px, 1),
            //         py,
            //         y: AdmLen::new(ny, py, 1),
            //         submatrices: vec![],
            //     },
            //     VsparkMatrix{
            //         px,
            //         x: AdmLen::new(nx, px, 2),
            //         py,
            //         y: AdmLen::new(ny, py, 2),
            //         submatrices: vec![
            //             VsparkRecDescr{
            //                 id: 0,
            //                 coeff: <F as From<u64>>::from(1),
            //                 x: AdmSubset::starting_at(px, 0, 1, 1),
            //                 y: AdmSubset::starting_at(py, 0, 1, 1),
            //             },
            //             VsparkRecDescr{
            //                 id: 0,
            //                 coeff: <F as From<u64>>::from(1),
            //                 x: AdmSubset::starting_at(px, 1, 1, 1),
            //                 y: AdmSubset::starting_at(py, 1, 1, 1),
            //             },
            //         ],
            //     },
            //     VsparkMatrix{
            //         px,
            //         x: AdmLen::new(nx, px, 4),
            //         py,
            //         y: AdmLen::new(ny, py, 4),
            //         submatrices: vec![
            //             VsparkRecDescr{
            //                 id: 1,
            //                 coeff: <F as From<u64>>::from(1),
            //                 x: AdmSubset::starting_at(px, 0, 2, 1),
            //                 y: AdmSubset::starting_at(py, 0, 2, 1),
            //             },
            //             VsparkRecDescr{
            //                 id: 1,
            //                 coeff: <F as From<u64>>::from(1),
            //                 x: AdmSubset::starting_at(px, 2, 2, 1),
            //                 y: AdmSubset::starting_at(py, 2, 2, 1),
            //             },
            //         ],
            //     },
            // ]);


            assert!(grp.valid());

            // println!("{:?}", grp.as_rowwise_dense(grp.len() - 1));

            let rx = (0..(nx + if px != 0 { 1 - px } else { 0 })).map(|_| F::rand(rng)).collect_vec();
            let ry = (0..(ny + if py != 0 { 1 - py } else { 0 })).map(|_| F::rand(rng)).collect_vec();

            let test_epoly = grp.tests_to_e_poly(nx, px, &rx, ny, py, &ry, d);
            let tau_table_x = tau::no_decomposition::table(nx, px, &rx);
            let tau_table_y = tau::no_decomposition::table(ny, py, &ry);
            let rec_epoly = grp.e_poly(&tau_table_x, &tau_table_y, d);
            let sqrt_tau_table_x = tau::sqrt_decomposition::tables(nx, px, (nx + 2) / 2, &rx);
            let sqrt_tau_table_y = tau::sqrt_decomposition::tables(ny, py, (ny + 2) / 2, &ry);
            let sqrt_epoly = grp.e_poly(&sqrt_tau_table_x, &sqrt_tau_table_y, d);

            // let tau_all_possible_offsets = tau_table_x.iter().zip(tau_table_y).map(|(x, y)| *x * y).collect_vec();
            // println!("{:?}", tau_all_possible_offsets);

            // let expected_answer = eq_poly(&rx[..1]).iter().zip(eq_poly(&ry[..1]).iter()).map(|(x, y)| *x * y).fold(F::zero(), |a, b| a + b);
            // println!("{:?}", expected_answer);

            assert_eq!(test_epoly, rec_epoly);
            assert_eq!(sqrt_epoly, rec_epoly);

            let mut adjusted_e_poly = test_epoly.clone();
            adjusted_e_poly[0] += F::one();

            let parts = vec![
                grp.c_poly(h, d),
                grp.i_poly(h, d).into_iter().map(|x| adjusted_e_poly[x]).collect_vec(),
                grp.x_poly(h, d).into_iter().map(|x| tau_table_x[x]).collect_vec(),
                grp.y_poly(h, d).into_iter().map(|x| tau_table_y[x]).collect_vec(),
            ];
            let e_prod = (0..parts[0].len())
                .map(|i| {
                    parts[0][i] * parts[1][i] * parts[2][i] * parts[3][i]
                })
                .chunks(1 << h).into_iter().map(|c| {
                    c.sum::<F>()
                })
                .collect_vec();
            assert_eq!(e_prod, test_epoly);
        }
    }
}