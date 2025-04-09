use std::fmt::{Display, Formatter};
use std::iter::once;
use std::ops::BitXor;
use ark_std::iterable::Iterable;
use ark_std::log2;
use itertools::Itertools;
use crate::common::wrapper::{ComputationalField, TFelt};
use crate::components::sumcheck::dense_eq::eq_eval;

#[derive(Debug, Default, Copy, Clone)]
pub struct AdmSubset {
    p: usize,  // page logsize
    a: usize,  // page offset
    k: usize,  // log(number of full pages)
    u: usize,  // in-page offset
    l: usize,  // length
}

#[derive(Debug, Default, Copy, Clone)]
pub struct _AdmSubset {
    p: usize,
    a: usize,
    k: usize,
    u: usize,
    l: usize,
}

macro_rules! AdmSubset {
    {$($field:ident: $value:expr),* $(,)?} => {
        {
        let $crate::components::vspark::matrix::_AdmSubset{p, a, k, u, l} = $crate::components::vspark::matrix::_AdmSubset {
            $(
                $field: $value,
            )*
            ..Default::default()
        };
        $crate::components::vspark::matrix::AdmSubset::new(p, a, k, u, l)
        }
    }
}

impl AdmSubset {
    pub fn new_unchecked(p: usize, a: usize, k: usize, u: usize, l: usize) -> Self {
        Self {p, a, k, u, l}
    }
    pub fn new(p: usize, a: usize, k: usize, u: usize, l: usize) -> Self {
        assert!(
            (u == 0) && (l == (1 << (k + p))) || (u + l <= (1 << p)) && (k == 0)
        );
        Self::new_unchecked(p, a, k, u, l)
    }

    pub fn starting_at(p: usize, start: usize, len: usize) -> Self {
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
            len,
        )
    }

    pub fn fill(l: &AdmLen, p: usize) -> Self {
        Self{
            p,
            a: 0,
            k: (log2(l.length()) as usize) - p,
            u: 0,
            l: l.length(),
        }
    }

    pub fn bounds(&self) -> Result<(usize, usize), String> {
        let Self{p, a, k, u, l} = self;
        if (*u == 0) && (*l == (1 << (k + p))) {
            Ok((a * (1 << (k + p)), (a + 1) * (1 << (k + p))))
        } else if (u + l <= (1 << p)) && (*k == 0) {
            Ok((a * (1usize << p) + u, a * (1usize << p) + u + l))
        } else {
            Err("Unsound data".to_string())
        }
    }

    pub fn length(&self) -> Result<usize, String> {
        let bounds = self.bounds()?;
        Ok(bounds.1 - bounds.0)
    }

    fn encode(&self) -> usize {
        let Self{p, a, u, k, l } = self; // l is not needed

        (2 * ((1usize << p) * a + u) + 1) * (1usize << k)
    }

    pub fn decode(n: usize, p: usize, mut code: usize) -> Option<Self> {
        if code == 0 {
            None
        } else {
            let k = code.trailing_zeros() as usize;
            if k + p + 1 > n + 1 {
                return None;
            }
            code >>= k + 1;
            let a = code >> p;
            let u = code & ((1 << p) - 1);
            if k != 0 && u != 0 {
                return None;
            }
            Some(Self {
                p,
                a,
                k,
                u,
                l: 0,
            })
        }
    }
}


pub fn compute_tau<F: ComputationalField>(n: usize, s: AdmSubset, r: &[F]) -> F {
    let mut partial =  F::one();
    if s.k == 0 {
        partial = r[0].static_pow(&[s.u as u64]);
    }

    let a_width = n - s.k - s.p;
    let full = eq_eval(&r[(r.len() - a_width)..], &(0..a_width).map(|i| F::from_const(((s.a >> i) & 1) as u64)).collect_vec());
    partial * full
}

pub fn compute_tau_table<F: ComputationalField>(n: usize, p: usize, r: &[F]) -> Vec<F> {
    if p == 0 {
        assert!(r.len() == n - p);
    } else {
        assert!(r.len() == n + 1 - p);
    }
    (0usize..(1 << (n + 1)))
        .map(|i|
            AdmSubset::decode(n, p, i).map_or(F::zero(), |s| compute_tau(n, s, r))
        )
        .collect_vec()
}


pub fn hybrid_eq_eval<F: TFelt>(r: &[F], x: &[F]) -> F {
    r.iter().zip_eq(x)
        .map(|(r, x)| {
            *x * r + (F::one() - x)
        }).fold(F::one(), |acc, x| acc * x)
}

pub fn compute_tau_at_point<F: TFelt>(n: usize, p: usize, x: &[F], r: &[F]) -> F {
    assert!(x.len() == n + 1);
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
    assert_eq!(r.len(), n);

    let partials = x[0] * hybrid_eq_eval(&r[0..p], &x[1..(p + 1)]) * eq_eval(&r[p..], &x[(p + 1)..]);
    let mut fulls = F::zero();

    // k = 2; (1 - x_0)
    for k in 1..(n + 1 - p) {
        let mut tmp = (0..k).map(|i| F::one() - x[i]).fold(F::one(), |acc, x| acc * x);
        tmp = tmp * x[k];
        tmp = tmp * (k + 1..k + p + 1).map(|i| F::one() - x[i]).fold(F::one(), |acc, x| acc * x);
        tmp = tmp * eq_eval(&x[(k + p + 1)..(n + 1)], &r[(k + p)..]);
        fulls = fulls + tmp;
    }
    partials + fulls
}

impl Display for AdmSubset{
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("AdmSubset<{}>(a: {}, k: {}, u: {}, l: {})", self.p, self.a, self.k, self.u, self.l))
    }
}

#[derive(Debug, Default, Ord, PartialOrd, Eq, PartialEq, Copy, Clone)]
pub struct AdmLen {
    p: usize,
    l: usize,
}

impl AdmLen {
    pub fn new(p: usize, l: usize) -> Self {
        assert!(l <= (1 << p) || l % (1 << p) == 0);
        Self{p, l}
    }
    pub fn length(&self) -> usize {
        self.l
    }
}

impl Display for AdmLen {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("AdmLen<{}>({})", self.p, self.l))
    }
}

pub fn belongs(subset: &AdmSubset, set: AdmLen) -> bool {
    subset.bounds().unwrap().1 < set.l
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
        Self { m }
    }

    pub fn trivial(px: usize, py: usize) -> Self {
        Self::new(vec![VsparkMatrix::<F>{
            px,
            x: AdmLen::new(px, 1),
            py,
            y: AdmLen::new(py, 1),
            submatrices: vec![],
        }])
    }

    pub fn valid(&self) -> bool {
        for (i, matrix) in self.m.iter().enumerate() {
            for (subm_idx, subm) in self.m[i].submatrices.iter().enumerate() {
                assert!(subm.id < i, "Invalid submatrix reference; matrix: {}, submatrix loc {}, ref {}", i, subm_idx, subm.id);
                assert!(subm.x.bounds().is_ok(), "Invalid submatrix x region; matrix: {}, submatrix loc {}, subset: {:?}", i, subm_idx, subm.x);
                assert!(subm.y.bounds().is_ok(), "Invalid submatrix y region; matrix: {}, submatrix loc {}, subset: {:?}", i, subm_idx, subm.y);
                assert!(subm.x.l == self.m[subm.id].x.length());
                assert!(subm.y.l == self.m[subm.id].y.length());
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
            return vec![vec![F::one()]];
        }
        let matrix = &self.m[id];
        let mut res = vec![vec![F::zero(); matrix.x.length()]; matrix.y.length()];
        matrix.submatrices.iter().enumerate().for_each(|(_id, submat)| {
            let d = self.as_rowwise_dense(submat.id);
            let (xl, xr) = submat.x.bounds().unwrap();
            let (yl, yr) = submat.y.bounds().unwrap();
            for (sr, r) in (yl..yr).enumerate() {
                for (sc, c) in (xl..xr).enumerate() {
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
                let addition = VsparkMatrix{
                    px: matrix.px,
                    x: matrix.x,
                    py: matrix.py,
                    y: matrix.y,
                    submatrices: submatrix_chunk,
                };
                matrix.submatrices.push(VsparkRecDescr{
                    id: result.len(),
                    coeff: F::one(),
                    x: AdmSubset!{
                        p: matrix.px,
                        a: 0,
                        k: 0,
                        u: 0,
                        l: matrix.x.length(),
                    },
                    y: AdmSubset!{
                        p: matrix.py,
                        a: 0,
                        k: 0,
                        u: 0,
                        l: matrix.y.length(),
                    },
                });
                result.push(addition);
            }
            result_positions[idx] = result.len();
            result.push(matrix);
        }
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bn254::Fq as F;
    use crate::common::wrapper::TFeltUtil;

    #[test]
    fn test_as_rowwise_dense() {
        fn build_test(px: usize, py: usize) -> VsparkMatrixGroup::<F> {
            VsparkMatrixGroup::<F>::new(vec![
                VsparkMatrix{
                    px,
                    x: AdmLen::new(px, 1),
                    py,
                    y: AdmLen::new(py, 1),
                    submatrices: vec![],
                },
                VsparkMatrix{
                    px,
                    x: AdmLen::new(px,2),
                    py,
                    y: AdmLen::new(py, 2),
                    submatrices: vec![
                        VsparkRecDescr{
                            id: 0,
                            coeff: <F as From<u64>>::from(1),
                            x: AdmSubset::starting_at(px, 0, 1),
                            y: AdmSubset::starting_at(py, 0, 1),
                        },
                        VsparkRecDescr{
                            id: 0,
                            coeff: <F as From<u64>>::from(1),
                            x: AdmSubset::starting_at(px, 1, 1),
                            y: AdmSubset::starting_at(py, 0, 1),
                        },
                        VsparkRecDescr{
                            id: 0,
                            coeff: <F as From<u64>>::from(2),
                            x: AdmSubset::starting_at(px, 1, 1),
                            y: AdmSubset::starting_at(py, 1, 1),
                        }
                    ],
                },
                VsparkMatrix{
                    px,
                    x: AdmLen::new(px, 4),
                    py,
                    y: AdmLen::new(py, 2),
                    submatrices: vec![
                        VsparkRecDescr{
                            id: 1,
                            coeff: <F as From<u64>>::from(3),
                            x: AdmSubset::starting_at(px,0, 2),
                            y: AdmSubset::starting_at(py, 0, 2),
                        },
                        VsparkRecDescr{
                            id: 1,
                            coeff: <F as From<u64>>::from(4),
                            x: AdmSubset::starting_at(px, 2, 2),
                            y: AdmSubset::starting_at(py, 0, 2),
                        },
                    ],
                },
                VsparkMatrix{
                    px,
                    x: AdmLen::new(px, 8),
                    py,
                    y: AdmLen::new(py, 8),
                    submatrices: vec![
                        VsparkRecDescr{
                            id: 2,
                            coeff: <F as From<u64>>::from(5),
                            x: AdmSubset::starting_at(px, 0, 4),
                            y: AdmSubset::starting_at(py, 0, 2),
                        },
                        VsparkRecDescr{
                            id: 2,
                            coeff: <F as From<u64>>::from(6),
                            x: AdmSubset::starting_at(px, 2, 4),
                            y: AdmSubset::starting_at(py, 3, 2),
                        },
                        VsparkRecDescr{
                            id: 2,
                            coeff: <F as From<u64>>::from(7),
                            x: AdmSubset::starting_at(px, 4, 4),
                            y: AdmSubset::starting_at(py, 6, 2),
                        },
                    ],
                }
            ])
        }
        let grp = build_test(3, 3);
        grp.valid();
        let dense = grp.as_rowwise_dense(3);
        println!("{}", dense.iter().map(|row| {row.iter().map(|e| format!("{: >4}", format!("{:?}", e))).join(", ")}).join("\n"));
        assert_eq!(dense.into_iter().flatten().collect_vec(), vec![
              15,   15,   20,   20,    0,    0,    0,    0,
               0,   30,    0,   40,    0,    0,    0,    0,
               0,    0,    0,    0,    0,    0,    0,    0,
               0,    0,   18,   18,   24,   24,    0,    0,
               0,    0,    0,   36,    0,   48,    0,    0,
               0,    0,    0,    0,    0,    0,    0,    0,
               0,    0,    0,    0,   21,   21,   28,   28,
               0,    0,    0,    0,    0,   42,    0,   56,
        ].into_iter().map(|x| <F as From<u64>>::from(x as u64)).collect_vec());
    }

    #[test]
    fn test_slicing_matrix() {
        fn build_test(logsize: usize) -> VsparkMatrixGroup::<F> {
            let size = 1 << logsize;
            let px = 16;
            let py = 16;
            let mut res = VsparkMatrixGroup::<F>::trivial(px, py);
            res.push(VsparkMatrix{
                px,
                x: AdmLen::new(px, size),
                py,
                y: AdmLen::new(py, size),
                submatrices: (0..size).map(|i| (0..size).map(move |j| VsparkRecDescr{
                    id: 0,
                    coeff: <F as From<u64>>::from((i * size + j) as u64),
                    x: AdmSubset::starting_at(px, j, 1),
                    y: AdmSubset::starting_at(py, i, 1),
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
    fn test_encodings() {
        let p = 3;
        for i in 0usize..100 {
            AdmSubset::decode(5, p, i).map(|x| {
                let res = x.encode();
                assert_eq!(i, res, "{}, {}, {}", i, x, res);
            });
        }
    }

    #[test]
    fn test_tau() {
        let n = 5;
        let p = 0;
        let r = vec![
            F::from(1012),
            F::from(1123),
            F::from(3121),
            F::from(21231),
            F::from(12312),
        ];
        let mut err = (vec![], vec![]);
        for idx in (0..(1 << (n + 1))) {
            let decode = AdmSubset::decode(n, p, idx as usize);
            let mut res1 = F::zero();
            if let Some(s) = decode {
                res1 = compute_tau(n, s, &r);
            }
            let x = vec![
                F::from((idx >> 0) & 1),
                F::from((idx >> 1) & 1),
                F::from((idx >> 2) & 1),
                F::from((idx >> 3) & 1),
                F::from((idx >> 4) & 1),
                F::from((idx >> 5) & 1),
            ];
            let res2 = compute_tau_at_point(n, p, &x, &r);
            if res1 != res2 {
                err.0.push(idx);
                err.1.push((res1, res2));
            }
        }

        println!("{:?}", err.0);
        for (a, b) in err.1 {
            println!("{} {}", a, b);
        }
        assert_eq!(err.0, vec![]);
    }
}