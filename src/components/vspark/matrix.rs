use std::fmt::{Display, Formatter};
use anyhow::{ensure, Error};
use ark_std::iterable::Iterable;
use ark_std::log2;
use itertools::Itertools;
use rand::Rng;
use crate::common::wrapper::TPrimeField;


#[derive(Debug, Default, Copy, Clone)]
pub struct AdmSubset {
    p: usize,
    a: usize,
    k: usize,
    u: usize,
    l: usize
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

    fn encode(&self, p: usize) -> usize {
        let Self{a, u, k, ..} = self; // l is not needed

        (2 * ((1 << p) * a + u) + 1) * (1usize << k)
    }

    pub fn decode(p: usize, mut code: usize) -> Option<Self> {
        if code == 0 {
            None
        } else {
            let k = code.trailing_zeros() as usize;
            code >>= k + 1;
            let a = code >> p;
            let u = code & ((1 << p) - 1);
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

pub fn build_tau_table(p: usize, total_logisze: usize) {

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
pub struct VsparkRecDescr<F: TPrimeField> {
    id: usize,
    coeff: F,
    x: AdmSubset,
    y: AdmSubset,
}

impl<F: TPrimeField> VsparkRecDescr<F> {
    pub fn new(id: usize, coeff: F, x: AdmSubset, y: AdmSubset) -> Self {
        Self {id, coeff, x, y}
    }
}

#[derive(Debug, Default)]
pub struct VsparkMatrix<F: TPrimeField> {
    px: usize,
    x: AdmLen,
    py: usize,
    y: AdmLen,
    submatrices: Vec<VsparkRecDescr<F>>,
}

impl <F: TPrimeField> VsparkMatrix<F> {
    pub fn new(px: usize, x: AdmLen, py: usize, y: AdmLen, submatrices: Vec<VsparkRecDescr<F>>) -> Self {
        assert!(px == x.p && py == y.p);
        Self { px, py, x, y, submatrices }
    }
}

#[derive(Debug, Default)]
pub struct VsparkMatrixGroup<F: TPrimeField> {
    m: Vec<VsparkMatrix<F>>,
}

impl <F: TPrimeField> VsparkMatrixGroup<F> {
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
            AdmSubset::decode(p, i).map(|x| {
                let res = x.encode(p);
                assert_eq!(i, res, "{}, {}, {}", i, x, res);
            });
        }
    }
}