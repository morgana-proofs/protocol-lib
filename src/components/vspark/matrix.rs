use std::fmt::{Display, Formatter};
use anyhow::{ensure, Error};
use ark_std::iterable::Iterable;
use ark_std::log2;
use itertools::Itertools;
use rand::Rng;
use crate::common::wrapper::TPrimeField;


#[derive(Debug, Default, Copy, Clone)]
pub struct AdmSubset<const p: usize> {
    a: usize,
    k: usize,
    u: usize,
    l: usize
}

#[derive(Debug, Default, Copy, Clone)]
pub struct _AdmSubset {
    a: usize,
    k: usize,
    u: usize,
    l: usize,
}

macro_rules! AdmSubset {
    {$($field:ident: $value:expr),* $(,)?} => {
        {
        let $crate::components::vspark::matrix::_AdmSubset{a, k, u, l} = $crate::components::vspark::matrix::_AdmSubset {
            $(
                $field: $value,
            )*
            ..Default::default()
        };
        $crate::components::vspark::matrix::AdmSubset::new(a, k, u, l)
        }
    }
}

impl<const p: usize> AdmSubset<p> {
    pub fn new_unchecked(a: usize, k: usize, u: usize, l: usize) -> Self {
        Self {a, k, u, l}
    }
    pub fn new(a: usize, k: usize, u: usize, l: usize) -> Self {
        assert!(
            (u == 0) && (l == (1 << (k + p))) || (u + l <= (1 << p)) && (k == 0)
        );
        Self::new_unchecked(a, k, u, l)
    }

    pub fn starting_at(start: usize, len: usize) -> Self {
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
            a,
            k,
            u,
            len,
        )
    }

    pub fn fill(l: &AdmLen<p>) -> Self {
        Self{
            a: 0,
            k: (log2(l.length()) as usize) - p,
            u: 0,
            l: l.length(),
        }
    }

    pub fn bounds(&self) -> Result<(usize, usize), String> {
        let Self{a, k, u, l} = self;
        if (*u == 0) && (*l == (1 << (k + p))) {
            Ok((a * (1 << (k + p)), (a + 1) * (1 << (k + p))))
        } else if (u + l <= (1 << p)) && (*k == 0) {
            Ok((a * (1 << p) + u, a * (1 << p) + u + l))
        } else {
            Err("Unsound data".to_string())
        }
    }

    pub fn length(&self) -> Result<usize, String> {
        let bounds = self.bounds()?;
        Ok(bounds.1 - bounds.0)
    }

    pub fn encode(&self) -> usize {
        if self.u == 0 {
            ((self.a << (p + 1)) + 1) << self.k
        } else if self.k == 0 {
            2 * ((1 << p) * self.a + self.u) + 1
        } else {
            panic!("Unsound data")
        }
    }
    
    pub fn decode(mut code: usize) -> Option<Self> {
        if code == 0 {
            None
        } else if code % 2 == 0 {
            let k = code.trailing_zeros() as usize;
            code >>= k + 1;
            if (code.trailing_zeros() as usize) < p {
                None
            } else {
                let a = code >> p;
                Some(Self {
                    a,
                    k,
                    u: 0,
                    l: 0,
                })
            }
        } else {
            code >>= 1;
            let a = code >> p;
            let u = code & ((1 << p) - 1);
            Some(Self {
                a,
                k: 0,
                u,
                l: 0,
            })
        }
    }
}

pub fn build_complete_eq_table<const p: usize>(total_logisze: usize) {

}

impl<const p: usize> Display for AdmSubset<p> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("AdmSubset<{}>(a: {}, k: {}, u: {}, l: {})", p, self.a, self.k, self.u, self.l))
    }
}

#[derive(Debug, Default, Ord, PartialOrd, Eq, PartialEq, Copy, Clone)]
pub struct AdmLen<const p: usize> (usize);

impl<const p: usize> AdmLen<p> {
    pub fn new(l: usize) -> Self {
        assert!(l <= (1 << p) || l % (1 << p) == 0);
        Self(l)
    }
    pub fn length(&self) -> usize {
        self.0
    }
}

impl<const p: usize> Display for AdmLen<p> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("AdmLen<{}>({})", p, self.0))
    }
}

pub fn belongs<const p: usize>(subset: &AdmSubset<p>, set: AdmLen<p>) -> bool {
    subset.bounds().unwrap().1 < set.0
}

#[derive(Debug, Default)]
pub struct VsparkRecDescr<const px: usize, const py: usize, F: TPrimeField> {
    id: usize,
    coeff: F,
    x: AdmSubset<px>,
    y: AdmSubset<py>,
}

impl<const px: usize, const py: usize, F: TPrimeField> VsparkRecDescr<px, py, F> {
    pub fn new(id: usize, coeff: F, x: AdmSubset<px>, y: AdmSubset<py>) -> Self {
        Self {id, coeff, x, y}
    }
}

#[derive(Debug, Default)]
pub struct VsparkMatrix<const px: usize, const py: usize, F: TPrimeField> {
    x: AdmLen<px>,
    y: AdmLen<py>,
    submatrices: Vec<VsparkRecDescr<px, py, F>>,
}

impl <const px: usize, const py: usize, F: TPrimeField> VsparkMatrix<px, py, F> {
    pub fn new(x: AdmLen<px>, y: AdmLen<py>, submatrices: Vec<VsparkRecDescr<px, py, F>>) -> Self {
        Self { x, y, submatrices }
    }
}

#[derive(Debug, Default)]
pub struct VsparkMatrixGroup<const px: usize, const py: usize, F: TPrimeField> {
    m: Vec<VsparkMatrix<px, py, F>>,
}

impl <const px: usize, const py: usize, F: TPrimeField> VsparkMatrixGroup<px, py, F> {
    pub fn new(m: Vec<VsparkMatrix<px, py, F>>) -> Self {
        Self { m }
    }

    pub fn trivial() -> Self {
        Self::new(vec![VsparkMatrix::<px, py, F>{
            x: AdmLen::new(1),
            y: AdmLen::new(1),
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

    pub fn push(&mut self, matrix: VsparkMatrix<px, py, F>) {
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
                    x: matrix.x,
                    y: matrix.y,
                    submatrices: submatrix_chunk,
                };
                matrix.submatrices.push(VsparkRecDescr{
                    id: result.len(),
                    coeff: F::one(),
                    x: AdmSubset!{
                        a: 0,
                        k: 0,
                        u: 0,
                        l: matrix.x.length(),
                    },
                    y: AdmSubset{
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
        fn build_test<const p: usize>() -> VsparkMatrixGroup::<p, p, F> {
            VsparkMatrixGroup::<p, p, F>::new(vec![
                VsparkMatrix{
                    x: AdmLen::new(1),
                    y: AdmLen::new(1),
                    submatrices: vec![],
                },
                VsparkMatrix{
                    x: AdmLen::new(2),
                    y: AdmLen::new(2),
                    submatrices: vec![
                        VsparkRecDescr{
                            id: 0,
                            coeff: <F as From<u64>>::from(1),
                            x: AdmSubset::starting_at(0, 1),
                            y: AdmSubset::starting_at(0, 1),
                        },
                        VsparkRecDescr{
                            id: 0,
                            coeff: <F as From<u64>>::from(1),
                            x: AdmSubset::starting_at(1, 1),
                            y: AdmSubset::starting_at(0, 1),
                        },
                        VsparkRecDescr{
                            id: 0,
                            coeff: <F as From<u64>>::from(2),
                            x: AdmSubset::starting_at(1, 1),
                            y: AdmSubset::starting_at(1, 1),
                        }
                    ],
                },
                VsparkMatrix{
                    x: AdmLen::new(4),
                    y: AdmLen::new(2),
                    submatrices: vec![
                        VsparkRecDescr{
                            id: 1,
                            coeff: <F as From<u64>>::from(3),
                            x: AdmSubset::starting_at(0, 2),
                            y: AdmSubset::starting_at(0, 2),
                        },
                        VsparkRecDescr{
                            id: 1,
                            coeff: <F as From<u64>>::from(4),
                            x: AdmSubset::starting_at(2, 2),
                            y: AdmSubset::starting_at(0, 2),
                        },
                    ],
                },
                VsparkMatrix{
                    x: AdmLen::new(8),
                    y: AdmLen::new(8),
                    submatrices: vec![
                        VsparkRecDescr{
                            id: 2,
                            coeff: <F as From<u64>>::from(5),
                            x: AdmSubset::starting_at(0, 4),
                            y: AdmSubset::starting_at(0, 2),
                        },
                        VsparkRecDescr{
                            id: 2,
                            coeff: <F as From<u64>>::from(6),
                            x: AdmSubset::starting_at(2, 4),
                            y: AdmSubset::starting_at(3, 2),
                        },
                        VsparkRecDescr{
                            id: 2,
                            coeff: <F as From<u64>>::from(7),
                            x: AdmSubset::starting_at(4, 4),
                            y: AdmSubset::starting_at(6, 2),
                        },
                    ],
                }
            ])
        }
        let grp = build_test::<3>();
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
        fn build_test(logsize: usize) -> VsparkMatrixGroup::<16, 16, F> {
            let size = 1 << logsize;
            let mut res = VsparkMatrixGroup::<16, 16, F>::trivial();
            res.push(VsparkMatrix{
                x: AdmLen::new(size),
                y: AdmLen::new(size),
                submatrices: (0..size).map(|i| (0..size).map(move |j| VsparkRecDescr{
                    id: 0,
                    coeff: <F as From<u64>>::from((i * size + j) as u64),
                    x: AdmSubset::starting_at(j, 1),
                    y: AdmSubset::starting_at(i, 1),
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
        AdmSubset::<3>::decode(0);
        for i in 0usize..100 {
            AdmSubset::<3>::decode(i).map(|x| {
                let res = AdmSubset::encode(&x);
                assert_eq!(i, res, "{}, {}, {}", i, x, res)
            });
        }
    }
}