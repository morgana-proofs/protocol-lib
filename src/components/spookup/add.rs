use std::marker::PhantomData;

use crate::common::wrapper::TFelt;

use super::spookup::SpookupOp;

#[derive(Debug, Clone, Copy)]
pub struct SpookupAdd<F: TFelt> {
    limb_bitsize: usize,
    mask: u32,
    _marker: PhantomData<fn () -> F>, // to make it Sync / Send without asking F
}

impl<F: TFelt> SpookupAdd<F> {
    pub fn new(limb_bitsize: usize) -> Self {
        assert!(limb_bitsize <= 15, "input won't fit in u32, too large to process anyway");
        Self { limb_bitsize, mask: (1 << limb_bitsize) - 1, _marker: PhantomData }
    }
}

/// Table of evaluations of xnor (aka eq polynomial in dim 1).
fn ev_xnor<F: TFelt>(x: F, y: F) -> F {
    F::one() - x - y + (x * y).double()
}

/// Table of evaluations of xor.
fn ev_xor<F: TFelt>(x: F, y: F) -> F {
    x + y - (x * y).double()
}


// two outputs correspond to the case where there is and there is no incoming carry
fn evaluate_add_base_case<F: TFelt>(x: F, y: F, z: F, carry_out: F) -> [F; 2] {
    let l = F::one();

    // if incoming carry = 0
    // 0000
    // 0110
    // 1010
    // 1101
    // if incoming carry = 1
    // 0010
    // 0101
    // 1001
    // 1111
 
    let xy11 = x * y; // x * y
    let xy01 = y - xy11; // (1 - x) * y
    let xy10 = x - xy11; // x * (1 - y)
    let xy00 = l - xy01 - xy10 - xy11;

    let zw11 = z * carry_out;
    let zw01 = carry_out - zw11;
    let zw10 = z - zw11;
    let zw00 = l - zw01 - zw10 - zw11;

    let carry_0_case = xy00 * zw00 + (xy01 + xy10) * zw10 + xy11 * zw01;
    let carry_1_case = xy00 * zw10 + (xy01 + xy10) * zw01 + xy11 * zw11;

    [carry_0_case, carry_1_case]
}

// index of the output in binary is a pair (input carry, output carry)
fn evaluate_add_inductive_step<F: TFelt>(x: F, y: F, z: F) -> [F; 4] {

    let xy11 = x * y; // x * y
    let xy01 = y - xy11; // (1 - x) * y
    let xy10 = x - xy11; // x * (1 - y)
    let xy00 = F::one() - xy01 - xy10 - xy11;

    let z1 = z;
    let z0 = F::one() - z;

    // 00:
    // 000
    // 011
    // 101

    // 01:
    // 110

    // 10:
    // 001

    // 11:
    // 100
    // 010
    // 111

    [
        xy00 * z0 + (xy01 + xy10) * z1,
        xy11 * z0,
        xy00 * z1,
        (xy01 + xy10) * z0 + xy11 * z1
    ]

}

/// Function that recursively evaluates adder. Outputs two evaluations separately
/// - one for incoming carry = 0, other for incoming carry = 1.
fn evaluate_add<F: TFelt>(x: &[F], y: &[F], z: &[F], carry_out: F) -> [F; 2] {
    if x.len() == 1 {
        evaluate_add_base_case(x[0], y[0], z[0], carry_out)
    } else {
        let [inc0, inc1] = evaluate_add(&x[1..], &y[1..], &z[1..], carry_out);
        let [c00, c01, c10, c11] = evaluate_add_inductive_step(x[0], y[0], z[0]);
        [c00 * inc0 + c01 * inc1, c10 * inc0 + c11 * inc1]
    }

}

impl<F: TFelt> SpookupOp for SpookupAdd<F> {
    type F = F;

    fn n_bits_in(&self) -> usize {
        2 * self.limb_bitsize + 1
    }

    fn n_bits_out(&self) -> usize {
        self.limb_bitsize + 1
    }

    fn apply(&self, x: u32) -> u32 {
        (x & self.mask) + ((x >> self.limb_bitsize) & self.mask) + (x >> (self.limb_bitsize * 2))
    }

    fn verifier_evaluate(&self, input_point: &[Self::F], output_point: &[Self::F]) -> Self::F {
        assert!(input_point.len() == self.n_bits_in());
        assert!(output_point.len() == self.n_bits_out());
        
        let x = &input_point[0 .. self.limb_bitsize];
        let y = &input_point[self.limb_bitsize .. 2 * self.limb_bitsize];
        let inc = input_point[2 * self.limb_bitsize];

        let z = &output_point[0 .. self.limb_bitsize];
        let out = output_point[self.limb_bitsize];

        let [e0, e1] = evaluate_add(x, y, z, out);

        (F::one() - inc) * e0 + inc * e1
    }
}

#[cfg(test)]
mod tests {

    use ark_bn254::Fq as F;
    use ark_ff::UniformRand;
    use ark_std::{rand::RngCore, test_rng};
    use itertools::Itertools;

    use crate::{common::{math::{eq_poly_sequence_last, evaluate_multivar}, wrapper::TFeltUtil}, components::spookup::{add::evaluate_add_base_case, spookup::SpookupOp}, protocol::component::TProtocol, transcript::transcript::tests::ManualTestTranscript};
    use super::{evaluate_add_inductive_step, SpookupAdd};

    #[test]
    fn inductive_step_tables() {
        for x in 0..2u64 {
            for y in 0..2u64 {
                    for z in 0..2u64 {

                        let s = evaluate_add_inductive_step::<F>(x.into(), y.into(), z.into());
                        
                        for inc in 0..2u64 {
                            for out in 0..2u64 {
                                assert!((s[(inc * 2 + out) as usize] == F::one()) == (((x + y + inc) % 2 == z) && ((x + y + inc) >> 1 == out)))
                            }
                        }
                }
            }
        }

        let rng = &mut test_rng();
        let pt = (0..3).map(|_| F::rand(rng)).collect_vec();

        let rhs = evaluate_add_inductive_step(pt[0], pt[1], pt[2]);

        for inc in 0..2 {
            for out in 0..2 {
                let ev_table: Vec<F> = (0..8).map(|s| ((s >> 2) & 1, (s >> 1) & 1, (s >> 0) & 1)).map(|(x, y, z)| (((x + y + inc) % 2 == z) && ((x + y + inc) >> 1 == out)) as u64).map(|x| x.into()).collect_vec();

                assert!(evaluate_multivar(&ev_table, &pt) == rhs[inc * 2 + out]);
            }
        }

    }

    #[test]
    fn base_case_tables() {
        for x in 0..2u64 {
            for y in 0..2u64 {
                for z in 0..2u64 {
                    for carry_out in 0..2u64 {

                        let [a, b] = evaluate_add_base_case::<F>(x.into(), y.into(), z.into(), carry_out.into());
                        let (a, b) = (a == F::one(), b == F::one());
                    
                        assert!(a == (((x + y) % 2 == z) && ((x + y) >> 1 == carry_out)), "x {} y {} c {} z {} | a {} b {}", x, y, carry_out, z, a, b);
                        assert!(b == (((x + y + 1) % 2 == z) && ((x + y + 1) >> 1 == carry_out)), "x {} y {} c {} z {} | a {} b {}", x, y, carry_out, z, a, b);
                    }
                }
            }
        }

        let rng = &mut test_rng();
        let pt = (0..4).map(|_| F::rand(rng)).collect_vec();

        let rhs = evaluate_add_base_case(pt[0], pt[1], pt[2], pt[3]);

        for inc in 0..2 {
                let ev_table: Vec<F> = (0..16).map(|s| ((s >> 3) & 1, (s >> 2) & 1, (s >> 1) & 1, (s >> 0) & 1)).map(|(x, y, z, carry_out)| (((x + y + inc) % 2 == z) && ((x + y + inc) >> 1 == carry_out)) as u64).map(|x| x.into()).collect_vec();
                assert!(evaluate_multivar(&ev_table, &pt) ==  rhs[inc]);
            }
        }


    

    #[test]

    fn add_spookup_works() {
        let bitsize = 4;
        let adder = SpookupAdd::<F>::new(bitsize);

        fn as_point(x: u32, l: usize) -> Vec<F> {
            let mut tmp : Vec<F> = (0..l).map(|j| ((x >> j) % 2).into()).collect();
            tmp.reverse();
            tmp
        }

        for n in 0u32 .. 1 << adder.n_bits_in() {
            for m in 0u32 .. 1 << adder.n_bits_out() {
                let q = adder.verifier_evaluate(&as_point(n, adder.n_bits_in()), &as_point(m, adder.n_bits_out()));
                assert!(q == F::one() || q == F::zero());
                
                assert!(
                    (adder.apply(n) == m) ==
                    (q == F::one())
                )
            }
        }

        // and check compatibility with prover in random point

        let bitsize = 7;
        let adder = SpookupAdd::<F>::new(bitsize);
        let rng = &mut test_rng();
        let pt_in = (0..adder.n_bits_in()).map(|_| F::rand(rng)).collect_vec();
        let pt_out = (0..adder.n_bits_out()).map(|_| F::rand(rng)).collect_vec();

        let prover_table = adder.prover_evaluate_at_output(&pt_out);

        let a = eq_poly_sequence_last(&pt_in).unwrap();
        let b = eq_poly_sequence_last(&pt_out).unwrap();

        let mut acc = F::zero();
        for n in 0u32 .. 1 << adder.n_bits_in() {
            let m = adder.apply(n) as usize;
            let n = n as usize;
            acc += a[n] * b[m]
        }


        println!("Verifier gives: {}", adder.verifier_evaluate(&pt_in, &pt_out));
        println!("Prover gives: {}", evaluate_multivar(&prover_table, &pt_in));
        println!("Naive eval: {}", acc);

//        assert!(adder.verifier_evaluate(&pt_in, &pt_out) == evaluate_multivar(&prover_table, &pt_in));

    }

    #[test]
    fn add_spookup_verifier_accepts_prover() {
        let n_bits = 7;
        let spooky_add = SpookupAdd::<F>::new(n_bits);
        let rng = &mut test_rng();
        let pt_out = (0..n_bits).map(|_| {F::rand(rng)}).collect_vec();

        let transcript = ManualTestTranscript::new((0..1000).map(|_|F::rand(rng)).collect());

        let inputs = (0..100000).map(|_| rng.next_u32() % (spooky_add.n_bits_in() as u32)).collect_vec(); //inputs are triples a, b, carry bit. outputs are a+b+carry, and output carry
        let outputs = inputs.iter().map(|&x| spooky_add.apply(x)).collect_vec();


        todo!();
        //spooky_add.prove(&mut transcript, claims, advice);

    }



}