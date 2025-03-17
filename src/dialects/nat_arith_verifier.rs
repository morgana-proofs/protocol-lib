// // Native arithmetic verifier (fallible for incorrect proofs, only for debug)

// use crate::common::wrapper::{PolyOps, TPrimeField};
// use super::dialect::{TArithmeticDialect, TDialectInterface, TTranscriptSupports};

// pub struct NatArithVerifier<F: PolyOps + Copy> {
//     proof: Vec<F>,
//     ctr: usize,
// }

// impl<F: TPrimeField> TTranscriptSupports<F> for NatArithVerifier<F> {

//     fn _challenge(&mut self) -> F {
//         todo!()
//     }

//     fn _read(&mut self) -> F {
//         todo!()
//     }

//     fn _write(&mut self, _value: &F) {
//         panic!("Write operation is unsupported for verifier dialect")
//     }

//     fn _unconstrained_read(&mut self) -> F {
//         let ret = self.proof[self.ctr];
//         self.ctr += 1;
//         ret
//     }

//     fn _unconstrained_write(&mut self, _value: &F) {
//         panic!("Write operation is unsupported for verifier dialect")
//     }

// }

// impl<F: TPrimeField> TDialectInterface for NatArithVerifier<F> {}

// impl<F: TPrimeField> TArithmeticDialect for NatArithVerifier<F> {
//     type Sig = F;
// }