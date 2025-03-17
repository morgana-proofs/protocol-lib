use std::{any::TypeId, cell::{RefCell, RefMut}, collections::HashMap, fmt::Debug, io::Read, marker::PhantomData, ops::{Add, Mul, Neg, Sub}, rc::Rc, sync::atomic::Ordering};

use ark_serialize::CanonicalDeserialize;

use crate::common::wrapper::{Invert, PolyOpUtil, TPrimeField};

use super::{board::{Board, FormalArithOps, FormalVTranscriptOps, OpEnc, Sig, TSupportsFormalArithOps, TSupportsFormalType, TSupportsFormalVTranscript, TypeEnc}, dialect::{TArithmeticDialect, TDialectInterface, TTranscriptSupports}};

// ------------- ENCODING --------------

#[derive(Debug)]
pub enum IRArithVerifierEncoding<F> {
    Transcript(FormalVTranscriptOps),
    Arith(FormalArithOps<F>),
}

// -------------- Board ----------------
// pub struct IRArithVerifierBoard<F: TPrimeField> {
//     pub n_wtns: usize,
//     pub ops: Vec<IRArithVerifierEncoding<F>>,
//     pub uid: u64,
// }

// impl<F: TPrimeField> IRArithVerifierBoard<F> {
//     pub fn new() -> Self {
//         Self { n_wtns: 0, ops: vec![], uid: UID.fetch_add(1, Ordering::Relaxed) }
//     }
// }

// ---------- Board Operator & Sig ------------

// #[derive(Clone)]
// pub struct Sig<F: TPrimeField> {
//     pub addr: usize,
//     pub board: Rc<RefCell<IRArithVerifierBoard<F>>>,
// }

// impl<F: TPrimeField> PartialEq for Sig<F> {
//     fn eq(&self, other: &Self) -> bool {
//         self.addr == other.addr && self.board_id() == other.board_id()
//     }
// }
// impl<F: TPrimeField> Eq for Sig<F> {}

pub struct IRArithVerifier<F: TPrimeField> {
    board: Rc<RefCell<Board>>,
    _marker: PhantomData<F>
}

impl<F: TPrimeField> IRArithVerifier<F> {
    pub fn new() -> Self {
        let preamble = HashMap::from([(TypeId::of::<Sig<F, Self>>(), TypeEnc(0))]);
        Self {board: Rc::new(RefCell::new(Board::new(preamble))), _marker: PhantomData}
    }

    pub fn decode<R: Read>(mut reader: R) -> Vec<IRArithVerifierEncoding<F>> {
        let mut ret = vec![];
        while let Ok(op) = OpEnc::deserialize_compressed(&mut reader) {
            let typeid = TypeEnc::deserialize_compressed(&mut reader).unwrap();
            assert!(typeid.0 == 0, "We only have a single type.");
            if let Some(x) = Self::decode_vtranscript_op_args(op, &mut reader) {ret.push(IRArithVerifierEncoding::Transcript(x))}
            else if let Some(x) = Self::decode_arith_op_args(op, &mut reader) {ret.push(IRArithVerifierEncoding::Arith((x)))}
            else {panic!()}
        };
        ret
    }
}

// impl<F: TPrimeField> Sig<F> {
//     fn board_mut(&self) -> RefMut<IRArithVerifierBoard<F>> {
//         (*self.board).borrow_mut()
//     }

//     fn board_id(&self) -> u64 {
//         (*self.board).borrow().uid
//     }
// }

// impl<F: TPrimeField> Debug for Sig<F>{
//     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
//         f.debug_struct("Sig").field("addr", &self.addr).finish()
//     }
// }

// ------------ Trait implementations -----------------

// ---- TSupportsArithOps => PolyOps ----

impl<F: TPrimeField, Dialect: TSupportsFormalArithOps<F>> PolyOpUtil for Sig<F, Dialect> {
    type Constants = F;

    fn from_const(&self, value: Self::Constants) -> Self {
        let board = &self.board;
        Dialect::__from_const(board, value)
    }

    fn lc(coeffs: &[Self::Constants], sigs: &[Self]) -> Self {
        assert!(coeffs.len() > 0);
        assert!(coeffs.len() == sigs.len());
        for i in 1..sigs.len() {
            assert!(sigs[0].board_id() == sigs[i].board_id());
        }
        let board = &sigs[0].board;
        Dialect::__lc(board, coeffs, sigs)
    }
}

impl<F: TPrimeField, Dialect: TSupportsFormalArithOps<F>> Add<Sig<F, Dialect>> for Sig<F, Dialect> {
    type Output = Self;

    fn add(self, y: Self) -> Self {
        assert!(self.board_id() == y.board_id());
        let board = &self.board;
        Dialect::__add(board, self.clone(), y)
    }
}

impl<F: TPrimeField, Dialect: TSupportsFormalArithOps<F>> Add<&Sig<F, Dialect>> for Sig<F, Dialect> {
    type Output = Self;

    fn add(self, y: &Self) -> Self {
        assert!(self.board_id() == y.board_id());
        let board = &self.board;
        Dialect::__add(board, self.clone(), y.clone())
    }
}

impl<F: TPrimeField, Dialect: TSupportsFormalArithOps<F>> Add<&mut Sig<F, Dialect>> for Sig<F, Dialect> {
    type Output = Self;

    fn add(self, y: &mut Self) -> Self {
        assert!(self.board_id() == y.board_id());
        let board = &self.board;
        Dialect::__add(board, self.clone(), y.clone())
    }
}

impl<F: TPrimeField, Dialect: TSupportsFormalArithOps<F>> Mul<Sig<F, Dialect>> for Sig<F, Dialect> {
    type Output = Self;

    fn mul(self, y: Self) -> Self {
        assert!(self.board_id() == y.board_id());
        let board = &self.board;
        Dialect::__mul(board, self.clone(), y)
    }
}

impl<F: TPrimeField, Dialect: TSupportsFormalArithOps<F>> Mul<&Sig<F, Dialect>> for Sig<F, Dialect> {
    type Output = Self;

    fn mul(self, y: &Self) -> Self {
        assert!(self.board_id() == y.board_id());
        let board = &self.board;
        Dialect::__mul(board, self.clone(), y.clone())
    }

}

impl<F: TPrimeField, Dialect: TSupportsFormalArithOps<F>> Mul<&mut Sig<F, Dialect>> for Sig<F, Dialect> {
    type Output = Self;

    fn mul(self, y: &mut Self) -> Self {
        assert!(self.board_id() == y.board_id());
        let board = &self.board;
        Dialect::__mul(board, self.clone(), y.clone())
    }
}

impl<F: TPrimeField, Dialect: TSupportsFormalArithOps<F>> Sub<Sig<F, Dialect>> for Sig<F, Dialect> {
    type Output = Self;

    fn sub(self, y: Self) -> Self {
        assert!(self.board_id() == y.board_id());
        let board = &self.board;
        Dialect::__sub(board, self.clone(), y)
    }
}

impl<F: TPrimeField, Dialect: TSupportsFormalArithOps<F>> Sub<&Sig<F, Dialect>> for Sig<F, Dialect> {
    type Output = Self;

    fn sub(self, y: &Self) -> Self {
        assert!(self.board_id() == y.board_id());
        let board = &self.board;
        Dialect::__sub(board, self.clone(), y.clone())
    }
}

impl<F: TPrimeField, Dialect: TSupportsFormalArithOps<F>> Sub<&mut Sig<F, Dialect>> for Sig<F, Dialect> {
    type Output = Self;

    fn sub(self, y: &mut Self) -> Self {
        assert!(self.board_id() == y.board_id());
        let board = &self.board;
        Dialect::__sub(board, self.clone(), y.clone())
    }
}

impl<F: TPrimeField, Dialect: TSupportsFormalArithOps<F>> Neg for Sig<F, Dialect> {
    type Output = Self;

    fn neg(self) -> Self {
        let board = &self.board;
        Dialect::__neg(board, self.clone())
    }
}

impl<F: TPrimeField, Dialect: TSupportsFormalArithOps<F>> Invert for Sig<F, Dialect> {
    type Output = Self;

    fn invert(self) -> Option<Self> {
        let board = &self.board;
        Some(Dialect::__invert(board, self.clone()))
    }
}

impl<F: TPrimeField> TSupportsFormalType<F> for IRArithVerifier<F> {}
impl<F: TPrimeField> TSupportsFormalVTranscript<F> for IRArithVerifier<F> {}
impl<F: TPrimeField> TSupportsFormalArithOps<F> for IRArithVerifier<F> {}

impl<F: TPrimeField> TTranscriptSupports<Sig<F, IRArithVerifier<F>>> for IRArithVerifier<F> {

    fn _challenge(&mut self) -> Sig<F, Self> {
        Self::__challenge(&self.board)
    }

    fn _read(&mut self) -> Sig<F, Self> {
        Self::__read(&self.board)
    }

    fn _write(&mut self, _value: &Sig<F, Self>) {
        panic!("Write operation is unsupported for verifier dialect")
    }

    fn _unconstrained_read(&mut self) -> Sig<F, Self> {
        Self::__read(&self.board)
    }

    fn _unconstrained_write(&mut self, _value: &Sig<F, Self>) {
        panic!("Write operation is unsupported for verifier dialect")
    }

}


impl<F: TPrimeField> TDialectInterface for IRArithVerifier<F> {}
impl<F: TPrimeField> TArithmeticDialect<F> for IRArithVerifier<F> {}


#[cfg(test)]
mod tests {
    use ark_bn254::Bn254;
    use ark_ec::pairing::Pairing;
    use ark_ff::Field;

    use crate::{common::wrapper::PolyOpUtil, dialects::{board::Sig, dialect::TDialectInterface, ir_arith_verifier::IRArithVerifier}};

    pub type F = <Bn254 as Pairing>::ScalarField;

    #[test]
    fn minimal_example() {
        let mut verifier = IRArithVerifier::<F>::new();
        let a = verifier.read();
        let b = a.from_const(F::from(2).inverse().unwrap());
        let c = a.clone() + b;
        let d = c.clone() * &a;
        let _ = Sig::lc(&[F::from(3), F::from(5), F::from(7)], &[a, c, d]);
    
        let tmp = verifier.board.borrow_mut();
        let serialized_ops = &mut tmp.serialized_ops.as_slice();

        println!("{:?}", IRArithVerifier::<F>::decode(serialized_ops));
    }
}