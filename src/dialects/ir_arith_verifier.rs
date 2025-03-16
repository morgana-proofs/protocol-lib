use std::{cell::{RefCell, RefMut}, fmt::Debug, ops::{Add, Mul, Neg, Sub}, rc::Rc, sync::atomic::Ordering};

use crate::common::wrapper::{PolyOpUtil, TPrimeField};

use super::dialect::{TArithmeticDialect, TDialectInterface, TSupportsField, UID};

// ------------- ENCODING --------------

#[derive(Debug)]
pub enum IRArithVerifierEncoding<F: TPrimeField> {
    Read(usize),
    UnconstrainedRead(usize),
    Challenge(usize),
    Add(usize, usize, usize),
    Mul(usize, usize, usize),
    Neg(usize, usize),
    Sub(usize, usize, usize),
    Lc(Vec<F>, Vec<usize>, usize),
    Const(F, usize),
}


// -------------- Board ----------------
pub struct IRArithVerifierBoard<F: TPrimeField> {
    n_wtns: usize,
    ops: Vec<IRArithVerifierEncoding<F>>,
    id: u64,
}

impl<F: TPrimeField> IRArithVerifierBoard<F> {
    pub fn new() -> Self {
        Self { n_wtns: 0, ops: vec![], id: UID.fetch_add(1, Ordering::Relaxed) }
    }
}

// ---------- Board Operator & Sig ------------

#[derive(Clone)]
pub struct Sig<F: TPrimeField> {
    pub addr: usize,
    pub board: Rc<RefCell<IRArithVerifierBoard<F>>>,
}

impl<F: TPrimeField> PartialEq for Sig<F> {
    fn eq(&self, other: &Self) -> bool {
        self.addr == other.addr && self.board_id() == other.board_id()
    }
}
impl<F: TPrimeField> Eq for Sig<F> {}

pub struct IRArithVerifier<F: TPrimeField> {
    board: Rc<RefCell<IRArithVerifierBoard<F>>>,
}


impl<F: TPrimeField> IRArithVerifier<F> {
    pub fn new() -> Self {
        Self {board: Rc::new(RefCell::new(IRArithVerifierBoard::new()))}
    }

    fn board_mut(&self) -> RefMut<IRArithVerifierBoard<F>> {
        (*self.board).borrow_mut()
    }

    fn _alloc_unbound(board: &Rc<RefCell<IRArithVerifierBoard<F>>>) -> Sig<F> {
        let mut board_mut_ref = board.borrow_mut();
        let addr = board_mut_ref.n_wtns;
        board_mut_ref.n_wtns += 1;
        Sig { addr, board: board.clone() }
    }
}


impl<F: TPrimeField> Sig<F> {
    fn board_mut(&self) -> RefMut<IRArithVerifierBoard<F>> {
        (*self.board).borrow_mut()
    }

    fn board_id(&self) -> u64 {
        (*self.board).borrow().id
    }
}

impl<F: TPrimeField> Debug for Sig<F>{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Sig").field("addr", &self.addr).finish()
    }
}

// ------------ Trait implementations -----------------

// ---- Sig is PolyOps ----

impl<F: TPrimeField> PolyOpUtil for Sig<F> {
    type Constants = F;

    fn from_const(&self, value: Self::Constants) -> Self {
        let board = &self.board;
        let out = IRArithVerifier::_alloc_unbound(board);
        self.board_mut().ops.push(IRArithVerifierEncoding::Const(value, out.addr));
        out
    }

    fn lc(coeffs: &[Self::Constants], sigs: &[Self]) -> Self {
        assert!(coeffs.len() > 0);
        assert!(coeffs.len() == sigs.len());
        for i in 1..sigs.len() {
            assert!(sigs[0].board_id() == sigs[i].board_id());
        }
        let board = &sigs[0].board;
        let out = IRArithVerifier::_alloc_unbound(board);
        sigs[0].board_mut().ops.push(IRArithVerifierEncoding::Lc(coeffs.to_vec(), sigs.iter().map(|x| x.addr).collect(), out.addr));
        out
    }
}

impl<F: TPrimeField> Add<Sig<F>> for Sig<F> {
    type Output = Self;

    fn add(self, y: Self) -> Self {
        assert!(self.board_id() == y.board_id());
        let board = &self.board;
        let out = IRArithVerifier::_alloc_unbound(board);
        self.board_mut().ops.push(IRArithVerifierEncoding::Add(self.addr, y.addr, out.addr));
        out
    }
}

impl<F: TPrimeField> Add<&Sig<F>> for Sig<F> {
    type Output = Self;

    fn add(self, y: &Self) -> Self {
        assert!(self.board_id() == y.board_id());
        let board = &self.board;
        let out = IRArithVerifier::_alloc_unbound(board);
        self.board_mut().ops.push(IRArithVerifierEncoding::Add(self.addr, y.addr, out.addr));
        out
    }
}

impl<F: TPrimeField> Add<&mut Sig<F>> for Sig<F> {
    type Output = Self;

    fn add(self, y: &mut Self) -> Self {
        assert!(self.board_id() == y.board_id());
        let board = &self.board;
        let out = IRArithVerifier::_alloc_unbound(board);
        self.board_mut().ops.push(IRArithVerifierEncoding::Add(self.addr, y.addr, out.addr));
        out
    }
}

impl<F: TPrimeField> Mul<Sig<F>> for Sig<F> {
    type Output = Self;

    fn mul(self, y: Self) -> Self {
        assert!(self.board_id() == y.board_id());
        let board = &self.board;
        let out = IRArithVerifier::_alloc_unbound(board);
        self.board_mut().ops.push(IRArithVerifierEncoding::Mul(self.addr, y.addr, out.addr));
        out
    }
}

impl<F: TPrimeField> Mul<&Sig<F>> for Sig<F> {
    type Output = Self;

    fn mul(self, y: &Self) -> Self {
        assert!(self.board_id() == y.board_id());
        let board = &self.board;
        let out = IRArithVerifier::_alloc_unbound(board);
        self.board_mut().ops.push(IRArithVerifierEncoding::Mul(self.addr, y.addr, out.addr));
        out
    }
}

impl<F: TPrimeField> Mul<&mut Sig<F>> for Sig<F> {
    type Output = Self;

    fn mul(self, y: &mut Self) -> Self {
        assert!(self.board_id() == y.board_id());
        let board = &self.board;
        let out = IRArithVerifier::_alloc_unbound(board);
        self.board_mut().ops.push(IRArithVerifierEncoding::Mul(self.addr, y.addr, out.addr));
        out
    }
}

impl<F: TPrimeField> Sub<Sig<F>> for Sig<F> {
    type Output = Self;

    fn sub(self, y: Self) -> Self {
        assert!(self.board_id() == y.board_id());
        let board = &self.board;
        let out = IRArithVerifier::_alloc_unbound(board);
        self.board_mut().ops.push(IRArithVerifierEncoding::Sub(self.addr, y.addr, out.addr));
        out
    }
}

impl<F: TPrimeField> Sub<&Sig<F>> for Sig<F> {
    type Output = Self;

    fn sub(self, y: &Self) -> Self {
        assert!(self.board_id() == y.board_id());
        let board = &self.board;
        let out = IRArithVerifier::_alloc_unbound(board);
        self.board_mut().ops.push(IRArithVerifierEncoding::Sub(self.addr, y.addr, out.addr));
        out
    }
}

impl<F: TPrimeField> Sub<&mut Sig<F>> for Sig<F> {
    type Output = Self;

    fn sub(self, y: &mut Self) -> Self {
        assert!(self.board_id() == y.board_id());
        let board = &self.board;
        let out = IRArithVerifier::_alloc_unbound(board);
        self.board_mut().ops.push(IRArithVerifierEncoding::Sub(self.addr, y.addr, out.addr));
        out
    }
}

impl<F: TPrimeField> Neg for Sig<F> {
    type Output = Self;

    fn neg(self) -> Self {
        let board = &self.board;
        let out = IRArithVerifier::_alloc_unbound(board);
        self.board_mut().ops.push(IRArithVerifierEncoding::Neg(self.addr, out.addr));
        out
    }

}

impl<F: TPrimeField> TSupportsField<Sig<F>> for IRArithVerifier<F> {
    type Constants = F;

    fn _challenge(&mut self) -> Sig<F> {
        let ret: Sig<F> = IRArithVerifier::_alloc_unbound(&self.board);
        self.board_mut().ops.push(IRArithVerifierEncoding::Challenge(ret.addr));
        ret
    }

    fn _read(&mut self) -> Sig<F> {
        let ret: Sig<F> = IRArithVerifier::_alloc_unbound(&self.board);
        self.board_mut().ops.push(IRArithVerifierEncoding::Read(ret.addr));
        ret
    }

    fn _write(&mut self, _value: &Sig<F>) {
        panic!("Write operation is unsupported for verifier dialect")
    }

    fn _unconstrained_read(&mut self) -> Sig<F> {
        let ret: Sig<F> = IRArithVerifier::_alloc_unbound(&self.board);
        self.board_mut().ops.push(IRArithVerifierEncoding::UnconstrainedRead(ret.addr));
        ret
    }

    fn _unconstrained_write(&mut self, _value: &Sig<F>) {
        panic!("Write operation is unsupported for verifier dialect")
    }

}

impl<F: TPrimeField> TDialectInterface for IRArithVerifier<F> {}

impl<F: TPrimeField> TArithmeticDialect for IRArithVerifier<F> {
    type Sig = Sig<F>;
}


#[cfg(test)]
mod tests {
    use ark_bn254::Bn254;
    use ark_ec::pairing::Pairing;
    use ark_ff::Field;

    use crate::{common::wrapper::PolyOpUtil, dialects::{dialect::TDialectInterface, ir_arith_verifier::{IRArithVerifier, Sig}}};

    pub type F = <Bn254 as Pairing>::ScalarField;

    #[test]
    fn minimal_example() {
        let mut verifier = IRArithVerifier::<F>::new();
        let a: Sig<F> = verifier.read();
        let b: Sig<F> = a.from_const(F::from(2).inverse().unwrap());
        let c = a.clone() + b;
        let d = c.clone() * &a;
        let _ = Sig::lc(&[F::from(3), F::from(5), F::from(7)], &[a, c, d]);
    
        println!("{:?}", verifier.board_mut().ops);
    }
}