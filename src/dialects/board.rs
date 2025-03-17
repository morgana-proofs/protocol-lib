// Board to allocate signals in and traits related to encoding of operations.

use std::{any::TypeId, cell::{RefCell, RefMut}, collections::HashMap, fmt::Debug, io::{Read, Write}, marker::PhantomData, rc::Rc, sync::atomic::{AtomicU64, Ordering}};

use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use itertools::Itertools;

use crate::common::wrapper::TPrimeField;

static UID2 : AtomicU64 = AtomicU64::new(0);

const ENC_TRANSCRIPT_CHALLENGE : u32 = 0;
const ENC_TRANSCRIPT_READ : u32 = 1;
const ENC_TRANSCRIPT_UNCONSTRAINED_READ : u32 = 2;
const ENC_FIELD_ADD : u32 = 3;
const ENC_FIELD_MUL : u32 = 4;
const ENC_FIELD_SUB : u32 = 5;
const ENC_FIELD_NEG : u32 = 6;
const ENC_FIELD_INV : u32 = 7;
const ENC_FIELD_LC : u32 = 8;
const ENC_FIELD_CONST : u32 = 9;

pub struct Sig<T: 'static, Dialect: 'static> {
    pub addr: Addr,
    pub board: Rc<RefCell<Board>>,
    pub _marker: PhantomData<(T, Dialect)>,
}

impl<T: 'static, Dialect: 'static> Clone for Sig<T, Dialect> {
    fn clone(&self) -> Self {
        Self { addr: self.addr.clone(), board: self.board.clone(), _marker: PhantomData }
    }
}

impl<T: 'static, Dialect: 'static> Sig<T, Dialect> {
    pub fn board_mut(&self) -> RefMut<Board> {
        (*self.board).borrow_mut()
    }

    pub fn board_id(&self) -> u64 {
        (*self.board).borrow().uid
    }
}

impl<T: 'static, Dialect: 'static> Debug for Sig<T, Dialect>{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Sig").field("addr", &self.addr.0).finish()
    }
}


/// Encoding of a type, operated by dialect. From the perspective of the board, it is enforced by HashMap preamble.
#[derive(Clone, Copy, PartialEq, Eq, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct TypeEnc(pub u32);

#[derive(Clone, Copy, PartialEq, Eq, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct OpEnc(pub u32);


/// Unique address of a value.
#[derive(Clone, Copy, PartialEq, Eq, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct Addr(pub usize);

pub struct Board {
 
    pub preamble: HashMap<TypeId, TypeEnc>, // A map that encodes each supported TypeId with a particular index. 
                                          // Supplied by the wrapping dialect on construction (TypeIds can change from run to run,
                                          // but these will always be correctly decoded as long as they are decoded by the same dialect).
                                          // Note that these typeids are not T-s, but of Sig<T>-s (because we might want to supports entries
                                          // that are not Sigs, but smth else, say Sponges, or Vars, or Lcs)
    pub wtns_table: Vec<TypeEnc>, // Table of types of witnesses. 
    pub serialized_ops: Vec<u8>,
    pub uid: u64,
}

impl Board {
    pub fn new(preamble: HashMap<TypeId, TypeEnc>) -> Self {
        Self { preamble, wtns_table: vec![], serialized_ops: vec![], uid: UID2.fetch_add(1, Ordering::Relaxed) }
    }

    /// Fetches sig type encoding. Fallible if preamble does not contain this type.
    fn fetch_sig_type_enc<T: 'static, Dialect: 'static>(&mut self) -> TypeEnc {
        *self.preamble.get(&TypeId::of::<Sig<T, Dialect>>()).unwrap()
    }
}

pub trait TSupportsFormalType<T: 'static> : 'static + Sized {
    fn _alloc_unbound(board: &Rc<RefCell<Board>>) -> Sig<T, Self> {
        let mut board_mut_ref = board.borrow_mut();
        let typeid = board_mut_ref.fetch_sig_type_enc::<T, Self>();
        let tt = &mut board_mut_ref.wtns_table;
        let addr = tt.len();
        tt.push(typeid);
        Sig { addr: Addr(addr), board: board.clone(), _marker: PhantomData }
    }

    /// Helper method that encodes an operation from INS to OUTS signals (of a single type, without constants involved).
    fn _encode_typed_sig_op<const INS: usize, const OUTS: usize>(board: &Rc<RefCell<Board>>, name: OpEnc, args: [Sig<T, Self>; INS]) -> [Sig<T, Self>; OUTS] {
        let output = [(); OUTS].map(|()| Self::_alloc_unbound(board));
        let mut board_mut_ref = board.borrow_mut();
        let typeid = board_mut_ref.fetch_sig_type_enc::<T, Self>();
        let encoded_input = args.map(|x| x.addr);
        let encoded_output = output.iter().map(|x|x.addr).collect_array::<OUTS>().unwrap();
        let op_encoding = name;
        let op_types = typeid;
        let op_data = (encoded_input, encoded_output);
        op_encoding.serialize_compressed(&mut board_mut_ref.serialized_ops).unwrap(); // write opcode
        op_types.serialize_compressed(&mut board_mut_ref.serialized_ops).unwrap(); // write types
        op_data.serialize_compressed(&mut board_mut_ref.serialized_ops).unwrap(); // write addresses
        output        
    }

}


#[derive(Debug)]
pub enum FormalVTranscriptOps {
    Challenge(([Addr; 0], [Addr; 1])),
    Read(([Addr; 0], [Addr; 1])),
    UnconstrainedRead(([Addr; 0], [Addr; 1]))
}

// --------- Implementations of serialization operations for a board. Trait should be implemented by an arithmetic dialect that desires to support this subset of operations. ----------
pub trait TSupportsFormalVTranscript<T: 'static> : TSupportsFormalType<T>{
    fn __challenge(board: &Rc<RefCell<Board>>) -> Sig<T, Self> {
        let [ret] = Self::_encode_typed_sig_op(board, OpEnc(ENC_TRANSCRIPT_CHALLENGE), []);
        ret
    }
    fn __read(board: &Rc<RefCell<Board>>) -> Sig<T, Self> {
        let [ret] = Self::_encode_typed_sig_op(board, OpEnc(ENC_TRANSCRIPT_READ), []);
        ret
    }
    fn __unconstrained_read(board: &Rc<RefCell<Board>>) -> Sig<T, Self> {
        let [ret] = Self::_encode_typed_sig_op(board, OpEnc(ENC_TRANSCRIPT_UNCONSTRAINED_READ), []);
        ret
    }

    // Sus
    fn decode_vtranscript_op_args<R: Read>(opcode: OpEnc, reader: &mut R) -> Option<FormalVTranscriptOps> {
        match opcode.0 {
            ENC_TRANSCRIPT_CHALLENGE => {
                Some(FormalVTranscriptOps::Challenge(CanonicalDeserialize::deserialize_compressed(reader).unwrap()))
            }
            ENC_TRANSCRIPT_READ => {
                Some(FormalVTranscriptOps::Read(CanonicalDeserialize::deserialize_compressed(reader).unwrap()))
            }
            ENC_TRANSCRIPT_UNCONSTRAINED_READ => {
                Some(FormalVTranscriptOps::UnconstrainedRead(CanonicalDeserialize::deserialize_compressed(reader).unwrap()))
            }
            _ => None
        }
    }
}

#[derive(Debug)]
pub enum FormalArithOps<F> {
    Add(([Addr; 2], [Addr; 1])),
    Mul(([Addr; 2], [Addr; 1])),
    Neg(([Addr; 1], [Addr; 1])),
    Invert(([Addr; 1], [Addr; 1])),
    Sub(([Addr; 2], [Addr; 1])),
    Lc(((Vec<F>, Vec<Addr>), Addr)),
    Const((F, Addr)),
}


pub trait TSupportsFormalArithOps<F: TPrimeField> : TSupportsFormalType<F> {
    fn __add(board: &Rc<RefCell<Board>>, a: Sig<F, Self>, b: Sig<F, Self>) -> Sig<F, Self> {
        let [ret] = Self::_encode_typed_sig_op(board, OpEnc(ENC_FIELD_ADD), [a, b]);
        ret
    }
    fn __mul(board: &Rc<RefCell<Board>>, a: Sig<F, Self>, b: Sig<F, Self>) -> Sig<F, Self> {
        let [ret] = Self::_encode_typed_sig_op(board, OpEnc(ENC_FIELD_MUL), [a, b]);
        ret
    }
    fn __sub(board: &Rc<RefCell<Board>>, a: Sig<F, Self>, b: Sig<F, Self>) -> Sig<F, Self> {
        let [ret] = Self::_encode_typed_sig_op(board, OpEnc(ENC_FIELD_SUB), [a, b]);
        ret
    }
    fn __neg(board: &Rc<RefCell<Board>>, a: Sig<F, Self>) -> Sig<F, Self> {
        let [ret] = Self::_encode_typed_sig_op(board, OpEnc(ENC_FIELD_NEG), [a]);
        ret
    }
    fn __invert(board: &Rc<RefCell<Board>>, a: Sig<F, Self>) -> Sig<F, Self> {
        let [ret] = Self::_encode_typed_sig_op(board, OpEnc(ENC_FIELD_INV), [a]);
        ret
    }


    fn __lc(board: &Rc<RefCell<Board>>, coeffs: &[F], sigs: &[Sig<F, Self>]) -> Sig<F, Self> {
        assert!(coeffs.len() == sigs.len());
        let output = Self::_alloc_unbound(board);
        let mut board_mut_ref = board.borrow_mut();
        let typeid = board_mut_ref.fetch_sig_type_enc::<F, Self>();
        let encoded_input = (coeffs.to_vec(), sigs.iter().map(|x| x.addr).collect_vec());
        let encoded_output = output.addr;
        let op_encoding = OpEnc(ENC_FIELD_LC);
        let op_types = typeid;
        let op_data = (encoded_input, encoded_output);
        op_encoding.serialize_compressed(&mut board_mut_ref.serialized_ops).unwrap();
        op_types.serialize_compressed(&mut board_mut_ref.serialized_ops).unwrap();
        op_data.serialize_compressed(&mut board_mut_ref.serialized_ops).unwrap();
        output        
    }

    fn __from_const(board: &Rc<RefCell<Board>>, value: F) -> Sig<F, Self> {
        let output = Self::_alloc_unbound(board);
        let mut board_mut_ref = board.borrow_mut();
        let typeid = board_mut_ref.fetch_sig_type_enc::<F, Self>();
        let encoded_input = value;
        let encoded_output = output.addr;
        let op_encoding = OpEnc(ENC_FIELD_CONST);
        let op_types = typeid;
        let op_data = (encoded_input, encoded_output);
        op_encoding.serialize_compressed(&mut board_mut_ref.serialized_ops).unwrap();
        op_types.serialize_compressed(&mut board_mut_ref.serialized_ops).unwrap();
        op_data.serialize_compressed(&mut board_mut_ref.serialized_ops).unwrap();
        output        
    }

    fn decode_arith_op_args<R: Read>(opcode: OpEnc, reader: &mut R) -> Option<FormalArithOps<F>> {
        match opcode.0 {
            ENC_FIELD_ADD => {
                Some(FormalArithOps::Add(CanonicalDeserialize::deserialize_compressed(reader).unwrap()))
            },
            ENC_FIELD_MUL => {
                Some(FormalArithOps::Mul(CanonicalDeserialize::deserialize_compressed(reader).unwrap()))
            },
            ENC_FIELD_SUB => {
                Some(FormalArithOps::Sub(CanonicalDeserialize::deserialize_compressed(reader).unwrap()))
            },
        
            ENC_FIELD_NEG => {
                Some(FormalArithOps::Neg(CanonicalDeserialize::deserialize_compressed(reader).unwrap()))
            },
            ENC_FIELD_INV => {
                Some(FormalArithOps::Invert(CanonicalDeserialize::deserialize_compressed(reader).unwrap()))
            },
            ENC_FIELD_LC => {
                Some(FormalArithOps::Lc(CanonicalDeserialize::deserialize_compressed(reader).unwrap()))
            },
            ENC_FIELD_CONST => {
                Some(FormalArithOps::Const(CanonicalDeserialize::deserialize_compressed(reader).unwrap()))
            },
            _ => None,
        }
    }
}