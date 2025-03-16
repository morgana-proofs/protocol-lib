use std::sync::atomic::AtomicU64;

use crate::common::wrapper::{PolyOps, TPrimeField};

pub static UID: AtomicU64 = AtomicU64::new(0);

pub trait TSupportsField<F: PolyOps> {
    type Constants : TPrimeField;
    /// squeezes new challenge
    fn _challenge(&mut self) -> F;
    /// reads from transcript (or allocates this operation); fails for prover dialects - they write and do not read
    fn _read(&mut self) -> F;
    /// writes to transcript (or allocates this operation); fails for verifier dialects - they read and do not write
    fn _write(&mut self, value: &F);
    /// same as read, but does not invoke sponge
    fn _unconstrained_read(&mut self) -> F;
    /// same as write, but does not invoke sponge
    fn _unconstrained_write(&mut self, value: &F); 
}

pub trait TDialectInterface {
    /// squeezes new challenge
    fn challenge<F>(&mut self) -> F where F: PolyOps, Self: TSupportsField<F> {
        self._challenge()
    }

    /// reads from transcript (or allocates this operation); fails for prover dialects - they write and do not read
    fn read<F>(&mut self) -> F where F: PolyOps, Self: TSupportsField<F> {
        self._read()
    }

    /// writes to transcript (or allocates this operation); fails for verifier dialects - they read and do not write
    fn write<F>(&mut self, value: &F) where F: PolyOps, Self: TSupportsField<F> {
        self._write(value)
    }

    /// same as read, but does not invoke sponge
    fn unconstrained_read<F>(&mut self) -> F where F: PolyOps, Self: TSupportsField<F> {
        self._unconstrained_read()
    }

    /// same as write, but does not invoke sponge
    fn unconstrained_write<F>(&mut self, value: &F) where F: PolyOps, Self: TSupportsField<F> {
        self._unconstrained_write(value)
    }

}

/// A verifier that is capable of field element manipulation
pub trait TArithmeticDialect: TDialectInterface + TSupportsField<Self::Sig> {
    type Sig: PolyOps;
}