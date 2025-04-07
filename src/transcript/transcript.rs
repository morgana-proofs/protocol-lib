// use crate::common::wrapper::{TFelt, TPrimeField};

// use super::board::{Sig, TSupportsFormalArithOps, TSupportsFormalType, TSupportsFormalVTranscript};

use crate::common::wrapper::TFelt;

// /// Entry point trait that passes through all interesting operations (so they can be conveniently called without fully qualified syntax).
// /// Due to "where" semantics, methods are unavailable unless an actual implementor trait is present.
pub trait TTranscriptInterface {
    /// squeezes new challenge
    fn challenge<F>(&mut self) -> F where Self: TTranscriptSupports<F> {
        self._challenge()
    }

    /// reads from transcript (or allocates this operation); fails for prover dialects - they write and do not read
    fn read<F>(&mut self) -> F where Self: TTranscriptSupports<F> {
        self._read()
    }

    /// writes to transcript (or allocates this operation); fails for verifier dialects - they read and do not write
    fn write<F>(&mut self, value: &F) where Self: TTranscriptSupports<F> {
        self._write(value)
    }

    /// same as read, but does not invoke sponge
    fn unconstrained_read<F>(&mut self) -> F where Self: TTranscriptSupports<F> {
        self._unconstrained_read()
    }

    /// same as write, but does not invoke sponge
    fn unconstrained_write<F>(&mut self, value: &F) where Self: TTranscriptSupports<F> {
        self._unconstrained_write(value)
    }
}


// /// Trait for general interactions with transcript. Operations from it are passed to TDialectInterface, because otherwise
// /// we would need fully qualified syntax to run them.
// /// Methods in this trait are generally fallible - prover is unable to use read methods, verifier is unable to use write
// /// methods, and some challenges can be unsupported. This is completely OK and much better than having separate traits for
// /// each of these concepts. 
pub trait TTranscriptSupports<T> {
    /// squeezes new challenge
    fn _challenge(&mut self) -> T;
    /// reads from transcript (or allocates this operation); fails for prover dialects - they write and do not read
    fn _read(&mut self) -> T;
    /// writes to transcript (or allocates this operation); fails for verifier dialects - they read and do not write
    fn _write(&mut self, value: &T);
    /// same as read, but does not invoke sponge
    fn _unconstrained_read(&mut self) -> T;
    /// same as write, but does not invoke sponge
    fn _unconstrained_write(&mut self, value: &T); 
}

// /// A verifier that is capable of field element manipulation
// pub trait TFormalArithmeticDialect<F: TPrimeField>: TDialectInterface + TSupportsFormalType<F> + TSupportsFormalArithOps<F> + TSupportsFormalVTranscript<F> + TTranscriptSupports<Sig<F, Self>>{}

pub trait TArithmeticTranscript<F: TFelt> : TTranscriptInterface + TTranscriptSupports<F> {}

// impl<F: TPrimeField, Dialect: TFormalArithmeticDialect<F>> TArithmeticDialect<Sig<F, Dialect>> for Dialect {}


#[cfg(test)]
pub mod tests {
    use super::*;

    pub struct ManualTestTranscript<F: TFelt> {
        challenges: Vec<F>,
        c_idx: usize,
        data: Vec<F>,
        d_idx: usize,
    }
    
    impl<F: TFelt> ManualTestTranscript<F> {
        pub fn new(challenges: Vec<F>) -> Self {
            Self {
                challenges,
                c_idx: 0,
                data: vec![],
                d_idx: 0,
            }
        }
        pub fn end(&mut self) {
            self.c_idx = 0;
        }
    }
    
    impl<F: TFelt> TTranscriptInterface for ManualTestTranscript<F> {}
    impl<F: TFelt> TTranscriptSupports<F> for ManualTestTranscript<F> {
        fn _challenge(&mut self) -> F {
            self.c_idx += 1;
            self.challenges[self.c_idx - 1].clone()
        }

        fn _read(&mut self) -> F {
            self.d_idx += 1;
            self.data[self.d_idx - 1].clone()
        }

        fn _write(&mut self, value: &F) {
            self.data.push(value.clone());
        }

        fn _unconstrained_read(&mut self) -> F {
            self.d_idx += 1;
            self.data[self.d_idx - 1].clone()
        }

        fn _unconstrained_write(&mut self, value: &F) {
            self.data.push(value.clone());
        }
    }

    impl<F: TFelt> TArithmeticTranscript<F> for ManualTestTranscript<F> {}
}