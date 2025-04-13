use std::collections::HashSet;

use itertools::Itertools;
use rayon::prelude::*;

use crate::common::{ptr_utils::{AsSharedMUMutPtr, UninitArr, UnsafeIndexRawMut}, wrapper::TFelt};

use super::spookup::MatrixOp;

pub struct SpookupOp<F: TFelt> {
    pub op: Box<dyn MatrixOp<F = F>>,
    pub inputs: Vec<usize>,
    pub outputs: Vec<usize>,
}

#[derive(Debug, Clone, Copy)]
pub struct Word {
    pub addr: usize,
}

/// Constructor of a spookup circuit.
pub struct SpookupCircuitConstructor<F: TFelt> {
    /// i-th element of this array is a bitlength of i-th word
    pub word_bitsizes: Vec<usize>,
    /// i-th element of this array is the set of addresses of words that comprise i-th state
    pub state_snapshots: Vec<HashSet<usize>>,
    /// operations that maps i-th state to i+1-st state
    pub operations: Vec<SpookupOp<F>>,
}

impl<F: TFelt> SpookupCircuitConstructor<F> {
    pub fn new(input_bitsizes: &[usize]) -> (Self, Vec<Word>) {
        (
            Self {
                word_bitsizes: input_bitsizes.to_vec(),
                state_snapshots: vec![(0..input_bitsizes.len()).collect()],
                operations: vec![]
            },
            (0..input_bitsizes.len()).map(|x| Word{addr: x}).collect()
        )
    }

    fn alloc_word(&mut self, bitsize: usize) -> Word {
        let l = self.word_bitsizes.len();
        self.word_bitsizes.push(bitsize);
        Word {addr: l}
    }

    /// Takes a collection of input words of total length k, lengths of output words of total length k', and a MatrixOp from
    /// k-bit strings to k'-bit strings. Concatenation of words is assumed to be little-endian.
    pub fn op(&mut self, op: impl MatrixOp<F = F> + 'static, inputs: &[Word], output_format: &[usize]) -> Vec<Word> {
        assert!(op.n_bits_in() == inputs.iter().map(|word| self.word_bitsizes[word.addr]).sum());
        assert!(op.n_bits_out() == output_format.iter().sum());
        
        let mut new_state = self.state_snapshots.last().unwrap().clone();
        for input in inputs {
            assert!(new_state.remove(&input.addr));
        }

        let outputs = output_format.iter().map(|&bitsize| self.alloc_word(bitsize)).collect_vec();
        for output in &outputs {
            new_state.insert(output.addr);
        }

        self.state_snapshots.push(new_state);
        self.operations.push(
            SpookupOp{
                op: Box::new(op),
                inputs: inputs.iter().map(|x| x.addr).collect(),
                outputs: outputs.iter().map(|x| x.addr).collect() }
        );

        outputs
    }

    pub fn finish(self) -> SpookupCircuit<F> {
        let SpookupCircuitConstructor{ word_bitsizes, state_snapshots, operations } = self;
        SpookupCircuit { word_bitsizes, state_snapshots, operations }
    }
}

pub struct SpookupCircuit<F: TFelt> {
    /// i-th element of this array is a bitlength of i-th word
    pub word_bitsizes: Vec<usize>,
    /// i-th element of this array is the set of addresses of words that comprise i-th state
    pub state_snapshots: Vec<HashSet<usize>>,
    /// operations that maps i-th state to i+1-st state
    pub operations: Vec<SpookupOp<F>>,
}

impl<F: TFelt> SpookupCircuit<F> {
    pub fn compute_execution_trace(&self, inputs: Vec<Vec<u32>>) -> Vec<Vec<u32>> {
        let n_inputs_global = inputs.len();
        assert!(n_inputs_global == self.state_snapshots[0].len());
        let l = inputs[0].len();
        for j in 1..inputs.len() {
            assert!(inputs[j].len() == l);
        }

        let mut result = inputs;

        for op in &self.operations {
            let n_inputs = op.inputs.len();
            let n_outputs = op.outputs.len();
            
            let inputs = op.inputs.iter().map(|&addr| {
                result.get(addr).unwrap_or_else(|| panic!("attempt to read from unknown address. should never happen."))
            }).collect_vec();

            let mut outputs : Vec<UninitArr<u32>> = vec![];
            (0..n_outputs).map(|_| outputs.push(UninitArr::new(l))).count(); // not calling it using vec![UninitArr::new(...)] because that would clone it

            let input_word_bitsizes = (0..n_inputs).map(|i| self.word_bitsizes[op.inputs[i]]).collect_vec();
            let output_word_bitsizes = (0..n_outputs).map(|i| self.word_bitsizes[op.outputs[i]]).collect_vec();

            let mut input_shifts = vec![0];
            for i in 0 .. n_inputs - 1 {
                input_shifts.push(input_shifts.last().unwrap() + input_word_bitsizes[i]);
            }

            let output_masks = output_word_bitsizes.iter().map(|bitsize| (1 << bitsize) - 1).collect_vec();

            #[cfg(not(feature = "parallel"))]
            let iter = (0..l).into_iter();
            #[cfg(feature = "parallel")]
            let iter = (0..l).into_par_iter();

            let output_ptrs = outputs.iter_mut().map(|o| o.as_shared_mut_ptr()).collect_vec();

            iter.map(|i| {
                let mut acc = inputs[0][i];
                for j in 1..n_inputs {
                    acc += (inputs[j][i]) << input_shifts[j];
                }
                let mut ret = op.op.apply(acc);
                for j in 0..n_outputs {
                    unsafe {
                        *output_ptrs[j].get_mut(i) = ret & output_masks[j];
                    }
                    ret >>= output_word_bitsizes[j];
                }
            }).count();

            for output in outputs {
                result.push(unsafe {output.assume_init()});
            }
        };

        result
    }
}