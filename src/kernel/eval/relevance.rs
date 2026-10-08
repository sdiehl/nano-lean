use crate::kernel::prelude::*;

#[derive(Clone, Copy, Debug, Default)]
pub(in crate::kernel) struct Summary {
    pub proofs: u64,
    pub proof_results: u64,
    pub data_results: u64,
}
impl Summary {
    pub(super) fn proof_argument(self, index: usize) -> bool {
        index < 64 && self.proofs & (1 << index) != 0
    }
    pub(super) fn result(self, arity: usize) -> Option<bool> {
        if arity >= 64 {
            return None;
        }
        if self.proof_results & (1 << arity) != 0 {
            Some(true)
        } else if self.data_results & (1 << arity) != 0 {
            Some(false)
        } else {
            None
        }
    }
    pub(super) fn set_result(&mut self, arity: usize, level: &Level) -> Result<()> {
        if arity < 64 {
            if level.equivalent(&Level::Nat(0))? {
                self.proof_results |= 1 << arity;
            } else if positive(level) {
                self.data_results |= 1 << arity;
            }
        }
        Ok(())
    }
}

// Only a universally positive level rules out proof equality, since nonzero can become zero.
fn positive(level: &Level) -> bool {
    match level {
        Level::Nat(n) => *n > 0,
        Level::Succ(_) => true,
        Level::Max(a, b) => positive(a) || positive(b),
        Level::IMax(_, b) => positive(b),
        Level::Param(_) => false,
    }
}
