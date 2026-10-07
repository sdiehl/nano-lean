use bumpalo::Bump;
use num_bigint::BigUint;
use std::cell::{Cell, RefCell};
use std::ops::Deref;

const RETAINED_CHUNK_LIMIT: usize = 16 << 20;

#[derive(Default)]
pub struct Arena {
    bump: Bump,
    nat_bytes: Cell<usize>,
    // Boxes keep references stable when the ownership vector grows.
    #[allow(clippy::vec_box)]
    nats: RefCell<Vec<Box<BigUint>>>,
    epoch: u64,
}

impl Arena {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn alloc_nat(&self, value: BigUint) -> &BigUint {
        self.nat_bytes.set(self.nat_bytes.get().saturating_add(
            size_of::<BigUint>() + (value.bits().div_ceil(64) as usize).saturating_mul(8),
        ));
        let value = Box::new(value);
        let ptr = &*value as *const BigUint;
        self.nats.borrow_mut().push(value);
        // SAFETY: boxes never move their contents, and reset needs exclusive access.
        // The returned reference cannot outlive this arena or cross a reset.
        unsafe { &*ptr }
    }

    pub fn allocated_bytes(&self) -> usize {
        self.bump
            .allocated_bytes()
            .saturating_add(self.nat_bytes.get())
    }

    /// Bumped by every reset, so anything keyed to an older value is stale.
    pub fn epoch(&self) -> u64 {
        self.epoch
    }

    pub fn reset(&mut self) {
        self.epoch += 1;
        self.nats.get_mut().clear();
        self.nat_bytes.set(0);
        // Bump::reset keeps its largest chunk, so drop one a large declaration left behind.
        if self.bump.allocated_bytes() > RETAINED_CHUNK_LIMIT {
            self.bump = Bump::new();
        } else {
            self.bump.reset();
        }
    }
}

impl Deref for Arena {
    type Target = Bump;

    fn deref(&self) -> &Bump {
        &self.bump
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn integer_references_survive_growth_and_storage_is_reclaimed() {
        let mut arena = Arena::new();
        for _ in 0..4 {
            let first = arena.alloc_nat(BigUint::from(1u32) << 8192);
            for n in 0..1024u32 {
                arena.alloc_nat(BigUint::from(n) << 8192);
            }
            assert_eq!(first.bits(), 8193);
            assert_eq!(arena.nats.borrow().len(), 1025);
            arena.reset();
            assert!(arena.nats.borrow().is_empty());
        }
        arena.alloc_slice_fill_copy(17 << 20, 0u8);
        arena.reset();
        assert!(arena.allocated_bytes() < RETAINED_CHUNK_LIMIT);
    }
}
