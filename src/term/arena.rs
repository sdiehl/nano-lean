//! Term storage with owned heap buffers for big integers.

use bumpalo::Bump;
use num_bigint::BigUint;
use std::cell::{Cell, RefCell};
use std::ops::Deref;

#[derive(Default)]
pub struct Arena {
    bump: Bump,
    nat_bytes: Cell<usize>,
    // Boxes keep references stable when the ownership vector grows.
    #[allow(clippy::vec_box)]
    nats: RefCell<Vec<Box<BigUint>>>,
}

impl Arena {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn alloc_nat(&self, value: BigUint) -> &BigUint {
        self.nat_bytes.set(self.nat_bytes.get().saturating_add(
            std::mem::size_of::<BigUint>() + (value.bits().div_ceil(64) as usize).saturating_mul(8),
        ));
        let value = Box::new(value);
        let ptr = &*value as *const BigUint;
        self.nats.borrow_mut().push(value);
        // SAFETY: boxes never move their contents. The vector only appends through
        // shared references; reset requires exclusive access to the whole arena.
        // The returned reference cannot outlive this arena or cross a reset.
        unsafe { &*ptr }
    }

    /// Bump chunks plus the live integer payloads (excluding allocator overhead).
    pub fn allocated_bytes(&self) -> usize {
        self.bump
            .allocated_bytes()
            .saturating_add(self.nat_bytes.get())
    }

    pub fn reset(&mut self) {
        self.nats.get_mut().clear();
        self.nat_bytes.set(0);
        // Bump::reset retains its largest chunk. Avoid carrying a large
        // declaration's high-water allocation through every subsequent check.
        if self.bump.allocated_bytes() > 16 << 20 {
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
        assert!(arena.allocated_bytes() < 16 << 20);
    }
}
