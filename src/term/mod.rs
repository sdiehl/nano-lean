//! Arena-allocated, hash-consed de Bruijn terms shared by the importer and the checker.

pub mod ctx;
pub mod decl;
pub mod expr;
pub mod intern;
pub mod level;
pub mod name;
pub mod ops;
pub mod outcome;
pub mod ptr;

pub type FxHashMap<K, V> = std::collections::HashMap<K, V, rustc_hash::FxBuildHasher>;
pub type FxHashSet<K> = std::collections::HashSet<K, rustc_hash::FxBuildHasher>;

/// Structural hasher for interned nodes. Each word is multiplied and folded
/// before the next is absorbed, so hashes of pointer tuples stay nonlinear
/// (FxHasher is linear in its inputs and collides on large arenas).
#[derive(Default)]
pub struct MixHasher(u64);

impl MixHasher {
    #[inline]
    fn absorb(&mut self, x: u64) {
        let h = (self.0 ^ x).wrapping_mul(0x9e37_79b9_7f4a_7c15);
        self.0 = h ^ (h >> 29);
    }
}

impl std::hash::Hasher for MixHasher {
    #[inline]
    fn write(&mut self, bytes: &[u8]) {
        let mut chunks = bytes.chunks_exact(8);
        for c in &mut chunks {
            self.absorb(u64::from_le_bytes(c.try_into().unwrap()));
        }
        let mut tail = [0u8; 8];
        tail[..chunks.remainder().len()].copy_from_slice(chunks.remainder());
        self.absorb(u64::from_le_bytes(tail) ^ (bytes.len() as u64) << 56);
    }

    #[inline]
    fn write_u8(&mut self, x: u8) {
        self.absorb(u64::from(x));
    }

    #[inline]
    fn write_u16(&mut self, x: u16) {
        self.absorb(u64::from(x));
    }

    #[inline]
    fn write_u32(&mut self, x: u32) {
        self.absorb(u64::from(x));
    }

    #[inline]
    fn write_u64(&mut self, x: u64) {
        self.absorb(x);
    }

    #[inline]
    fn write_usize(&mut self, x: usize) {
        self.absorb(x as u64);
    }

    #[inline]
    fn finish(&self) -> u64 {
        let mut h = self.0;
        h ^= h >> 33;
        h = h.wrapping_mul(0xff51_afd7_ed55_8ccd);
        h ^ (h >> 33)
    }
}

#[macro_export]
macro_rules! hash64 {
    ($($x:expr),* $(,)?) => {{
        use std::hash::{Hash, Hasher};
        let mut h = $crate::term::MixHasher::default();
        $( ($x).hash(&mut h); )*
        h.finish()
    }};
}
