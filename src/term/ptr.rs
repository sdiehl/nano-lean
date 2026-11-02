use super::expr::{Expr, HAS_LOCAL, Meta, NLB_MASK};
use super::level::Level;
use super::name::{NameNode, StrNode};
use num_bigint::BigUint;
use std::fmt;
use std::marker::PhantomData;
use std::num::NonZeroU64;

macro_rules! thin {
    ($name:ident, $t:ty) => {
        #[derive(Clone, Copy, PartialEq, Eq, Hash)]
        pub struct $name<'a>(NonZeroU64, PhantomData<&'a $t>);

        impl<'a> $name<'a> {
            #[inline]
            pub fn new(r: &'a $t) -> Self {
                Self(NonZeroU64::new(r as *const $t as u64).unwrap(), PhantomData)
            }

            #[inline]
            #[allow(clippy::should_implement_trait)] // Returns the arena lifetime, independent of the handle borrow.
            pub fn as_ref(self) -> &'a $t {
                // SAFETY: built from a `&'a $t`, and the phantom keeps the borrow alive.
                unsafe { &*(self.0.get() as *const $t) }
            }
        }

        impl<'a> std::ops::Deref for $name<'a> {
            type Target = $t;
            #[inline]
            fn deref(&self) -> &$t {
                self.as_ref()
            }
        }

        impl fmt::Debug for $name<'_> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                fmt::Debug::fmt(self.as_ref(), f)
            }
        }
    };
}

thin!(NamePtr, NameNode<'a>);
thin!(LevelPtr, Level<'a>);
thin!(StringPtr, StrNode<'a>);
thin!(BigUintPtr, BigUint);

impl fmt::Display for NamePtr<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self.as_ref(), f)
    }
}

/// The tagged pointers below keep data in the top 16 bits, which holds while user space
/// addresses fit in 48 bits. That is the default on x86_64 and aarch64 for Linux, macOS and
/// Windows. Construction panics on a wider address, so a 57 bit process fails loudly instead
/// of truncating.
#[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
compile_error!("tagged pointers need a 64 bit target with 48 bit user addresses");

const ADDR: u64 = 0x0000_ffff_ffff_ffff;
const META_SHIFT: u32 = 48;

/// Pointer to an arena `Expr` with the loose bound variable count packed in the top 16 bits.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct ExprPtr<'a>(NonZeroU64, PhantomData<&'a Expr<'a>>);

impl<'a> ExprPtr<'a> {
    #[inline]
    pub fn new(r: &'a Expr<'a>, meta: Meta) -> Self {
        let addr = r as *const Expr<'a> as u64;
        assert!(addr & !ADDR == 0, "address wider than 48 bits");
        Self(
            NonZeroU64::new(addr | (u64::from(meta) << META_SHIFT))
                .expect("references are nonnull"),
            PhantomData,
        )
    }

    #[inline]
    pub fn meta(self) -> Meta {
        (self.0.get() >> META_SHIFT) as Meta
    }

    #[inline]
    pub fn nlb(self) -> u16 {
        self.meta() & NLB_MASK
    }

    #[inline]
    pub fn closed(self) -> bool {
        self.nlb() == 0
    }

    #[inline]
    pub fn has_local(self) -> bool {
        self.meta() & HAS_LOCAL != 0
    }

    #[inline]
    #[allow(clippy::should_implement_trait)] // Returns the arena lifetime, independent of the handle borrow.
    pub fn as_ref(self) -> &'a Expr<'a> {
        // SAFETY: the low 48 bits are the address of the `&'a Expr` this was built from.
        unsafe { &*((self.0.get() & ADDR) as *const Expr<'a>) }
    }
}

impl<'a> std::ops::Deref for ExprPtr<'a> {
    type Target = Expr<'a>;
    #[inline]
    fn deref(&self) -> &Expr<'a> {
        self.as_ref()
    }
}

impl fmt::Debug for ExprPtr<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self.as_ref(), f)
    }
}

/// Thin pointer to an interned slice of levels, length packed in the top 16 bits.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct LevelsPtr<'a>(u64, PhantomData<&'a [LevelPtr<'a>]>);

impl<'a> LevelsPtr<'a> {
    #[inline]
    pub fn new(s: &'a [LevelPtr<'a>]) -> Self {
        assert!(s.len() <= usize::from(u16::MAX), "too many universe levels");
        let addr = s.as_ptr() as u64;
        assert!(addr & !ADDR == 0, "address wider than 48 bits");
        Self(addr | ((s.len() as u64) << META_SHIFT), PhantomData)
    }

    #[inline]
    pub fn len(self) -> usize {
        (self.0 >> META_SHIFT) as usize
    }

    #[inline]
    pub fn is_empty(self) -> bool {
        self.len() == 0
    }

    #[inline]
    #[allow(clippy::should_implement_trait)] // Returns the arena lifetime, independent of the handle borrow.
    pub fn as_ref(self) -> &'a [LevelPtr<'a>] {
        // SAFETY: address and length are those of the `&'a` slice this was built from.
        unsafe { std::slice::from_raw_parts((self.0 & ADDR) as *const LevelPtr<'a>, self.len()) }
    }
}

impl<'a> std::ops::Deref for LevelsPtr<'a> {
    type Target = [LevelPtr<'a>];
    #[inline]
    fn deref(&self) -> &[LevelPtr<'a>] {
        self.as_ref()
    }
}

impl fmt::Debug for LevelsPtr<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self.as_ref(), f)
    }
}
