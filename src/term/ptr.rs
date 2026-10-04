use super::expr::Expr;
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

const ADDR: u64 = 0x0000_ffff_ffff_ffff;

/// Pointer to an arena `Expr` with the loose bound variable count packed in the top 16 bits.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct ExprPtr<'a>(NonZeroU64, PhantomData<&'a Expr<'a>>);

impl<'a> ExprPtr<'a> {
    #[inline]
    pub fn new(r: &'a Expr<'a>, meta: u16) -> Self {
        let addr = r as *const Expr<'a> as u64;
        debug_assert_eq!(addr & !ADDR, 0);
        Self(
            NonZeroU64::new(addr | (u64::from(meta) << 48)).unwrap(),
            PhantomData,
        )
    }

    #[inline]
    pub fn meta(self) -> u16 {
        (self.0.get() >> 48) as u16
    }

    /// Number of loose bound variables: `Var(i)` occurs loose only if `i < nlb`.
    #[inline]
    pub fn nlb(self) -> u16 {
        self.meta() & 0x7fff
    }

    #[inline]
    pub fn closed(self) -> bool {
        self.nlb() == 0
    }

    #[inline]
    pub fn has_local(self) -> bool {
        self.meta() & 0x8000 != 0
    }

    #[inline]
    #[allow(clippy::should_implement_trait)] // Returns the arena lifetime, independent of the handle borrow.
    pub fn as_ref(self) -> &'a Expr<'a> {
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
        assert!(s.len() < 1 << 16, "too many universe levels");
        Self(s.as_ptr() as u64 | ((s.len() as u64) << 48), PhantomData)
    }

    #[inline]
    pub fn len(self) -> usize {
        (self.0 >> 48) as usize
    }

    #[inline]
    pub fn is_empty(self) -> bool {
        self.len() == 0
    }

    #[inline]
    #[allow(clippy::should_implement_trait)] // Returns the arena lifetime, independent of the handle borrow.
    pub fn as_ref(self) -> &'a [LevelPtr<'a>] {
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
