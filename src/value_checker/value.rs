//! Semantic values. Syntax stays in the term store; values live in the
//! per-declaration arena and are compared by pointer in caches.

use crate::term::ptr::{ExprPtr, LevelPtr, LevelsPtr, NamePtr};
use num_bigint::BigUint;
use std::cell::Cell;

pub type V<'t> = &'t Val<'t>;

pub struct Val<'t> {
    pub k: K<'t>,
    /// May mention a local. Over-approximates through closure environments.
    pub open: bool,
}

#[derive(Clone, Copy)]
pub enum K<'t> {
    Sort(LevelPtr<'t>),
    Pi(V<'t>, Clo<'t>),
    Lam(&'t Lazy<'t>, Clo<'t>),
    Neu(Head<'t>, &'t [V<'t>]),
    Nat(&'t BigUint),
    Str(&'t str),
}

#[derive(Clone, Copy)]
pub enum Head<'t> {
    Local(u32, V<'t>),
    Const(NamePtr<'t>, LevelsPtr<'t>),
    Proj(NamePtr<'t>, u16, V<'t>),
}

/// A body awaiting one argument. A typed closure yields the type of the
/// body's value instead of the value: it is the codomain of a lambda's type.
#[derive(Clone, Copy)]
pub struct Clo<'t> {
    pub env: Env<'t>,
    pub sub: Sub<'t>,
    pub body: ExprPtr<'t>,
    pub typed: bool,
}

/// A lambda domain, evaluated at most once and only when needed.
pub struct Lazy<'t> {
    pub env: Env<'t>,
    pub sub: Sub<'t>,
    pub e: ExprPtr<'t>,
    pub val: Cell<Option<V<'t>>>,
}

/// Universe instantiation `ks := vs`, normalized so identity has one form.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Sub<'t> {
    pub ks: LevelsPtr<'t>,
    pub vs: LevelsPtr<'t>,
}

impl Sub<'_> {
    pub fn is_id(self) -> bool {
        self.ks.is_empty()
    }
}

#[derive(Clone, Copy)]
pub struct Env<'t>(pub Option<&'t EnvNode<'t>>);

pub struct EnvNode<'t> {
    pub head: V<'t>,
    pub tail: Env<'t>,
    pub open: bool,
}

impl<'t> Env<'t> {
    pub const EMPTY: Self = Env(None);

    pub fn get(self, mut i: u16) -> Option<V<'t>> {
        let mut e = self.0;
        while let Some(n) = e {
            if i == 0 {
                return Some(n.head);
            }
            i -= 1;
            e = n.tail.0;
        }
        None
    }

    pub fn open(self) -> bool {
        self.0.is_some_and(|n| n.open)
    }

    pub fn key(self) -> usize {
        self.0.map_or(0, |n| n as *const EnvNode as usize)
    }
}

#[inline]
pub fn key(v: V<'_>) -> usize {
    v as *const Val as usize
}
