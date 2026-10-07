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

/// Bound values, innermost first: cheap pushes over an interned frame that
/// closures capture and index directly.
#[derive(Clone, Copy)]
pub enum Env<'t> {
    Nil,
    Node(&'t EnvNode<'t>),
    Frame(&'t Frame<'t>),
}

pub struct EnvNode<'t> {
    pub head: V<'t>,
    pub tail: Env<'t>,
    pub open: bool,
    /// Nodes above the nearest frame, including this one.
    pub depth: u32,
    /// Values in the whole environment.
    pub len: u32,
}

/// `vals[i]` is de Bruijn index `i`.
pub struct Frame<'t> {
    pub vals: &'t [V<'t>],
    pub open: bool,
}

impl<'t> Env<'t> {
    pub const EMPTY: Self = Env::Nil;

    pub fn get(self, mut i: u16) -> Option<V<'t>> {
        let mut e = self;
        loop {
            match e {
                Env::Nil => return None,
                Env::Node(n) if i == 0 => return Some(n.head),
                Env::Node(n) => {
                    i -= 1;
                    e = n.tail;
                }
                Env::Frame(f) => return f.vals.get(usize::from(i)).copied(),
            }
        }
    }

    pub fn open(self) -> bool {
        match self {
            Env::Nil => false,
            Env::Node(n) => n.open,
            Env::Frame(f) => f.open,
        }
    }

    pub fn depth(self) -> u32 {
        match self {
            Env::Node(n) => n.depth,
            _ => 0,
        }
    }

    pub fn size(self) -> usize {
        match self {
            Env::Nil => 0,
            Env::Node(n) => n.len as usize,
            Env::Frame(f) => f.vals.len(),
        }
    }

    pub fn key(self) -> usize {
        match self {
            Env::Nil => 0,
            Env::Node(n) => n as *const EnvNode as usize,
            Env::Frame(f) => f as *const Frame as usize,
        }
    }

    /// All values, innermost first.
    pub fn iter(self) -> impl Iterator<Item = V<'t>> {
        let mut e = self;
        let mut at = 0;
        std::iter::from_fn(move || match e {
            Env::Nil => None,
            Env::Node(n) => {
                e = n.tail;
                Some(n.head)
            }
            Env::Frame(f) => {
                at += 1;
                f.vals.get(at - 1).copied()
            }
        })
    }
}

#[inline]
pub fn key(v: V<'_>) -> usize {
    v as *const Val as usize
}
