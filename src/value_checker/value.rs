use crate::term::ptr::{ExprPtr, LevelPtr, LevelsPtr, NamePtr};
use num_bigint::BigUint;
use std::cell::Cell;

pub type V<'t> = &'t Val<'t>;

pub struct Val<'t> {
    pub k: K<'t>,
    /// May mention a local, over-approximated through closure environments.
    pub open: bool,
    pub memo: Cell<Option<&'t Memo<'t>>>,
}

impl<'t> Val<'t> {
    pub fn new(k: K<'t>, open: bool) -> Self {
        Self {
            k,
            open,
            memo: Cell::new(None),
        }
    }
}

/// Results cached on a value, valid only for the checker whose generation they carry.
#[derive(Default)]
pub struct Memo<'t> {
    pub epoch: Cell<u32>,
    pub whnf_core: Cell<Option<V<'t>>>,
    pub whnf: Cell<Option<V<'t>>>,
    pub unfold: Cell<Option<Option<V<'t>>>>,
    pub ty: Cell<Option<V<'t>>>,
}

impl Memo<'_> {
    pub fn reset(&self, epoch: u32) {
        self.epoch.set(epoch);
        self.whnf_core.set(None);
        self.whnf.set(None);
        self.unfold.set(None);
        self.ty.set(None);
    }
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
    /// A let-bound local carries its value and unfolds only at the head.
    Local(u32, V<'t>, Option<V<'t>>),
    Const(NamePtr<'t>, LevelsPtr<'t>),
    Proj(NamePtr<'t>, u16, V<'t>),
}

/// A typed closure yields the type of the body's value, the codomain of a lambda's type.
#[derive(Clone, Copy)]
pub struct Clo<'t> {
    pub env: Env<'t>,
    pub sub: Sub<'t>,
    pub body: ExprPtr<'t>,
    pub typed: bool,
}

pub struct Lazy<'t> {
    pub env: Env<'t>,
    pub sub: Sub<'t>,
    pub e: ExprPtr<'t>,
    pub val: Cell<Option<V<'t>>>,
}

/// Normalized so identity has one form.
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

/// Cheap pushes over an interned frame. One pointer wide.
#[derive(Clone, Copy)]
pub struct Env<'t>(Option<&'t EnvObj<'t>>);

pub enum EnvObj<'t> {
    Node(EnvNode<'t>),
    Frame(Frame<'t>),
}

pub enum View<'t> {
    Nil,
    Node(&'t EnvNode<'t>),
    Frame(&'t Frame<'t>),
}

pub struct EnvNode<'t> {
    pub head: V<'t>,
    pub tail: Env<'t>,
    /// The frame under the node run, so lookups past `depth` index it directly.
    pub base: Env<'t>,
    pub depth: u32,
    pub open: bool,
}

impl<'t> EnvNode<'t> {
    /// SAFETY: the tail must be a node.
    #[inline(always)]
    unsafe fn next(&self) -> &'t EnvNode<'t> {
        match self.tail.0 {
            Some(EnvObj::Node(m)) => m,
            _ => unsafe { std::hint::unreachable_unchecked() },
        }
    }

    /// The node `i` links down, unrolled by two since deep walks dominate the steps.
    #[inline]
    pub fn nth_node(&'t self, i: u16) -> &'t EnvNode<'t> {
        debug_assert!(u32::from(i) < self.depth);
        let (mut n, mut k) = (self, u32::from(i));
        // SAFETY: `depth` counts the nodes above the base, so `i < depth` stays on nodes.
        unsafe {
            while k >= 2 {
                n = n.next().next();
                k -= 2;
            }
            if k != 0 {
                n = n.next();
            }
        }
        n
    }

    #[inline]
    pub fn below(&self, i: u16) -> Option<V<'t>> {
        self.base_vals()
            .get(usize::from(i) - self.depth as usize)
            .copied()
    }

    #[inline]
    pub fn base_vals(&self) -> &'t [V<'t>] {
        match self.base.0 {
            Some(EnvObj::Frame(f)) => f.vals,
            _ => &[],
        }
    }
}

pub struct Frame<'t> {
    pub vals: &'t [V<'t>],
    pub open: bool,
}

impl<'t> Env<'t> {
    pub const EMPTY: Self = Env(None);

    pub fn new(o: &'t EnvObj<'t>) -> Self {
        Env(Some(o))
    }

    #[inline]
    pub fn view(self) -> View<'t> {
        match self.0 {
            None => View::Nil,
            Some(EnvObj::Node(n)) => View::Node(n),
            Some(EnvObj::Frame(f)) => View::Frame(f),
        }
    }

    #[inline]
    pub fn get(self, i: u16) -> Option<V<'t>> {
        match self.0 {
            None => None,
            Some(EnvObj::Frame(f)) => f.vals.get(usize::from(i)).copied(),
            Some(EnvObj::Node(n)) if u32::from(i) < n.depth => Some(n.nth_node(i).head),
            Some(EnvObj::Node(n)) => n.below(i),
        }
    }

    /// The node `d` links down and its head.
    ///
    /// # Safety
    /// `self` must be a node and `d` below its depth.
    #[inline]
    pub unsafe fn down(self, d: u16) -> (Self, V<'t>) {
        let Some(EnvObj::Node(n)) = self.0 else {
            unsafe { std::hint::unreachable_unchecked() }
        };
        if d == 0 {
            return (self, n.head);
        }
        let p = n.nth_node(d - 1);
        // SAFETY: `d` is below the depth, so the link under `p` is a node.
        (p.tail, unsafe { p.next() }.head)
    }

    pub fn open(self) -> bool {
        match self.view() {
            View::Nil => false,
            View::Node(n) => n.open,
            View::Frame(f) => f.open,
        }
    }

    pub fn depth(self) -> u32 {
        match self.view() {
            View::Node(n) => n.depth,
            _ => 0,
        }
    }

    pub fn size(self) -> usize {
        match self.view() {
            View::Nil => 0,
            View::Node(n) => n.depth as usize + n.base_vals().len(),
            View::Frame(f) => f.vals.len(),
        }
    }

    pub fn key(self) -> usize {
        self.0.map_or(0, |o| o as *const EnvObj as usize)
    }

    pub fn iter(self) -> impl Iterator<Item = V<'t>> {
        let mut e = self;
        let mut at = 0;
        std::iter::from_fn(move || match e.view() {
            View::Nil => None,
            View::Node(n) => {
                e = n.tail;
                Some(n.head)
            }
            View::Frame(f) => {
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

const _: () = assert!(size_of::<EnvObj<'_>>() == 32);
