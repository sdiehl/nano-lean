mod conv;
mod decl;
mod eval;
mod infer;
mod intern;
mod session;
mod stats;
mod tables;
#[cfg(test)]
mod tests;
pub mod value;
mod whnf;

use crate::checker::Limits;
use crate::checker::env::Decls;
use crate::resource::Budget;
#[cfg(feature = "vstats")]
use crate::term::FxHashMap;
use crate::term::arena::Arena;
use crate::term::ctx::Ctx;
use crate::term::decl::Declar;
use crate::term::intern::{Names, Store};
use crate::term::level::Level;
use crate::term::ptr::{LevelPtr, LevelsPtr, NamePtr};
use crate::{ensure, reject};
use smallvec::SmallVec;
#[cfg(feature = "vstats")]
use stats::Stats;
use stats::stat;
use std::mem::{take, transmute};
use tables::{POOL, Tables};
use value::*;

pub(crate) use decl::{RecCheck, check_recursor};
pub use session::{BRIDGED, Session, check};
#[cfg(feature = "vstats")]
pub use stats::{RESETS, TOTAL, report};

const ARENA_STRIDE_MASK: u64 = 1023;
const INCLUDED_MAX: usize = 8;

/// Probe budget ran out, never a semantic answer.
#[derive(Debug)]
pub struct Stop;
pub type R<T> = Result<T, Stop>;

struct Vc<'t, 'a: 't> {
    pub ctx: Ctx<'t, 'a>,
    names: Names<'t>,
    uparams: LevelsPtr<'t>,
    limit: u32,
    limits: Limits,
    steps_left: u64,
    probe_remaining: Option<u32>,
    next_local: u32,
    depth: usize,
    /// Bumped whenever a check depends on the universe parameters in scope.
    scoped: u64,
    included: SmallVec<[(LevelsPtr<'t>, bool); 4]>,
    id: Sub<'t>,
    dummy: V<'t>,
    t: Tables<'t>,
    base: usize,
    #[cfg(feature = "vstats")]
    pub stats: Stats,
    #[cfg(feature = "vstats")]
    pub unfolded: FxHashMap<NamePtr<'t>, u64>,
}

impl Drop for Vc<'_, '_> {
    fn drop(&mut self) {
        let t = take(&mut self.t).recycle();
        POOL.with(|p| *p.borrow_mut() = Some(t));
    }
}

impl<'t, 'a: 't> Vc<'t, 'a> {
    pub fn new(store: &'a Store<'a>, arena: &'t Arena, limits: Limits) -> Self {
        let mut ctx = Ctx::new(store, arena);
        let e = ctx.levels(&[]);
        let z = ctx.zero();
        let dummy = arena.alloc(Val {
            k: K::Sort(z),
            open: false,
        });
        Self {
            names: store.names,
            ctx,
            uparams: e,
            limit: 0,
            limits,
            steps_left: limits.steps,
            probe_remaining: None,
            next_local: 0,
            depth: 0,
            scoped: 0,
            included: SmallVec::new(),
            id: Sub { ks: e, vs: e },
            dummy,
            // SAFETY: pooled tables are empty.
            t: POOL
                .with(|p| p.borrow_mut().take())
                .map_or_else(Default::default, |t| unsafe {
                    transmute::<Tables<'static>, Tables<'t>>(t)
                }),
            base: arena.allocated_bytes(),
            #[cfg(feature = "vstats")]
            stats: Stats::default(),
            #[cfg(feature = "vstats")]
            unfolded: Default::default(),
        }
    }

    fn used(&self) -> usize {
        self.ctx.arena.allocated_bytes() - self.base
    }

    fn ensure_arena(&self) {
        if self.used() > self.limits.arena_bytes {
            Budget::Arena.decline();
        }
    }

    #[inline]
    pub(crate) fn work(&mut self) {
        if self.steps_left & ARENA_STRIDE_MASK >= 2 {
            self.steps_left -= 1;
        } else {
            self.work_slow();
        }
    }

    #[cold]
    #[inline(never)]
    fn work_slow(&mut self) {
        self.spend_slow();
    }

    #[inline]
    pub(crate) fn tick(&mut self) -> R<()> {
        if self.steps_left & ARENA_STRIDE_MASK >= 2 {
            self.steps_left -= 1;
            return Ok(());
        }
        self.tick_slow()
    }

    #[inline(never)]
    fn tick_slow(&mut self) -> R<()> {
        self.spend_slow();
        Ok(())
    }

    #[inline(always)]
    fn spend_slow(&mut self) {
        if self.steps_left == 0 {
            Budget::Work.decline();
        }
        self.steps_left -= 1;
        if self.steps_left & ARENA_STRIDE_MASK == 0 {
            self.ensure_arena();
        }
    }

    pub(crate) fn sub(&self, ks: LevelsPtr<'t>, vs: LevelsPtr<'t>) -> Sub<'t> {
        if ks.is_empty() || ks == vs {
            self.id
        } else {
            Sub { ks, vs }
        }
    }

    pub(crate) fn fresh_local(&mut self, ty: V<'t>) -> V<'t> {
        self.next_local += 1;
        let id = self.next_local;
        // Ids are never reused, so interning could only miss.
        stat!(self, vals);
        self.ctx.arena.alloc(Val {
            k: K::Neu(Head::Local(id, ty), &[]),
            open: true,
        })
    }

    pub(crate) fn konst0(&mut self, n: Option<NamePtr<'t>>) -> V<'t> {
        let Some(n) = n else {
            reject!("missing builtin constant")
        };
        let e = self.ctx.levels(&[]);
        self.mk(K::Neu(Head::Const(n, e), &[]), false)
    }

    fn within(&mut self, ls: LevelsPtr<'t>) -> bool {
        if ls.is_empty() || ls == self.uparams {
            return true;
        }
        if let Some(&(_, ok)) = self.included.iter().find(|w| w.0 == ls) {
            return ok;
        }
        let ok = ls.iter().all(|l| self.uparams.contains(l));
        if self.included.len() < INCLUDED_MAX {
            self.included.push((ls, ok));
        }
        ok
    }

    fn check_level(&mut self, l: LevelPtr<'t>) {
        fn has_param(l: LevelPtr<'_>) -> bool {
            match *l {
                Level::Zero => false,
                Level::Succ(l, _) => has_param(l),
                Level::Max(l, r, _) | Level::IMax(l, r, _) => has_param(l) || has_param(r),
                Level::Param(..) => true,
            }
        }
        if has_param(l) {
            self.scoped += 1;
            ensure!(l.params_in(self.uparams), "undeclared universe parameter");
        }
    }
}

impl<'t, 'a: 't> Decls<'t> for Vc<'t, 'a> {
    #[inline]
    fn declar(&self, n: NamePtr<'t>) -> Option<Declar<'t>> {
        let i = n.decl_idx()?;
        (i < self.limit).then(|| self.ctx.store.declars[i as usize])
    }

    #[inline]
    fn names(&self) -> &Names<'t> {
        &self.names
    }
}
