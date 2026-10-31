mod conv;
mod decl;
mod derive;
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
use crate::resource::{Budget, stack_exhausted, stack_floor};
#[cfg(feature = "vstats")]
use crate::term::FxHashMap;
use crate::term::arena::Arena;
use crate::term::ctx::Ctx;
use crate::term::decl::Declar;
use crate::term::intern::{Names, Store};
use crate::term::level::Level;
use crate::term::ops::LEVEL_FORM;
use crate::term::outcome::{Decline, Failure, R, Stop};
use crate::term::ptr::{LevelPtr, LevelsPtr, NamePtr};
use crate::{ensure, reject};
use smallvec::SmallVec;
#[cfg(feature = "vstats")]
use stats::Stats;
use stats::{bytes, stat};
use std::fmt;
use std::mem::{take, transmute};
use tables::{POOL, Tables};
use value::{Head, K, Sub, V, Val};

pub(crate) use decl::{RecCheck, check_recursor};
pub use session::{BRIDGED, Session, check};
#[cfg(feature = "vstats")]
pub use stats::{RESETS, TOTAL, report};

const ARENA_STRIDE_MASK: u64 = 1023;
const INCLUDED_MAX: usize = 8;

struct Vc<'t, 'a: 't> {
    pub ctx: Ctx<'t, 'a>,
    names: Names<'t>,
    uparams: LevelsPtr<'t>,
    limit: u32,
    limits: Limits,
    steps_left: u64,
    /// The suspended outer step budget while an argument probe runs on its own.
    probe_outer: Option<u64>,
    next_local: u32,
    depth: usize,
    /// Bumped whenever a check depends on the universe parameters in scope.
    scoped: u64,
    included: SmallVec<[(LevelsPtr<'t>, bool); 4]>,
    id: Sub<'t>,
    dummy: V<'t>,
    t: Tables<'t>,
    base: usize,
    floor: usize,
    fail: Option<Failure>,
    /// Set while a rule is derived over locals whose types are placeholders.
    deriving: bool,
    derivations: u32,
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
            probe_outer: None,
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
            base: arena.used_bytes(),
            floor: stack_floor(),
            fail: None,
            deriving: false,
            derivations: 0,
            #[cfg(feature = "vstats")]
            stats: Stats::default(),
            #[cfg(feature = "vstats")]
            unfolded: Default::default(),
        }
    }

    fn used(&self) -> usize {
        self.ctx.arena.used_bytes() - self.base
    }

    #[cold]
    #[inline(never)]
    fn reject(&mut self, msg: fmt::Arguments<'_>) -> Stop {
        self.fail = Some(Failure::Rejected(msg.to_string()));
        Stop
    }

    #[cold]
    #[inline(never)]
    fn decline(&mut self, budget: Budget) -> Stop {
        self.fail = Some(Failure::Declined(Decline::Exhausted(budget)));
        Stop
    }

    /// The failure behind a `Stop` that reached the top of the check.
    fn failure(&mut self) -> Failure {
        Failure::escaped(&mut self.fail)
    }

    #[inline(always)]
    fn guard(&mut self) -> R<()> {
        if stack_exhausted(self.floor) {
            return Err(self.decline(Budget::Stack));
        }
        Ok(())
    }

    fn ensure_arena(&mut self) -> R<()> {
        if self.used() > self.limits.arena_bytes {
            return Err(self.decline(Budget::Arena));
        }
        Ok(())
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
        if self.steps_left == 0 {
            return Err(match self.probe_outer {
                Some(_) => Stop,
                None => self.decline(Budget::Work),
            });
        }
        self.steps_left -= 1;
        if self.steps_left & ARENA_STRIDE_MASK == 0 {
            self.ensure_arena()?;
        }
        Ok(())
    }

    fn level_eq(&mut self, a: LevelPtr<'t>, b: LevelPtr<'t>) -> R<bool> {
        let Some(r) = self.ctx.try_level_eq(a, b) else {
            reject!(self, "{LEVEL_FORM}")
        };
        Ok(r)
    }

    fn levels_eq(&mut self, a: LevelsPtr<'t>, b: LevelsPtr<'t>) -> R<bool> {
        let Some(r) = self.ctx.try_levels_eq(a, b) else {
            reject!(self, "{LEVEL_FORM}")
        };
        Ok(r)
    }

    pub(crate) fn sub(&self, ks: LevelsPtr<'t>, vs: LevelsPtr<'t>) -> Sub<'t> {
        if ks.is_empty() || ks == vs {
            self.id
        } else {
            Sub { ks, vs }
        }
    }

    pub(crate) fn fresh_local(&mut self, ty: V<'t>) -> V<'t> {
        self.local(ty, None)
    }

    pub(crate) fn local(&mut self, ty: V<'t>, val: Option<V<'t>>) -> V<'t> {
        self.next_local += 1;
        let id = self.next_local;
        // Ids are never reused, so interning could only miss.
        stat!(self, vals);
        bytes!(self, b_val, size_of::<Val>());
        self.ctx.arena.alloc(Val {
            k: K::Neu(Head::Local(id, ty, val), &[]),
            open: true,
        })
    }

    pub(crate) fn konst0(&mut self, n: Option<NamePtr<'t>>) -> R<V<'t>> {
        let Some(n) = n else {
            reject!(self, "missing builtin constant")
        };
        let e = self.ctx.levels(&[]);
        Ok(self.mk(K::Neu(Head::Const(n, e), &[]), false))
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

    fn check_level(&mut self, l: LevelPtr<'t>) -> R<()> {
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
            ensure!(
                self,
                l.params_in(self.uparams),
                "undeclared universe parameter"
            );
        }
        Ok(())
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
