use super::tables::{Mode, Scoped};
use super::value::{Env, K, Sub, V};
use super::{R, Vc};
use crate::checker::Limits;
use crate::ensure;
use crate::term::ctx::Ctx;
use crate::term::decl::Declar;
use crate::term::expr::Expr;
use crate::term::outcome::Failure;
use crate::term::ptr::{ExprPtr, LevelPtr, LevelsPtr};
use smallvec::SmallVec;
use std::mem::swap;

impl<'t, 'a: 't> Vc<'t, 'a> {
    pub(super) fn check(&mut self, idx: u32) -> Result<(), Failure> {
        self.check_in(idx).map_err(|_| self.failure())
    }

    fn check_in(&mut self, idx: u32) -> R<()> {
        self.ensure_arena()?;
        let d = self.ctx.store.declars[idx as usize];
        self.uparams = d.uparams();
        self.included.clear();
        self.limit = idx;
        match d {
            Declar::Axiom(i) => {
                self.check_type(i.ty)?;
            }
            Declar::Def(i, v, _) | Declar::Opaque(i, v) => {
                self.check_telescope(i.ty)?;
                self.check_value(v, i.ty)?;
            }
            Declar::Thm(i, v) => {
                let l = self.check_telescope(i.ty)?;
                let z = self.ctx.zero();
                ensure!(
                    self,
                    self.level_eq(l, z)?,
                    "theorem type is not a proposition"
                );
                self.check_value(v, i.ty)?;
            }
            _ => unreachable!("bridged declaration"),
        }
        Ok(())
    }

    fn check_type(&mut self, ty: ExprPtr<'t>) -> R<LevelPtr<'t>> {
        let id = self.id;
        let s = self.infer(Env::EMPTY, id, ty, Mode::Check)?;
        self.ensure_sort(s)
    }

    /// Walks Pi binders under canonical locals so the value check reuses the type check's caches.
    fn check_telescope(&mut self, ty: ExprPtr<'t>) -> R<LevelPtr<'t>> {
        if !ty.closed()
            || !matches!(*ty, Expr::Pi { .. })
            || self.t.infer_closed[Mode::Check].contains_key(&(ty, self.id))
        {
            return self.check_type(ty);
        }
        self.restoring_depth(|vc| vc.check_telescope_in(ty))
    }

    fn check_telescope_in(&mut self, ty: ExprPtr<'t>) -> R<LevelPtr<'t>> {
        let id = self.id;
        let mark = self.scoped;
        let (mut env, mut e) = (Env::EMPTY, ty);
        let mut sorts = SmallVec::<[LevelPtr<'t>; 8]>::new();
        while let Expr::Pi { ty: b, body, .. } = *e {
            self.tick()?;
            let s = self.infer(env, id, b, Mode::Check)?;
            sorts.push(self.ensure_sort(s)?);
            let dom = self.eval(env, id, b)?;
            let x = self.binder_local(dom);
            env = self.push(env, x);
            e = body;
        }
        let s = self.infer(env, id, e, Mode::Check)?;
        let mut l = self.ensure_sort(s)?;
        for &s1 in sorts.iter().rev() {
            l = self.ctx.imax(s1, l);
        }
        let t = self.mk(K::Sort(l), false);
        let uparams = if self.scoped == mark {
            LevelsPtr::new(&[])
        } else {
            self.uparams
        };
        self.t.infer_closed[Mode::Check].insert((ty, id), Scoped { ty: t, uparams });
        Ok(l)
    }

    /// A lambda domain equal to the type's own domain needs no check since the type is well formed.
    fn check_value(&mut self, v: ExprPtr<'t>, ty: ExprPtr<'t>) -> R<()> {
        self.restoring_depth(|vc| vc.check_value_in(v, ty))
    }

    fn check_value_in(&mut self, mut v: ExprPtr<'t>, mut ty: ExprPtr<'t>) -> R<()> {
        let id = self.id;
        let mut env = Env::EMPTY;
        let mut doms = SmallVec::<[(V<'t>, Env<'t>, ExprPtr<'t>); 8]>::new();
        while let (
            Expr::Lam { ty: a, body, .. },
            Expr::Pi {
                ty: b, body: tb, ..
            },
        ) = (*v, *ty)
        {
            let dom = self.eval(env, id, a)?;
            if a != b {
                let s = self.infer(env, id, a, Mode::Check)?;
                self.ensure_sort(s)?;
                doms.push((dom, env, b));
            }
            let x = self.binder_local(dom);
            env = self.push(env, x);
            (v, ty) = (body, tb);
        }
        let vt = self.infer(env, id, v, Mode::Check)?;
        for (dom, env, b) in doms {
            let d = self.eval(env, id, b)?;
            ensure!(self, self.def_eq(dom, d)?, "declaration type mismatch");
        }
        let tv = self.eval(env, id, ty)?;
        ensure!(self, self.def_eq(vt, tv)?, "declaration type mismatch");
        Ok(())
    }
}

#[derive(Clone, Copy)]
pub(crate) enum RecCheck<'t> {
    Sort(ExprPtr<'t>),
    /// A constructor type whose fields, the binders past the parameter count, must stay within
    /// the inductive's universe.
    Ctor(ExprPtr<'t>, u16, LevelPtr<'t>),
    Type(ExprPtr<'t>, ExprPtr<'t>),
    Rule(ExprPtr<'t>, ExprPtr<'t>),
}

impl<'t, 'a: 't> Vc<'t, 'a> {
    fn check_ctor_in(&mut self, ty: ExprPtr<'t>, np: u16, bound: LevelPtr<'t>) -> R<()> {
        let id = self.id;
        let (mut env, mut e, mut k) = (Env::EMPTY, ty, 0);
        while let Expr::Pi { ty: b, body, .. } = *e {
            self.tick()?;
            let s = self.infer(env, id, b, Mode::Check)?;
            let l = self.ensure_sort(s)?;
            if k >= np {
                ensure!(
                    self,
                    self.leq(l, bound)?,
                    "constructor field universe exceeds inductive universe"
                );
            }
            let dom = self.eval(env, id, b)?;
            let x = self.binder_local(dom);
            env = self.push(env, x);
            e = body;
            k += 1;
        }
        let s = self.infer(env, id, e, Mode::Check)?;
        self.ensure_sort(s)?;
        Ok(())
    }

    fn rec_check(&mut self, c: RecCheck<'t>) -> R<()> {
        let id = self.id;
        match c {
            RecCheck::Sort(ty) => {
                self.check_type(ty)?;
            }
            RecCheck::Ctor(ty, np, bound) => {
                self.restoring_depth(|vc| vc.check_ctor_in(ty, np, bound))?;
            }
            // A recursor identical to the one built from the checked specification is accepted as
            // built, the way the Lean kernel trusts its own; anything else is checked as a term.
            RecCheck::Type(ty, want) => {
                if !ty.same(want) {
                    self.check_type(ty)?;
                    let a = self.eval(Env::EMPTY, id, ty)?;
                    let b = self.eval(Env::EMPTY, id, want)?;
                    ensure!(self, self.def_eq(a, b)?, "incorrect recursor type");
                }
            }
            RecCheck::Rule(rhs, want) => {
                if !rhs.same(want) {
                    let wt = self.infer(Env::EMPTY, id, want, Mode::Check)?;
                    let at = self.infer(Env::EMPTY, id, rhs, Mode::Check)?;
                    ensure!(
                        self,
                        self.def_eq(at, wt)?,
                        "incorrect recursor computation rule"
                    );
                    let a = self.eval(Env::EMPTY, id, rhs)?;
                    let b = self.eval(Env::EMPTY, id, want)?;
                    ensure!(
                        self,
                        self.def_eq(a, b)?,
                        "incorrect recursor computation rule"
                    );
                }
            }
        }
        Ok(())
    }
}

/// The value core a block's obligation batches share, so each starts from what the earlier ones
/// evaluated. Dropped when the limit would move backwards or a batch fails.
#[derive(Default)]
pub(crate) struct RecChecker<'t, 'a: 't>(Option<Vc<'t, 'a>>);

impl<'t, 'a: 't> RecChecker<'t, 'a> {
    pub(crate) fn check(
        &mut self,
        ctx: &mut Ctx<'t, 'a>,
        limits: Limits,
        steps: &mut u64,
        uparams: LevelsPtr<'t>,
        limit: u32,
        checks: &[RecCheck<'t>],
    ) -> Result<Option<usize>, Failure> {
        if self.0.as_ref().is_some_and(|vc| vc.limit > limit) {
            self.0 = None;
        }
        let vc = self
            .0
            .get_or_insert_with(|| Vc::new(ctx.store, ctx.arena, limits));
        swap(&mut vc.ctx, ctx);
        let e = vc.ctx.levels(&[]);
        vc.id = Sub { ks: e, vs: e };
        vc.steps_left = *steps;
        vc.uparams = uparams;
        vc.included.clear();
        vc.limit = limit;
        let mut at = 0;
        let result = checks
            .iter()
            .enumerate()
            .try_for_each(|(i, &c)| {
                at = i;
                vc.rec_check(c)
            })
            .map_err(|_| vc.failure());
        swap(&mut vc.ctx, ctx);
        *steps = vc.steps_left;
        match result {
            Ok(()) => Ok(None),
            Err(Failure::Rejected(_)) => {
                self.0 = None;
                Ok(Some(at))
            }
            Err(failure) => {
                self.0 = None;
                Err(failure)
            }
        }
    }
}
