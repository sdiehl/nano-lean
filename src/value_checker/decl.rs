use super::value::{Env, K, Sub, V};
use super::{R, Vc};
use crate::checker::Limits;
use crate::ensure;
use crate::term::ctx::Ctx;
use crate::term::decl::Declar;
use crate::term::expr::Expr;
use crate::term::outcome::{self, Failure, raise};
use crate::term::ptr::{ExprPtr, LevelPtr, LevelsPtr};
use smallvec::SmallVec;
use std::mem::swap;

const PROBE_ESCAPED: &str = "probe exhaustion escaped its probe";

impl<'t, 'a: 't> Vc<'t, 'a> {
    pub(super) fn check(&mut self, idx: u32) {
        self.ensure_arena();
        let d = self.ctx.store.declars[idx as usize];
        self.uparams = d.uparams();
        self.included.clear();
        self.limit = idx;
        let r: R<()> = (|| {
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
                    ensure!(self.ctx.level_eq(l, z), "theorem type is not a proposition");
                    self.check_value(v, i.ty)?;
                }
                _ => unreachable!("bridged declaration"),
            }
            Ok(())
        })();
        r.expect(PROBE_ESCAPED);
    }

    fn check_type(&mut self, ty: ExprPtr<'t>) -> R<LevelPtr<'t>> {
        let id = self.id;
        let s = self.infer(Env::EMPTY, id, ty, false)?;
        self.ensure_sort(s)
    }

    /// Walks Pi binders under canonical locals so the value check reuses the type check's caches.
    fn check_telescope(&mut self, ty: ExprPtr<'t>) -> R<LevelPtr<'t>> {
        if !ty.closed()
            || !matches!(*ty, Expr::Pi { .. })
            || self.t.infer_closed[0].contains_key(&(ty, self.id))
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
            let s = self.infer(env, id, b, false)?;
            sorts.push(self.ensure_sort(s)?);
            let dom = self.eval(env, id, b)?;
            let x = self.binder_local(dom);
            env = self.push(env, x);
            e = body;
        }
        let s = self.infer(env, id, e, false)?;
        let mut l = self.ensure_sort(s)?;
        for &s1 in sorts.iter().rev() {
            l = self.ctx.imax(s1, l);
        }
        let t = self.mk(K::Sort(l), false);
        let s = if self.scoped == mark {
            LevelsPtr::new(&[])
        } else {
            self.uparams
        };
        self.t.infer_closed[0].insert((ty, id), (t, s));
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
                let s = self.infer(env, id, a, false)?;
                self.ensure_sort(s)?;
                doms.push((dom, env, b));
            }
            let x = self.binder_local(dom);
            env = self.push(env, x);
            (v, ty) = (body, tb);
        }
        let vt = self.infer(env, id, v, false)?;
        for (dom, env, b) in doms {
            let d = self.eval(env, id, b)?;
            ensure!(self.def_eq(dom, d)?, "declaration type mismatch");
        }
        let tv = self.eval(env, id, ty)?;
        ensure!(self.def_eq(vt, tv)?, "declaration type mismatch");
        Ok(())
    }
}

#[derive(Clone, Copy)]
pub(crate) enum RecCheck<'t> {
    Sort(ExprPtr<'t>),
    Type(ExprPtr<'t>, ExprPtr<'t>),
    Rule(ExprPtr<'t>, ExprPtr<'t>),
}

impl<'t, 'a: 't> Vc<'t, 'a> {
    fn rec_check(&mut self, c: RecCheck<'t>) -> R<()> {
        let id = self.id;
        match c {
            RecCheck::Sort(ty) => {
                self.check_type(ty)?;
            }
            RecCheck::Type(ty, want) => {
                self.check_type(ty)?;
                if ty != want {
                    let a = self.eval(Env::EMPTY, id, ty)?;
                    let b = self.eval(Env::EMPTY, id, want)?;
                    ensure!(self.def_eq(a, b)?, "incorrect recursor type");
                }
            }
            RecCheck::Rule(rhs, want) => {
                let wt = self.infer(Env::EMPTY, id, want, false)?;
                if rhs != want {
                    let at = self.infer(Env::EMPTY, id, rhs, false)?;
                    ensure!(self.def_eq(at, wt)?, "incorrect recursor computation rule");
                    let a = self.eval(Env::EMPTY, id, rhs)?;
                    let b = self.eval(Env::EMPTY, id, want)?;
                    ensure!(self.def_eq(a, b)?, "incorrect recursor computation rule");
                }
            }
        }
        Ok(())
    }
}

pub(crate) fn check_recursor<'t, 'a: 't>(
    ctx: &mut Ctx<'t, 'a>,
    limits: Limits,
    steps: &mut u64,
    uparams: LevelsPtr<'t>,
    limit: u32,
    checks: &[RecCheck<'t>],
) -> Result<(), usize> {
    let mut vc = Vc::new(ctx.store, ctx.arena, limits);
    swap(&mut vc.ctx, ctx);
    let e = vc.ctx.levels(&[]);
    vc.id = Sub { ks: e, vs: e };
    vc.steps_left = *steps;
    vc.uparams = uparams;
    vc.limit = limit;
    let mut at = 0;
    let result = outcome::run(|| {
        for (i, &c) in checks.iter().enumerate() {
            at = i;
            vc.rec_check(c).expect(PROBE_ESCAPED);
        }
    });
    swap(&mut vc.ctx, ctx);
    *steps = vc.steps_left;
    match result {
        Ok(()) => Ok(()),
        Err(Failure::Rejected(_)) => Err(at),
        Err(Failure::Declined(d)) => raise(d),
        Err(Failure::Internal(m)) => raise(m),
    }
}
