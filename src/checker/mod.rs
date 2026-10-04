//! Locally nameless type checker over the interned term store. Going under a
//! binder instantiates it with a fresh local that carries its type, so every
//! term the checker sees is closed and all caches key on pointers.

mod defeq;
mod inductive;
mod quot;
#[cfg(test)]
mod tests;
mod whnf;

use crate::term::FxHashMap;
use crate::term::FxHashSet;
use crate::term::ctx::Ctx;
use crate::term::decl::{Constructor, Declar, Inductive};
use crate::term::expr::Expr;
use crate::term::intern::{Names, Store};
use crate::term::ptr::{ExprPtr, LevelPtr, LevelsPtr, NamePtr};
use crate::{ensure, reject};
use bumpalo::Bump;

pub struct Tc<'t, 'a: 't> {
    pub ctx: Ctx<'t, 'a>,
    pub(crate) names: Names<'t>,
    pub(crate) uparams: LevelsPtr<'t>,
    /// Declarations at or past this index are not yet in scope.
    pub(crate) limit: u32,
    next_local: u32,
    infer_cache: [FxHashMap<ExprPtr<'t>, ExprPtr<'t>>; 2],
    pub(crate) whnf_core_cache: FxHashMap<ExprPtr<'t>, ExprPtr<'t>>,
    pub(crate) whnf_cache: FxHashMap<ExprPtr<'t>, ExprPtr<'t>>,
    pub(crate) eq_cache: FxHashSet<(ExprPtr<'t>, ExprPtr<'t>)>,
    pub(crate) fail_cache: FxHashSet<(ExprPtr<'t>, ExprPtr<'t>)>,
}

impl<'t, 'a: 't> Tc<'t, 'a> {
    pub fn new(store: &'a Store<'a>, arena: &'t Bump) -> Self {
        let ctx = Ctx::new(store, arena);
        let uparams = ctx
            .store
            .declars
            .first()
            .map_or_else(|| LevelsPtr::new(&[]), |d| d.uparams());
        Self {
            names: store.names,
            ctx,
            uparams,
            limit: 0,
            next_local: 0,
            infer_cache: Default::default(),
            whnf_core_cache: FxHashMap::default(),
            whnf_cache: FxHashMap::default(),
            eq_cache: FxHashSet::default(),
            fail_cache: FxHashSet::default(),
        }
    }

    /// Check the declaration at `idx`. An inductive block is checked as a whole
    /// at its first type; its other members are skipped.
    pub fn check(&mut self, idx: u32) {
        self.infer_cache.iter_mut().for_each(|cache| cache.clear());
        self.whnf_core_cache.clear();
        self.whnf_cache.clear();
        self.eq_cache.clear();
        self.fail_cache.clear();
        let d: Declar<'t> = self.ctx.store.declars[idx as usize];
        self.uparams = d.uparams();
        self.limit = idx;
        match d {
            Declar::Axiom(i) => self.check_type(i.ty),
            Declar::Def(i, v, _) | Declar::Opaque(i, v) => {
                self.check_type(i.ty);
                self.check_value(v, i.ty);
            }
            Declar::Thm(i, v) => {
                self.check_type(i.ty);
                ensure!(self.is_prop(i.ty), "theorem type is not a proposition");
                self.check_value(v, i.ty);
            }
            Declar::Quot(i) => {
                self.check_type(i.ty);
                self.check_quot(i);
            }
            Declar::Ind(_) | Declar::Ctor(_) | Declar::Rec(_) => self.check_inductive(idx, d),
        }
    }

    pub(crate) fn check_type(&mut self, ty: ExprPtr<'t>) {
        let s = self.infer(ty, false);
        self.ensure_sort(s);
    }

    fn check_value(&mut self, v: ExprPtr<'t>, ty: ExprPtr<'t>) {
        let vt = self.infer(v, false);
        ensure!(self.def_eq(vt, ty), "declaration type mismatch");
    }

    pub(crate) fn declar(&self, n: NamePtr<'t>) -> Option<Declar<'t>> {
        let i = n.decl_idx()?;
        (i < self.limit).then(|| self.ctx.store.declars[i as usize])
    }

    pub(crate) fn structure_like(
        &self,
        n: NamePtr<'t>,
    ) -> Option<(Inductive<'t>, Constructor<'t>)> {
        let Some(Declar::Ind(i)) = self.declar(n) else {
            return None;
        };
        if i.ctors.len() != 1 || i.num_indices != 0 || i.is_rec {
            return None;
        }
        match self.declar(i.ctors[0]) {
            Some(Declar::Ctor(c)) => Some((i, c)),
            _ => None,
        }
    }

    pub(crate) fn fresh_local(&mut self, ty: ExprPtr<'t>) -> ExprPtr<'t> {
        self.next_local += 1;
        self.ctx.local(self.next_local, ty)
    }

    pub(crate) fn empty_levels(&mut self) -> LevelsPtr<'t> {
        self.ctx.levels(&[])
    }

    pub(crate) fn konst0(&mut self, n: Option<NamePtr<'t>>) -> ExprPtr<'t> {
        let Some(n) = n else {
            reject!("missing builtin constant")
        };
        let ls = self.empty_levels();
        self.ctx.konst(n, ls)
    }

    pub(crate) fn ensure_sort(&mut self, e: ExprPtr<'t>) -> LevelPtr<'t> {
        if let Expr::Sort { level, .. } = *e {
            return level;
        }
        match *self.whnf(e) {
            Expr::Sort { level, .. } => level,
            _ => reject!("expected a sort"),
        }
    }

    pub(crate) fn ensure_pi(&mut self, e: ExprPtr<'t>) -> ExprPtr<'t> {
        if e.is_pi() {
            return e;
        }
        let w = self.whnf(e);
        ensure!(w.is_pi(), "expected a function type");
        w
    }

    pub(crate) fn is_prop(&mut self, e: ExprPtr<'t>) -> bool {
        let t = self.infer(e, true);
        let t = self.whnf(t);
        match *t {
            Expr::Sort { level, .. } => self.ctx.level_eq(level, self.ctx.zero()),
            _ => false,
        }
    }

    fn check_level(&self, l: LevelPtr<'t>) {
        ensure!(l.params_in(self.uparams), "undeclared universe parameter");
    }

    pub fn infer(&mut self, e: ExprPtr<'t>, only: bool) -> ExprPtr<'t> {
        if let Some(&r) = self.infer_cache[0].get(&e) {
            return r;
        }
        if only && let Some(&r) = self.infer_cache[1].get(&e) {
            return r;
        }
        let r = match *e {
            Expr::Var { .. } => reject!("unexpected bound variable"),
            Expr::Local { ty, .. } => ty,
            Expr::Sort { level, .. } => {
                if !only {
                    self.check_level(level);
                }
                let l = self.ctx.succ(level);
                self.ctx.sort(l)
            }
            Expr::Const { name, levels, .. } => {
                let Some(d) = self.declar(name) else {
                    reject!("unknown constant {}", name.as_ref())
                };
                ensure!(
                    levels.len() == d.uparams().len(),
                    "wrong number of universe levels for {}",
                    name.as_ref()
                );
                if !only {
                    for &l in levels.as_ref() {
                        self.check_level(l);
                    }
                }
                self.ctx.declar_type(&d, levels)
            }
            Expr::App { fun, arg, .. } => {
                if only {
                    self.infer_app_only(e)
                } else {
                    let ft = self.infer(fun, false);
                    let ft = self.ensure_pi(ft);
                    let Expr::Pi { ty, body, .. } = *ft else {
                        unreachable!()
                    };
                    let at = self.infer(arg, false);
                    ensure!(self.def_eq(at, ty), "application type mismatch");
                    self.ctx.inst1(body, arg)
                }
            }
            Expr::Lam { .. } => self.infer_lam(e, only),
            Expr::Pi { .. } => self.infer_pi(e, only),
            Expr::Let { data, .. } => {
                if !only {
                    self.check_type(data.ty);
                    let vt = self.infer(data.val, false);
                    ensure!(self.def_eq(vt, data.ty), "let value type mismatch");
                }
                let b = self.ctx.inst1(data.body, data.val);
                self.infer(b, only)
            }
            Expr::Proj {
                name, idx, e: s, ..
            } => self.infer_proj(name, idx, s, only),
            Expr::NatLit { .. } => self.konst0(self.names.nat),
            Expr::StrLit { .. } => self.konst0(self.names.string),
        };
        self.infer_cache[usize::from(only)].insert(e, r);
        r
    }

    fn infer_app_only(&mut self, e: ExprPtr<'t>) -> ExprPtr<'t> {
        let (f, args) = self.ctx.unfold_apps(e);
        let mut ft = self.infer(f, true);
        let mut j = 0;
        for i in 0..args.len() {
            if let Expr::Pi { body, .. } = *ft {
                ft = body;
            } else {
                ft = self.ctx.inst(ft, &args[j..i]);
                ft = self.ensure_pi(ft);
                let Expr::Pi { body, .. } = *ft else {
                    unreachable!()
                };
                ft = body;
                j = i;
            }
        }
        self.ctx.inst(ft, &args[j..])
    }

    fn infer_lam(&mut self, e: ExprPtr<'t>, only: bool) -> ExprPtr<'t> {
        let mut locals = Vec::new();
        let mut tys = Vec::new();
        let mut cur = e;
        while let Expr::Lam { ty, body, .. } = *cur {
            let d = self.ctx.inst(ty, &locals);
            if !only {
                self.check_type(d);
            }
            tys.push(ty);
            let l = self.fresh_local(d);
            locals.push(l);
            cur = body;
        }
        let b = self.ctx.inst(cur, &locals);
        let r = self.infer(b, only);
        let mut r = self.ctx.abstract_locals(r, &locals);
        for &ty in tys.iter().rev() {
            r = self.ctx.pi(ty, r);
        }
        r
    }

    fn infer_pi(&mut self, e: ExprPtr<'t>, only: bool) -> ExprPtr<'t> {
        let mut locals = Vec::new();
        let mut levels = Vec::new();
        let mut cur = e;
        while let Expr::Pi { ty, body, .. } = *cur {
            let d = self.ctx.inst(ty, &locals);
            let s = self.infer(d, only);
            levels.push(self.ensure_sort(s));
            let l = self.fresh_local(d);
            locals.push(l);
            cur = body;
        }
        let b = self.ctx.inst(cur, &locals);
        let s = self.infer(b, only);
        let mut r = self.ensure_sort(s);
        for &l in levels.iter().rev() {
            r = self.ctx.imax(l, r);
        }
        self.ctx.sort(r)
    }

    fn infer_proj(
        &mut self,
        name: NamePtr<'t>,
        idx: u16,
        s: ExprPtr<'t>,
        only: bool,
    ) -> ExprPtr<'t> {
        let st = self.infer(s, only);
        let st = self.whnf(st);
        let (h, args) = self.ctx.unfold_apps(st);
        let Expr::Const {
            name: iname,
            levels,
            ..
        } = *h
        else {
            reject!("projection of a non-structure")
        };
        ensure!(iname == name, "projection type mismatch");
        let Some((ind, ctor)) = self.structure_like(name).or_else(|| self.single_ctor(name)) else {
            reject!("projection of a non-structure")
        };
        ensure!(
            args.len() == usize::from(ind.num_params),
            "projection of a non-structure"
        );
        let is_prop = self.is_prop(st);
        let ct = self.ctx.declar_type(&Declar::Ctor(ctor), levels);
        let mut r = self.ctx.inst_pis(ct, &args);
        for i in 0..idx {
            r = self.whnf(r);
            let Expr::Pi { ty, body, .. } = *r else {
                reject!("invalid projection")
            };
            if body.nlb() > 0 {
                ensure!(!is_prop || self.is_prop(ty), "invalid projection");
                let p = self.ctx.proj(name, i, s);
                r = self.ctx.inst1(body, p);
            } else {
                r = body;
            }
        }
        r = self.whnf(r);
        let Expr::Pi { ty, .. } = *r else {
            reject!("invalid projection")
        };
        ensure!(!is_prop || self.is_prop(ty), "invalid projection");
        ty
    }

    /// Projections are allowed on any single-constructor inductive without
    /// indices, recursive or not.
    fn single_ctor(&self, n: NamePtr<'t>) -> Option<(Inductive<'t>, Constructor<'t>)> {
        let Some(Declar::Ind(i)) = self.declar(n) else {
            return None;
        };
        if i.ctors.len() != 1 || i.num_indices != 0 {
            return None;
        }
        match self.declar(i.ctors[0]) {
            Some(Declar::Ctor(c)) => Some((i, c)),
            _ => None,
        }
    }
}
