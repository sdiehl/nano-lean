mod contextual;
mod defeq;
pub(crate) mod env;
mod inductive;
pub(crate) mod nat;
mod native_inductive;
pub use inductive::Adapter;
#[cfg(feature = "vstats")]
pub use inductive::BLOCKS;
mod quot;
#[cfg(test)]
mod tests;
mod whnf;

use crate::resource::Budget;
use crate::term::arena::Arena;
use crate::term::ctx::Ctx;
use crate::term::decl::Declar;
use crate::term::expr::Expr;
use crate::term::intern::{Names, Store};
use crate::term::ops::LEVEL_FORM;
use crate::term::outcome::{Decline, Failure, R, Stop};
use crate::term::ptr::{ExprPtr, LevelPtr, LevelsPtr, NamePtr};
use crate::term::{FxHashMap, FxHashSet};
use crate::{ensure, reject};
use env::{Decls, strip_pis};
use std::cell::Cell;
use std::fmt;
use std::rc::Rc;

#[derive(Clone, Copy)]
pub struct Limits {
    pub steps: u64,
    pub arena_bytes: usize,
}

impl Default for Limits {
    fn default() -> Self {
        Self {
            steps: 100_000_000,
            arena_bytes: 256 << 20,
        }
    }
}

/// Both engines share the work budget and rejections never retry.
pub fn check_declaration<'a>(
    store: &'a Store<'a>,
    arena: &mut Arena,
    idx: u32,
    limits: Limits,
) -> Result<bool, Failure> {
    check_with_adapter(store, arena, idx, limits, None, false)
}

pub fn check_with_adapter<'a>(
    store: &'a Store<'a>,
    arena: &mut Arena,
    idx: u32,
    mut limits: Limits,
    mut adapter: Option<&mut Adapter<'a>>,
    native_only: bool,
) -> Result<bool, Failure> {
    let (result, steps) = check_shared(store, arena, idx, limits, adapter.as_deref_mut());
    limits.steps = steps;
    match result {
        Err(Failure::Declined(Decline::Exhausted(Budget::Arena))) if !native_only => {
            arena.reset();
            check_existing_only(store, arena, idx, limits, adapter).map(|()| true)
        }
        result => result.map(|()| false),
    }
}

pub fn check_shared<'a>(
    store: &'a Store<'a>,
    arena: &Arena,
    idx: u32,
    limits: Limits,
    adapter: Option<&mut Adapter<'a>>,
) -> (Result<(), Failure>, u64) {
    let mut tc = Tc::new(store, arena)
        .with_limits(limits)
        .with_adapter(adapter);
    let result = tc.check(idx);
    (result, tc.steps_left)
}

pub fn check_existing_only<'a>(
    store: &'a Store<'a>,
    arena: &mut Arena,
    idx: u32,
    limits: Limits,
    adapter: Option<&mut Adapter<'a>>,
) -> Result<(), Failure> {
    let mut tc = Tc::new(store, arena)
        .with_limits(limits)
        .with_adapter(adapter);
    tc.check_existing(idx).map_err(|_| tc.failure())
}

type ContextKey<'t> = (ExprPtr<'t>, Vec<ExprPtr<'t>>);
type RecKey<'t> = (NamePtr<'t>, LevelsPtr<'t>, Vec<ExprPtr<'t>>);

pub struct Tc<'t, 'a: 't> {
    pub ctx: Ctx<'t, 'a>,
    pub(crate) names: Names<'t>,
    pub(crate) uparams: LevelsPtr<'t>,
    pub(crate) limit: u32,
    adapter: Option<&'t mut Adapter<'a>>,
    next_local: u32,
    /// Values of the let-bound locals, unfolded only at the head.
    pub(crate) let_vals: FxHashMap<u32, ExprPtr<'t>>,
    conversion_depth: Rc<Cell<usize>>,
    conversion_locals: FxHashMap<(usize, ExprPtr<'t>), ExprPtr<'t>>,
    probe_remaining: Option<u32>,
    limits: Limits,
    steps_left: u64,
    fail: Option<Failure>,
    #[cfg(test)]
    probe_exhaustions: usize,
    open_infer_cache: [FxHashMap<ContextKey<'t>, ExprPtr<'t>>; 2],
    support_cache: FxHashMap<ExprPtr<'t>, Rc<[u16]>>,
    infer_cache: [FxHashMap<ExprPtr<'t>, ExprPtr<'t>>; 2],
    pub(crate) argument_support: FxHashMap<(NamePtr<'t>, usize), Rc<[bool]>>,
    pub(crate) rec_cache: FxHashMap<RecKey<'t>, ExprPtr<'t>>,
    pub(crate) whnf_core_cache: FxHashMap<ExprPtr<'t>, ExprPtr<'t>>,
    /// Unfolding results are valid only within the current declaration scope.
    pub(crate) unfold_cache: FxHashMap<ExprPtr<'t>, Option<ExprPtr<'t>>>,
    pub(crate) whnf_cache: FxHashMap<ExprPtr<'t>, ExprPtr<'t>>,
    pub(crate) eq_cache: FxHashSet<(ExprPtr<'t>, ExprPtr<'t>)>,
    pub(crate) fail_cache: FxHashSet<(ExprPtr<'t>, ExprPtr<'t>)>,
}

impl<'t, 'a: 't> Tc<'t, 'a> {
    pub fn new(store: &'a Store<'a>, arena: &'t Arena) -> Self {
        let ctx = Ctx::new(store, arena);
        let uparams = ctx
            .store
            .declars
            .first()
            .map_or_else(|| LevelsPtr::new(&[]), super::term::decl::Declar::uparams);
        Self {
            names: store.names,
            ctx,
            uparams,
            limit: 0,
            adapter: None,
            next_local: 0,
            let_vals: FxHashMap::default(),
            conversion_depth: Default::default(),
            conversion_locals: Default::default(),
            probe_remaining: None,
            limits: Limits::default(),
            steps_left: Limits::default().steps,
            fail: None,
            #[cfg(test)]
            probe_exhaustions: 0,
            open_infer_cache: Default::default(),
            support_cache: Default::default(),
            infer_cache: Default::default(),
            argument_support: FxHashMap::default(),
            rec_cache: FxHashMap::default(),
            whnf_core_cache: FxHashMap::default(),
            unfold_cache: FxHashMap::default(),
            whnf_cache: FxHashMap::default(),
            eq_cache: FxHashSet::default(),
            fail_cache: FxHashSet::default(),
        }
    }

    pub fn with_adapter(mut self, adapter: Option<&'t mut Adapter<'a>>) -> Self {
        self.adapter = adapter;
        self
    }

    pub fn with_limits(mut self, limits: Limits) -> Self {
        self.limits = limits;
        self.steps_left = limits.steps;
        self
    }

    #[cold]
    #[inline(never)]
    pub(crate) fn reject(&mut self, msg: fmt::Arguments<'_>) -> Stop {
        self.fail = Some(Failure::Rejected(msg.to_string()));
        Stop
    }

    #[cold]
    #[inline(never)]
    pub(crate) fn decline(&mut self, budget: Budget) -> Stop {
        self.fail = Some(Failure::Declined(Decline::Exhausted(budget)));
        Stop
    }

    #[cold]
    #[inline(never)]
    pub(crate) fn failed(&mut self, failure: Failure) -> Stop {
        self.fail = Some(failure);
        Stop
    }

    /// The failure behind a `Stop` that reached the top of the check.
    pub(crate) fn failure(&mut self) -> Failure {
        Failure::escaped(&mut self.fail)
    }

    pub fn check(&mut self, idx: u32) -> Result<(), Failure> {
        self.check_in(idx).map_err(|_| self.failure())
    }

    fn check_in(&mut self, idx: u32) -> R<()> {
        if self.ctx.arena.used_bytes() > self.limits.arena_bytes {
            return Err(self.decline(Budget::Arena));
        }
        self.infer_cache
            .iter_mut()
            .for_each(std::collections::HashMap::clear);
        self.open_infer_cache
            .iter_mut()
            .for_each(std::collections::HashMap::clear);
        self.support_cache.clear();
        self.argument_support.clear();
        self.rec_cache.clear();
        self.whnf_core_cache.clear();
        self.whnf_cache.clear();
        self.unfold_cache.clear();
        self.eq_cache.clear();
        self.fail_cache.clear();
        self.let_vals.clear();
        self.probe_remaining = None;
        self.conversion_depth.set(0);
        self.conversion_locals.clear();
        self.steps_left = self.limits.steps;
        let d: Declar<'t> = self.ctx.store.declars[idx as usize];
        self.uparams = d.uparams();
        self.limit = idx;
        match d {
            Declar::Axiom(i) => self.check_type(i.ty),
            Declar::Def(i, v, _) | Declar::Opaque(i, v) => {
                self.check_type(i.ty)?;
                self.check_value(v, i.ty)
            }
            Declar::Thm(i, v) => {
                self.check_type(i.ty)?;
                ensure!(
                    self,
                    self.is_prop(i.ty)?,
                    "theorem type is not a proposition"
                );
                self.check_value(v, i.ty)
            }
            Declar::Quot(i) => {
                self.check_type(i.ty)?;
                self.check_quot(i)
            }
            Declar::Ind(_) | Declar::Ctor(_) | Declar::Rec(_) => self.check_inductive(idx, d),
        }
    }

    pub(crate) fn check_type(&mut self, ty: ExprPtr<'t>) -> R<()> {
        let s = self.infer(ty, false)?;
        self.ensure_sort(s)?;
        Ok(())
    }

    fn check_value(&mut self, v: ExprPtr<'t>, ty: ExprPtr<'t>) -> R<()> {
        let vt = self.infer(v, false)?;
        ensure!(self, self.def_eq(vt, ty)?, "declaration type mismatch");
        Ok(())
    }

    pub(crate) fn level_eq(&mut self, a: LevelPtr<'t>, b: LevelPtr<'t>) -> R<bool> {
        let Some(r) = self.ctx.try_level_eq(a, b) else {
            reject!(self, "{LEVEL_FORM}")
        };
        Ok(r)
    }

    pub(crate) fn levels_eq(&mut self, a: LevelsPtr<'t>, b: LevelsPtr<'t>) -> R<bool> {
        let Some(r) = self.ctx.try_levels_eq(a, b) else {
            reject!(self, "{LEVEL_FORM}")
        };
        Ok(r)
    }

    pub(crate) fn leq(&mut self, a: LevelPtr<'t>, b: LevelPtr<'t>) -> R<bool> {
        let Some(r) = self.ctx.try_leq(a, b) else {
            reject!(self, "{LEVEL_FORM}")
        };
        Ok(r)
    }

    pub(crate) fn is_zero(&mut self, l: LevelPtr<'t>) -> R<bool> {
        let z = self.ctx.zero();
        self.leq(l, z)
    }

    pub(crate) fn inst(&mut self, e: ExprPtr<'t>, subs: &[ExprPtr<'t>]) -> R<ExprPtr<'t>> {
        let Some(r) = self.ctx.inst(e, subs) else {
            reject!(self, "variable index overflow")
        };
        Ok(r)
    }

    pub(crate) fn inst1(&mut self, e: ExprPtr<'t>, s: ExprPtr<'t>) -> R<ExprPtr<'t>> {
        self.inst(e, &[s])
    }

    pub(crate) fn fresh_local(&mut self, ty: ExprPtr<'t>) -> ExprPtr<'t> {
        self.next_local += 1;
        self.ctx.local(self.next_local, ty)
    }

    pub(crate) fn let_local(&mut self, ty: ExprPtr<'t>, val: ExprPtr<'t>) -> ExprPtr<'t> {
        let x = self.fresh_local(ty);
        self.let_vals.insert(self.next_local, val);
        x
    }

    pub(crate) fn empty_levels(&mut self) -> LevelsPtr<'t> {
        self.ctx.levels(&[])
    }

    pub(crate) fn konst0(&mut self, n: Option<NamePtr<'t>>) -> R<ExprPtr<'t>> {
        let Some(n) = n else {
            reject!(self, "missing builtin constant")
        };
        let ls = self.empty_levels();
        Ok(self.ctx.konst(n, ls))
    }

    pub(crate) fn ensure_sort(&mut self, e: ExprPtr<'t>) -> R<LevelPtr<'t>> {
        if let Expr::Sort { level, .. } = *e {
            return Ok(level);
        }
        match *self.whnf(e)? {
            Expr::Sort { level, .. } => Ok(level),
            _ => reject!(self, "expected a sort"),
        }
    }

    pub(crate) fn ensure_pi(&mut self, e: ExprPtr<'t>) -> R<ExprPtr<'t>> {
        if e.is_pi() {
            return Ok(e);
        }
        let w = self.whnf(e)?;
        ensure!(self, w.is_pi(), "expected a function type");
        Ok(w)
    }

    pub(crate) fn is_prop(&mut self, e: ExprPtr<'t>) -> R<bool> {
        let t = self.infer(e, true)?;
        let t = self.whnf(t)?;
        match *t {
            Expr::Sort { level, .. } => self.is_zero(level),
            _ => Ok(false),
        }
    }

    fn check_level(&mut self, l: LevelPtr<'t>) -> R<()> {
        ensure!(
            self,
            l.params_in(self.uparams),
            "undeclared universe parameter"
        );
        Ok(())
    }

    pub fn infer(&mut self, e: ExprPtr<'t>, only: bool) -> R<ExprPtr<'t>> {
        self.tick()?;
        if let Some(&r) = self.infer_cache[0].get(&e) {
            return Ok(r);
        }
        if only && let Some(&r) = self.infer_cache[1].get(&e) {
            return Ok(r);
        }
        let r = match *e {
            Expr::Var { .. } => reject!(self, "unexpected bound variable"),
            Expr::Local { ty, .. } => ty,
            Expr::Sort { level, .. } => {
                if !only {
                    self.check_level(level)?;
                }
                let l = self.ctx.succ(level);
                self.ctx.sort(l)
            }
            Expr::Const { name, levels, .. } => {
                let Some(d) = self.declar(name) else {
                    reject!(self, "unknown constant {}", name.as_ref())
                };
                ensure!(
                    self,
                    levels.len() == d.uparams().len(),
                    "wrong number of universe levels for {}",
                    name.as_ref()
                );
                if !only {
                    for &l in levels.as_ref() {
                        self.check_level(l)?;
                    }
                }
                self.ctx.declar_type(&d, levels)
            }
            Expr::App { .. } => self.infer_app(e, only)?,
            Expr::Lam { .. } | Expr::Pi { .. } | Expr::Let { .. } => {
                self.infer_contextual(e, &mut Vec::new(), only)?
            }
            Expr::Proj {
                name, idx, e: s, ..
            } => self.infer_proj(name, idx, s, only)?,
            Expr::NatLit { .. } => self.literal_type(self.names.nat)?,
            Expr::StrLit { .. } => self.literal_type(self.names.string)?,
        };
        self.infer_cache[usize::from(only)].insert(e, r);
        Ok(r)
    }

    fn literal_type(&mut self, name: Option<NamePtr<'t>>) -> R<ExprPtr<'t>> {
        let ty = self.konst0(name)?;
        let sort = self.infer(ty, true)?;
        let one = self.ctx.succ(self.ctx.zero());
        let expected = self.ctx.sort(one);
        ensure!(self, self.def_eq(sort, expected)?, "invalid literal type");
        Ok(ty)
    }

    fn infer_app(&mut self, e: ExprPtr<'t>, only: bool) -> R<ExprPtr<'t>> {
        let (f, args) = self.ctx.unfold_apps(e);
        let mut ft = self.infer(f, only)?;
        let mut j = 0;
        for i in 0..args.len() {
            self.tick()?;
            if !ft.is_pi() {
                ft = self.inst(ft, &args[j..i])?;
                ft = self.ensure_pi(ft)?;
                j = i;
            }
            let Expr::Pi { ty, body, .. } = *ft else {
                unreachable!()
            };
            if !only {
                let domain = self.inst(ty, &args[j..i])?;
                let actual = self.infer(args[i], false)?;
                ensure!(
                    self,
                    self.def_eq(actual, domain)?,
                    "application type mismatch"
                );
            }
            ft = body;
        }
        self.inst(ft, &args[j..])
    }

    fn infer_proj(
        &mut self,
        name: NamePtr<'t>,
        idx: u16,
        s: ExprPtr<'t>,
        only: bool,
    ) -> R<ExprPtr<'t>> {
        let st = self.infer(s, only)?;
        let is_prop = self.is_prop(st)?;
        let st = self.whnf(st)?;
        let (h, args) = self.ctx.unfold_apps(st);
        let Expr::Const {
            name: iname,
            levels,
            ..
        } = *h
        else {
            reject!(self, "projection of a non-structure")
        };
        ensure!(self, iname == name, "projection type mismatch");
        let Some((ind, ctor)) = self.single_ctor(name) else {
            reject!(self, "projection of a non-structure")
        };
        ensure!(
            self,
            args.len() == usize::from(ind.num_params),
            "projection of a non-structure"
        );
        let ct = self.ctx.declar_type(&Declar::Ctor(ctor), levels);
        let Some(ct) = strip_pis(ct, args.len()) else {
            reject!(self, "expected a Pi binder")
        };
        let mut r = self.inst(ct, &args)?;
        for i in 0..idx {
            r = self.whnf(r)?;
            let Expr::Pi { ty, body, .. } = *r else {
                reject!(self, "invalid projection")
            };
            if body.nlb() > 0 {
                ensure!(self, !is_prop || self.is_prop(ty)?, "invalid projection");
                let p = self.ctx.proj(name, i, s);
                r = self.inst1(body, p)?;
            } else {
                r = body;
            }
        }
        r = self.whnf(r)?;
        let Expr::Pi { ty, .. } = *r else {
            reject!(self, "invalid projection")
        };
        ensure!(self, !is_prop || self.is_prop(ty)?, "invalid projection");
        Ok(ty)
    }
}

impl<'t, 'a: 't> Decls<'t> for Tc<'t, 'a> {
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
