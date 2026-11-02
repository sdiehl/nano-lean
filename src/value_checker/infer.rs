use super::eval::{SPINE, agree};
use super::tables::{Inferred, Mode, Scoped};
use super::value::{Clo, Env, Head, K, Sub, V, key};
use super::{R, Vc, stat};
use crate::checker::env::Decls;
use crate::term::expr::Expr;
use crate::term::ptr::{ExprPtr, LevelPtr, LevelsPtr, NamePtr};
use crate::{ensure, reject};
use std::mem::MaybeUninit;
use std::ptr;

impl<'t, 'a: 't> Vc<'t, 'a> {
    pub(crate) fn ensure_sort(&mut self, t: V<'t>) -> R<LevelPtr<'t>> {
        if let K::Sort(l) = t.k {
            return Ok(l);
        }
        match self.whnf(t)?.k {
            K::Sort(l) => Ok(l),
            _ => reject!(self, "expected a sort"),
        }
    }

    pub(crate) fn ensure_pi(&mut self, t: V<'t>) -> R<(V<'t>, Clo<'t>)> {
        if let K::Pi(d, c) = t.k {
            return Ok((d, c));
        }
        match self.whnf(t)?.k {
            K::Pi(d, c) => Ok((d, c)),
            _ => reject!(self, "expected a function type"),
        }
    }

    pub(crate) fn is_prop(&mut self, t: V<'t>) -> R<bool> {
        let s = self.type_of(t)?;
        let s = self.whnf(s)?;
        Ok(match s.k {
            K::Sort(l) => {
                let z = self.ctx.zero();
                self.level_eq(l, z)?
            }
            _ => false,
        })
    }

    fn literal_type(&mut self, n: Option<NamePtr<'t>>) -> R<V<'t>> {
        let ty = self.konst0(n)?;
        let s = self.type_of(ty)?;
        let z = self.ctx.zero();
        let one = self.ctx.succ(z);
        let expected = self.mk(K::Sort(one), false);
        ensure!(self, self.def_eq(s, expected)?, "invalid literal type");
        Ok(ty)
    }

    pub(crate) fn type_of(&mut self, v: V<'t>) -> R<V<'t>> {
        if let Some(t) = self.memo(v).and_then(|m| m.ty.get()) {
            return Ok(t);
        }
        self.tick()?;
        let t = match v.k {
            K::Sort(l) => {
                let l = self.ctx.succ(l);
                self.mk(K::Sort(l), false)
            }
            K::Nat(_) => self.literal_type(self.names.nat)?,
            K::Str(_) => self.literal_type(self.names.string)?,
            K::Pi(d, c) => {
                let s1 = self.type_of(d)?;
                let s1 = self.ensure_sort(s1)?;
                let s2 = self.restoring_depth(|vc| {
                    let x = vc.binder_local(d);
                    let b = vc.inst(c, x)?;
                    vc.type_of(b)
                })?;
                let s2 = self.ensure_sort(s2)?;
                let l = self.ctx.imax(s1, s2);
                self.mk(K::Sort(l), false)
            }
            K::Lam(d, c) => {
                let d = self.force(d)?;
                self.mk(K::Pi(d, Clo { typed: true, ..c }), v.open)
            }
            K::Neu(h, args) => {
                let mut t = match h {
                    Head::Local(_, ty, _) => ty,
                    Head::Const(n, ls) => self.const_type(n, ls)?,
                    Head::Proj(n, i, s) => self.proj_type(n, i, s)?,
                };
                for &a in args {
                    let (_, c) = self.ensure_pi(t)?;
                    t = self.inst(c, a)?;
                }
                t
            }
        };
        self.memo_of(v).ty.set(Some(t));
        Ok(t)
    }

    fn proj_type(&mut self, name: NamePtr<'t>, idx: u16, s: V<'t>) -> R<V<'t>> {
        let st = self.type_of(s)?;
        let is_prop = self.is_prop(st)?;
        let st = self.whnf(st)?;
        let K::Neu(Head::Const(iname, ls), args) = st.k else {
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
        let mut r = self.const_type(ctor.info.name, ls)?;
        for &a in args {
            let K::Pi(_, c) = r.k else {
                reject!(self, "expected a function type")
            };
            r = self.inst(c, a)?;
        }
        for i in 0..idx {
            let K::Pi(d, c) = self.whnf(r)?.k else {
                reject!(self, "invalid projection")
            };
            if self.reads_arg(c) {
                ensure!(self, !is_prop || self.is_prop(d)?, "invalid projection");
                let p = self.proj(name, i, s);
                r = self.inst(c, p)?;
            } else {
                let dummy = self.dummy;
                r = self.inst(c, dummy)?;
            }
        }
        let K::Pi(d, _) = self.whnf(r)?.k else {
            reject!(self, "invalid projection")
        };
        ensure!(self, !is_prop || self.is_prop(d)?, "invalid projection");
        Ok(d)
    }

    #[inline(always)]
    fn infer_binder(
        &mut self,
        env: Env<'t>,
        sub: Sub<'t>,
        dom: V<'t>,
        body: ExprPtr<'t>,
        mode: Mode,
    ) -> R<V<'t>> {
        self.restoring_depth(|vc| {
            let x = vc.binder_local(dom);
            let env1 = vc.push(env, x);
            vc.infer(env1, sub, body, mode)
        })
    }

    /// Types `(fun x => body) a` by checking `body` once under a local and substituting `a`
    /// into its type, so a ladder of redexes never re-infers the bodies below it.
    fn infer_redex(
        &mut self,
        env: Env<'t>,
        sub: Sub<'t>,
        ty: ExprPtr<'t>,
        body: ExprPtr<'t>,
        a: ExprPtr<'t>,
    ) -> R<V<'t>> {
        let s = self.infer(env, sub, ty, Mode::Check)?;
        self.ensure_sort(s)?;
        let dom = self.eval(env, sub, ty)?;
        let at = self.infer(env, sub, a, Mode::Check)?;
        ensure!(self, self.def_eq(at, dom)?, "application type mismatch");
        let v = if !body.closed() && body.sup() & 1 != 0 {
            Some(self.eval(env, sub, a)?)
        } else {
            None
        };
        self.restoring_depth(|vc| {
            let x = vc.binder_local(dom);
            let env1 = vc.push(env, x);
            let t = vc.infer(env1, sub, body, Mode::Check)?;
            match v {
                Some(v) => vc.zeta(x, v, t),
                None => Ok(t),
            }
        })
    }

    pub(crate) fn infer(
        &mut self,
        env: Env<'t>,
        sub: Sub<'t>,
        e: ExprPtr<'t>,
        mode: Mode,
    ) -> R<V<'t>> {
        let t = self.infer_fast(env, sub, e, mode)?;
        #[cfg(feature = "memocheck")]
        self.audit_value("type", t, |c| {
            c.audit_bypass();
            c.infer_slow(env, sub, e, mode)
        });
        Ok(t)
    }

    /// Hits return from a frameless probe. Whatever calls out happens in `infer_slow`.
    #[inline(always)]
    fn infer_fast(&mut self, env: Env<'t>, sub: Sub<'t>, e: ExprPtr<'t>, mode: Mode) -> R<V<'t>> {
        self.guard()?;
        if let Expr::Var { idx, .. } = *e {
            let Some(v) = env.get(idx) else {
                reject!(self, "unexpected bound variable")
            };
            return match v.k {
                K::Neu(Head::Local(_, ty, _), []) => Ok(ty),
                _ => self.type_of(v),
            };
        }
        if e.closed() {
            if let Some(&Scoped { ty, uparams }) = self.t.infer_closed[Mode::Check].get(&(e, sub)) {
                if uparams.is_empty() {
                    stat!(self, closed_hit);
                    return Ok(ty);
                }
                if uparams == self.uparams {
                    stat!(self, closed_hit);
                    self.scoped += 1;
                    return Ok(ty);
                }
            }
        } else {
            let raw = (e, sub, env.key());
            if let Some(&Scoped { ty, uparams }) = self.t.infer_open[Mode::Check].get(&raw) {
                if uparams.is_empty() {
                    return Ok(ty);
                }
                if uparams == self.uparams {
                    self.scoped += 1;
                    return Ok(ty);
                }
            }
            if mode == Mode::Only
                && let Some(h) = self.t.infer_open[Mode::Only].get(&raw)
            {
                return Ok(h.ty);
            }
        }
        self.infer_slow(env, sub, e, mode)
    }

    #[cold]
    #[inline(never)]
    fn infer_app_wide(
        &mut self,
        env: Env<'t>,
        sub: Sub<'t>,
        e: ExprPtr<'t>,
        mode: Mode,
    ) -> R<V<'t>> {
        let mut args = Vec::new();
        let mut f = e;
        while let Expr::App { fun, arg, .. } = *f {
            args.push(arg);
            f = fun;
        }
        self.infer_spine(env, sub, f, &args, mode)
    }

    /// `args` runs from the outermost argument in.
    #[inline(always)]
    fn infer_spine(
        &mut self,
        env: Env<'t>,
        sub: Sub<'t>,
        f: ExprPtr<'t>,
        args: &[ExprPtr<'t>],
        mode: Mode,
    ) -> R<V<'t>> {
        let (mut ft, rest) = match *f {
            Expr::Lam { ty, body, .. } if mode == Mode::Check => {
                let (&a, rest) = args.split_last().expect("an application has an argument");
                (self.infer_redex(env, sub, ty, body, a)?, rest)
            }
            _ => (self.infer(env, sub, f, mode)?, args),
        };
        for &a in rest.iter().rev() {
            self.tick()?;
            let p = match ft.k {
                K::Pi(..) => ft,
                _ => self.whnf(ft)?,
            };
            let K::Pi(d, c) = p.k else {
                reject!(self, "expected a function type")
            };
            if mode == Mode::Check {
                let at = self.infer(env, sub, a, Mode::Check)?;
                ensure!(self, self.def_eq(at, d)?, "application type mismatch");
            }
            let x = if self.uses_arg(c) {
                self.eval(env, sub, a)?
            } else {
                self.dummy
            };
            ft = if c.typed {
                self.inst(c, x)?
            } else {
                let k = (key(p), key(x));
                match self.t.insts.probe(&k) {
                    Ok(&v) => {
                        stat!(self, inst_hit);
                        #[cfg(feature = "memocheck")]
                        self.audit_value("instantiation", v, |vc| {
                            vc.audit_bypass();
                            vc.inst(c, x)
                        });
                        v
                    }
                    Err(h) => {
                        stat!(self, inst_miss);
                        let v = self.inst(c, x)?;
                        self.t.insts.insert_new(h, k, v);
                        v
                    }
                }
            };
        }
        Ok(ft)
    }

    #[inline(never)]
    fn infer_slow(&mut self, env: Env<'t>, sub: Sub<'t>, e: ExprPtr<'t>, mode: Mode) -> R<V<'t>> {
        self.tick()?;
        let closed = e.closed();
        let raw = (e, sub, env.key());
        let mark = self.scoped;
        if closed {
            if !self.bypassed()
                && let Some(&h) = self.t.infer_closed[Mode::Check].get(&(e, sub))
                && self.admit(h)
            {
                stat!(self, closed_hit);
                return Ok(h.ty);
            }
            stat!(self, closed_miss);
            if mode == Mode::Only
                && !self.bypassed()
                && let Some(h) = self.t.infer_closed[Mode::Only].get(&(e, sub))
            {
                return Ok(h.ty);
            }
        }
        let env = if closed {
            Env::EMPTY
        } else if matches!(*e, Expr::Lam { .. } | Expr::Pi { .. } | Expr::Let { .. }) {
            self.trim(env, e)?
        } else {
            env
        };
        if !closed && env.key() != raw.2 && !self.bypassed() {
            let k = (e, sub, env.key());
            let hit = match self.t.infer_open[Mode::Check].get(&k).copied() {
                Some(h) if self.admit(h) => Some(h),
                _ if mode == Mode::Only => self.t.infer_open[Mode::Only].get(&k).copied(),
                _ => None,
            };
            if let Some(h) = hit {
                self.t.infer_open[mode].insert(raw, h);
                return Ok(h.ty);
            }
        }
        let proj = !closed && matches!(*e, Expr::App { .. }) && !self.bypassed();
        if proj && let Some(h) = self.infer_projected(env, sub, e, mode) {
            self.t.infer_open[mode].insert(raw, h);
            return Ok(h.ty);
        }
        #[cfg(feature = "memocheck")]
        self.audit_entered();
        let t = match *e {
            Expr::Var { idx, .. } => {
                let Some(v) = env.get(idx) else {
                    reject!(self, "unexpected bound variable")
                };
                self.type_of(v)?
            }
            Expr::Local { .. } => reject!(self, "unexpected local in syntax"),
            Expr::Sort { level, .. } => {
                if mode == Mode::Check {
                    self.check_level(level)?;
                }
                let l = self.subst_level(sub, level);
                let l = self.ctx.succ(l);
                self.mk(K::Sort(l), false)
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
                if mode == Mode::Check {
                    for &l in levels.as_ref() {
                        self.check_level(l)?;
                    }
                }
                let ls = self.ctx.subst_levels(levels, sub.ks, sub.vs);
                self.const_type(name, ls)?
            }
            Expr::App { .. } => 'app: {
                let mut args = [MaybeUninit::<ExprPtr<'t>>::uninit(); SPINE];
                let mut n = 0;
                let mut f = e;
                while let Expr::App { fun, arg, .. } = *f {
                    if n == SPINE {
                        break 'app self.infer_app_wide(env, sub, e, mode)?;
                    }
                    args[n].write(arg);
                    n += 1;
                    f = fun;
                }
                // SAFETY: the walk above wrote the first `n` arguments.
                let args = unsafe { &*(ptr::from_ref(&args[..n]) as *const [ExprPtr<'t>]) };
                self.infer_spine(env, sub, f, args, mode)?
            }
            Expr::Lam { ty, body, .. } => {
                let dom = self.eval(env, sub, ty)?;
                if mode == Mode::Check {
                    let s = self.infer(env, sub, ty, Mode::Check)?;
                    self.ensure_sort(s)?;
                    self.infer_binder(env, sub, dom, body, Mode::Check)?;
                }
                self.mk(
                    K::Pi(
                        dom,
                        Clo {
                            env,
                            sub,
                            body,
                            typed: true,
                        },
                    ),
                    dom.open || env.open(),
                )
            }
            Expr::Pi { ty, body, .. } => {
                let s = self.infer(env, sub, ty, mode)?;
                let s1 = self.ensure_sort(s)?;
                let dom = self.eval(env, sub, ty)?;
                let s = self.infer_binder(env, sub, dom, body, mode)?;
                let s2 = self.ensure_sort(s)?;
                let l = self.ctx.imax(s1, s2);
                self.mk(K::Sort(l), false)
            }
            Expr::Let { data, .. } if mode == Mode::Only || !self.nat_typed(data.ty) => {
                if mode == Mode::Check {
                    let s = self.infer(env, sub, data.ty, Mode::Check)?;
                    self.ensure_sort(s)?;
                    let tv = self.eval(env, sub, data.ty)?;
                    let at = self.infer(env, sub, data.val, Mode::Check)?;
                    ensure!(self, self.def_eq(at, tv)?, "let value type mismatch");
                }
                let v = self.eval(env, sub, data.val)?;
                let env1 = self.push(env, v);
                self.infer(env1, sub, data.body, mode)?
            }
            // A Nat let body sees a local, so closed literal folding never forces the value.
            Expr::Let { data, .. } => {
                let s = self.infer(env, sub, data.ty, Mode::Check)?;
                self.ensure_sort(s)?;
                let tv = self.eval(env, sub, data.ty)?;
                let at = self.infer(env, sub, data.val, Mode::Check)?;
                ensure!(self, self.def_eq(at, tv)?, "let value type mismatch");
                let v = self.eval(env, sub, data.val)?;
                let x = self.local(tv, Some(v));
                let env1 = self.push(env, x);
                let t = self.infer(env1, sub, data.body, Mode::Check)?;
                self.zeta(x, v, t)?
            }
            Expr::Proj {
                name, idx, e: s, ..
            } => {
                if mode == Mode::Check {
                    self.infer(env, sub, s, Mode::Check)?;
                }
                let sv = self.eval(env, sub, s)?;
                let p = self.mk(K::Neu(Head::Proj(name, idx, sv), &[]), sv.open);
                self.type_of(p)?
            }
            Expr::NatLit { .. } => self.literal_type(self.names.nat)?,
            Expr::StrLit { .. } => self.literal_type(self.names.string)?,
        };
        let s = Scoped {
            ty: t,
            uparams: if mode == Mode::Only || self.scoped == mark {
                LevelsPtr::new(&[])
            } else {
                self.uparams
            },
        };
        if closed {
            self.t.infer_closed[mode].insert((e, sub), s);
        } else {
            self.t.infer_open[mode].insert((e, sub, env.key()), s);
            if env.key() != raw.2 {
                self.t.infer_open[mode].insert(raw, s);
            }
            if proj {
                stat!(self, proj_put);
                self.t
                    .infer_proj
                    .insert((e, sub), Inferred { env, ty: s, mode });
            }
        }
        Ok(t)
    }
}

impl<'t, 'a: 't> Vc<'t, 'a> {
    /// An earlier result whose environment agrees with this one on every slot `e` reads.
    #[inline(never)]
    fn infer_projected(
        &mut self,
        env: Env<'t>,
        sub: Sub<'t>,
        e: ExprPtr<'t>,
        mode: Mode,
    ) -> Option<Scoped<'t>> {
        stat!(self, proj_probe);
        let &Inferred {
            env: o,
            ty,
            mode: m,
        } = self.t.infer_proj.probe(&(e, sub)).ok()?;
        if m == Mode::Only && mode == Mode::Check {
            return None;
        }
        let sl = self.slots(e)?;
        if !agree(o, env, sl) {
            return None;
        }
        if !self.admit(ty) {
            return None;
        }
        stat!(self, proj_hit);
        Some(ty)
    }

    /// Whether a cached type's parameters are in scope, recording the dependence if it has one.
    /// The frameless probes in `infer_fast` inline the two cheap cases of this.
    #[inline(always)]
    fn admit(&mut self, s: Scoped<'t>) -> bool {
        if !self.within(s.uparams) {
            return false;
        }
        if !s.uparams.is_empty() {
            self.scoped += 1;
        }
        true
    }
}

impl<'t, 'a: 't> Vc<'t, 'a> {
    fn nat_typed(&self, ty: ExprPtr<'t>) -> bool {
        matches!(*ty, Expr::Const { name, .. } if Some(name) == self.names.nat)
    }
}
