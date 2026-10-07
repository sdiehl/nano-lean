use super::value::*;
use super::{R, Vc, stat};
use crate::term::decl::{Constructor, Declar, Inductive};
use crate::term::expr::Expr;
use crate::term::ptr::{ExprPtr, LevelPtr, LevelsPtr, NamePtr};
use crate::{ensure, reject};

impl<'t, 'a: 't> Vc<'t, 'a> {
    pub(crate) fn ensure_sort(&mut self, t: V<'t>) -> R<LevelPtr<'t>> {
        if let K::Sort(l) = t.k {
            return Ok(l);
        }
        match self.whnf(t)?.k {
            K::Sort(l) => Ok(l),
            _ => reject!("expected a sort"),
        }
    }

    pub(crate) fn ensure_pi(&mut self, t: V<'t>) -> R<(V<'t>, Clo<'t>)> {
        if let K::Pi(d, c) = t.k {
            return Ok((d, c));
        }
        match self.whnf(t)?.k {
            K::Pi(d, c) => Ok((d, c)),
            _ => reject!("expected a function type"),
        }
    }

    /// Whether `t` is a proposition, i.e. its type is `Prop`.
    pub(crate) fn is_prop(&mut self, t: V<'t>) -> R<bool> {
        let s = self.type_of(t)?;
        let s = self.whnf(s)?;
        Ok(match s.k {
            K::Sort(l) => {
                let z = self.ctx.zero();
                self.ctx.level_eq(l, z)
            }
            _ => false,
        })
    }

    pub(crate) fn structure_like(
        &self,
        n: NamePtr<'t>,
    ) -> Option<(Inductive<'t>, Constructor<'t>)> {
        self.single_ctor(n).filter(|(i, _)| !i.is_rec)
    }

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

    fn literal_type(&mut self, n: Option<NamePtr<'t>>) -> R<V<'t>> {
        let ty = self.konst0(n);
        let s = self.type_of(ty)?;
        let z = self.ctx.zero();
        let one = self.ctx.succ(z);
        let expected = self.mk(K::Sort(one), false);
        ensure!(self.def_eq(s, expected)?, "invalid literal type");
        Ok(ty)
    }

    /// Type of a value, without syntax.
    pub(crate) fn type_of(&mut self, v: V<'t>) -> R<V<'t>> {
        if let Some(&t) = self.t.type_of.get(&key(v)) {
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
                let saved = self.depth;
                let x = self.binder_local(d);
                let s2 = self.inst(c, x).and_then(|b| self.type_of(b));
                self.depth = saved;
                let s2 = s2?;
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
                    Head::Local(_, ty) => ty,
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
        self.t.type_of.insert(key(v), t);
        Ok(t)
    }

    fn proj_type(&mut self, name: NamePtr<'t>, idx: u16, s: V<'t>) -> R<V<'t>> {
        let st = self.type_of(s)?;
        let is_prop = self.is_prop(st)?;
        let st = self.whnf(st)?;
        let K::Neu(Head::Const(iname, ls), args) = st.k else {
            reject!("projection of a non-structure")
        };
        ensure!(iname == name, "projection type mismatch");
        let Some((ind, ctor)) = self.single_ctor(name) else {
            reject!("projection of a non-structure")
        };
        ensure!(
            args.len() == usize::from(ind.num_params),
            "projection of a non-structure"
        );
        let mut r = self.const_type(ctor.info.name, ls)?;
        for &a in args {
            let K::Pi(_, c) = r.k else {
                reject!("expected a function type")
            };
            r = self.inst(c, a)?;
        }
        for i in 0..idx {
            let (d, c) = match self.whnf(r)?.k {
                K::Pi(d, c) => (d, c),
                _ => reject!("invalid projection"),
            };
            if self.uses_arg(c) {
                ensure!(!is_prop || self.is_prop(d)?, "invalid projection");
                let p = self.proj(name, i, s);
                r = self.inst(c, p)?;
            } else {
                let dummy = self.dummy;
                r = self.inst(c, dummy)?;
            }
        }
        let K::Pi(d, _) = self.whnf(r)?.k else {
            reject!("invalid projection")
        };
        ensure!(!is_prop || self.is_prop(d)?, "invalid projection");
        Ok(d)
    }

    /// Infer the type of syntax `e` under `env`. Check mode validates; infer-only
    /// assumes `e` is well typed.
    pub(crate) fn infer(
        &mut self,
        env: Env<'t>,
        sub: Sub<'t>,
        e: ExprPtr<'t>,
        only: bool,
    ) -> R<V<'t>> {
        self.tick()?;
        if let Expr::Var { idx, .. } = *e {
            let v = env
                .get(idx)
                .unwrap_or_else(|| reject!("unexpected bound variable"));
            return match v.k {
                K::Neu(Head::Local(_, ty), []) => Ok(ty),
                _ => self.type_of(v),
            };
        }
        let closed = e.closed();
        let raw = (e, sub, env.key());
        let mark = self.scoped;
        if closed {
            if let Some(&(t, s)) = self.t.infer_closed[0].get(&(e, sub))
                && self.within(s)
            {
                stat!(self, closed_hit);
                if !s.is_empty() {
                    self.scoped += 1;
                }
                return Ok(t);
            }
            stat!(self, closed_miss);
            if only && let Some(&(t, _)) = self.t.infer_closed[1].get(&(e, sub)) {
                return Ok(t);
            }
        } else if let Some(&t) = self.t.infer_open[0].get(&raw) {
            // Open entries do not record whether they met a parameter.
            self.scoped += 1;
            return Ok(t);
        } else if only && let Some(&t) = self.t.infer_open[1].get(&raw) {
            return Ok(t);
        }
        let env = if closed {
            Env::EMPTY
        } else if matches!(*e, Expr::Lam { .. } | Expr::Pi { .. } | Expr::Let { .. }) {
            self.trim(env, e)
        } else {
            env
        };
        if !closed && env.key() != raw.2 {
            let k = (e, sub, env.key());
            let hit = match self.t.infer_open[0].get(&k) {
                Some(&t) => {
                    self.scoped += 1;
                    Some(t)
                }
                None if only => self.t.infer_open[1].get(&k).copied(),
                None => None,
            };
            if let Some(t) = hit {
                self.t.infer_open[usize::from(only)].insert(raw, t);
                return Ok(t);
            }
        }
        let t = match *e {
            Expr::Var { idx, .. } => {
                let v = env
                    .get(idx)
                    .unwrap_or_else(|| reject!("unexpected bound variable"));
                self.type_of(v)?
            }
            Expr::Local { .. } => reject!("unexpected local in syntax"),
            Expr::Sort { level, .. } => {
                if !only {
                    self.check_level(level);
                }
                let l = if sub.is_id() {
                    level
                } else {
                    self.ctx.subst_level(level, sub.ks, sub.vs)
                };
                let l = self.ctx.succ(l);
                self.mk(K::Sort(l), false)
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
                let ls = self.ctx.subst_levels(levels, sub.ks, sub.vs);
                self.const_type(name, ls)?
            }
            Expr::App { .. } => {
                let mut args = smallvec::SmallVec::<[ExprPtr<'t>; 8]>::new();
                let mut f = e;
                while let Expr::App { fun, arg, .. } = *f {
                    args.push(arg);
                    f = fun;
                }
                let mut ft = self.infer(env, sub, f, only)?;
                for &a in args.iter().rev() {
                    self.tick()?;
                    let (d, c) = self.ensure_pi(ft)?;
                    if !only {
                        let at = self.infer(env, sub, a, false)?;
                        ensure!(self.def_eq(at, d)?, "application type mismatch");
                    }
                    let x = if self.uses_arg(c) {
                        self.eval(env, sub, a)?
                    } else {
                        self.dummy
                    };
                    ft = self.inst(c, x)?;
                }
                ft
            }
            Expr::Lam { ty, body, .. } => {
                let dom = self.eval(env, sub, ty)?;
                if !only {
                    let s = self.infer(env, sub, ty, false)?;
                    self.ensure_sort(s)?;
                    let saved = self.depth;
                    let x = self.binder_local(dom);
                    let env1 = self.push(env, x);
                    let r = self.infer(env1, sub, body, false);
                    self.depth = saved;
                    r?;
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
                let s = self.infer(env, sub, ty, only)?;
                let s1 = self.ensure_sort(s)?;
                let dom = self.eval(env, sub, ty)?;
                let saved = self.depth;
                let x = self.binder_local(dom);
                let env1 = self.push(env, x);
                let s = self.infer(env1, sub, body, only);
                self.depth = saved;
                let s = s?;
                let s2 = self.ensure_sort(s)?;
                let l = self.ctx.imax(s1, s2);
                self.mk(K::Sort(l), false)
            }
            Expr::Let { data, .. } => {
                if !only {
                    let s = self.infer(env, sub, data.ty, false)?;
                    self.ensure_sort(s)?;
                    let tv = self.eval(env, sub, data.ty)?;
                    let at = self.infer(env, sub, data.val, false)?;
                    ensure!(self.def_eq(at, tv)?, "let value type mismatch");
                }
                let v = self.eval(env, sub, data.val)?;
                let env1 = self.push(env, v);
                self.infer(env1, sub, data.body, only)?
            }
            Expr::Proj {
                name, idx, e: s, ..
            } => {
                if !only {
                    self.infer(env, sub, s, false)?;
                }
                let sv = self.eval(env, sub, s)?;
                let p = self.mk(K::Neu(Head::Proj(name, idx, sv), &[]), sv.open);
                self.type_of(p)?
            }
            Expr::NatLit { .. } => self.literal_type(self.names.nat)?,
            Expr::StrLit { .. } => self.literal_type(self.names.string)?,
        };
        if closed {
            let s = if only || self.scoped == mark {
                LevelsPtr::new(&[])
            } else {
                self.uparams
            };
            self.t.infer_closed[usize::from(only)].insert((e, sub), (t, s));
        } else {
            self.t.infer_open[usize::from(only)].insert((e, sub, env.key()), t);
            if env.key() != raw.2 {
                self.t.infer_open[usize::from(only)].insert(raw, t);
            }
        }
        Ok(t)
    }
}
