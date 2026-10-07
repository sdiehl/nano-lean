use super::value::*;
use super::{R, Vc, stat};
use crate::term::decl::Declar;
use crate::term::expr::Expr;
use crate::term::ptr::ExprPtr;
use crate::{ensure, reject};
use smallvec::SmallVec;
use std::cell::Cell;

impl<'t, 'a: 't> Vc<'t, 'a> {
    pub(crate) fn push(&mut self, env: Env<'t>, v: V<'t>) -> Env<'t> {
        let k = (key(v), env.key());
        let open = v.open || env.open();
        if let Some(&e) = self.t.envs[usize::from(open)].get(&k) {
            return e;
        }
        let e = Env(Some(&*self.ctx.arena.alloc(EnvNode {
            head: v,
            tail: env,
            open,
        })));
        self.t.envs[usize::from(open)].insert(k, e);
        e
    }

    pub(crate) fn eval(&mut self, env: Env<'t>, sub: Sub<'t>, e: ExprPtr<'t>) -> R<V<'t>> {
        if let Expr::Var { idx, .. } = *e {
            return Ok(env
                .get(idx)
                .unwrap_or_else(|| reject!("unexpected bound variable")));
        }
        let closed = e.closed();
        let env = if closed { Env::EMPTY } else { env };
        if let Some(&v) = if closed {
            self.t.eval_closed.get(&(e, sub))
        } else {
            self.t.eval_memo.get(&(e, sub, env.key()))
        } {
            stat!(self, memo_hits);
            return Ok(v);
        }
        stat!(self, evals);
        self.work();
        let v = match *e {
            Expr::Var { idx, .. } => env
                .get(idx)
                .unwrap_or_else(|| reject!("unexpected bound variable")),
            Expr::Sort { level, .. } => {
                let l = if sub.is_id() {
                    level
                } else {
                    self.ctx.subst_level(level, sub.ks, sub.vs)
                };
                self.mk(K::Sort(l), false)
            }
            Expr::Const { name, levels, .. } => {
                let ls = self.ctx.subst_levels(levels, sub.ks, sub.vs);
                self.mk(K::Neu(Head::Const(name, ls), &[]), false)
            }
            Expr::App { .. } => {
                let mut args = SmallVec::<[ExprPtr<'t>; 8]>::new();
                let mut f = e;
                while let Expr::App { fun, arg, .. } = *f {
                    args.push(arg);
                    f = fun;
                }
                let fv = self.eval(env, sub, f)?;
                let mut vs = SmallVec::<[V<'t>; 8]>::with_capacity(args.len());
                for &a in args.iter().rev() {
                    vs.push(self.eval(env, sub, a)?);
                }
                self.apply(fv, &vs)?
            }
            Expr::Lam { ty, body, .. } => {
                let env = self.trim(env, e);
                let dom = match self.t.lazies[usize::from(env.open())].get(&(env.key(), sub, ty)) {
                    Some(&d) => d,
                    None => {
                        let d = &*self.ctx.arena.alloc(Lazy {
                            env,
                            sub,
                            e: ty,
                            val: Cell::new(None),
                        });
                        self.t.lazies[usize::from(env.open())].insert((env.key(), sub, ty), d);
                        d
                    }
                };
                self.mk(
                    K::Lam(
                        dom,
                        Clo {
                            env,
                            sub,
                            body,
                            typed: false,
                        },
                    ),
                    env.open(),
                )
            }
            Expr::Pi { ty, body, .. } => {
                let env = self.trim(env, e);
                let d = self.eval(env, sub, ty)?;
                self.mk(
                    K::Pi(
                        d,
                        Clo {
                            env,
                            sub,
                            body,
                            typed: false,
                        },
                    ),
                    d.open || env.open(),
                )
            }
            Expr::Let { data, .. } => {
                let v = self.eval(env, sub, data.val)?;
                let env = self.push(env, v);
                self.eval(env, sub, data.body)?
            }
            Expr::Proj {
                name, idx, e: s, ..
            } => {
                let s = self.eval(env, sub, s)?;
                self.proj(name, idx, s)
            }
            Expr::NatLit { n, .. } => self.mk(K::Nat(n.as_ref()), false),
            Expr::StrLit { s, .. } => self.mk(K::Str(s.as_ref().s), false),
            Expr::Local { .. } => reject!("unexpected local in syntax"),
        };
        if closed {
            self.t.eval_closed.insert((e, sub), v);
        } else {
            self.t.eval_memo.insert((e, sub, env.key()), v);
        }
        Ok(v)
    }

    /// Keep only the slots `e` reads, so closures equal up to unused
    /// captures share one value.
    pub(crate) fn trim(&mut self, env: Env<'t>, e: ExprPtr<'t>) -> Env<'t> {
        let sup = self.support_of(e);
        let Some(&max) = sup.last() else {
            return Env::EMPTY;
        };
        if sup.len() == usize::from(max) + 1 {
            return env;
        }
        let mut vals = [self.dummy; 64];
        let mut keep = Vec::new();
        let vals: &mut [V<'t>] = if max < 64 {
            &mut vals[..=usize::from(max)]
        } else {
            keep.resize(usize::from(max) + 1, self.dummy);
            &mut keep
        };
        let (mut node, mut i, mut it) = (env.0, 0u16, sup.iter().peekable());
        while let (Some(n), Some(&&j)) = (node, it.peek()) {
            if i == j {
                vals[usize::from(i)] = n.head;
                it.next();
            }
            node = n.tail.0;
            i += 1;
        }
        ensure!(it.peek().is_none(), "unexpected bound variable");
        let mut out = Env::EMPTY;
        for &v in vals.iter().rev() {
            out = self.push(out, v);
        }
        out
    }

    /// A projection value, reduced when the structure is already a constructor application.
    pub(crate) fn proj(
        &mut self,
        name: crate::term::ptr::NamePtr<'t>,
        idx: u16,
        s: V<'t>,
    ) -> V<'t> {
        if let K::Neu(Head::Const(c, _), args) = s.k
            && let Some(Declar::Ctor(k)) = self.declar(c)
            && let Some(&f) = args.get(usize::from(k.num_params) + usize::from(idx))
        {
            return f;
        }
        self.mk(K::Neu(Head::Proj(name, idx, s), &[]), s.open)
    }

    pub(crate) fn force(&mut self, l: &'t Lazy<'t>) -> R<V<'t>> {
        if let Some(v) = l.val.get() {
            return Ok(v);
        }
        let v = self.eval(l.env, l.sub, l.e)?;
        l.val.set(Some(v));
        Ok(v)
    }

    pub(crate) fn inst(&mut self, c: Clo<'t>, x: V<'t>) -> R<V<'t>> {
        stat!(self, applies);
        let env = self.push(c.env, x);
        if c.typed {
            self.infer(env, c.sub, c.body, true)
        } else {
            self.eval(env, c.sub, c.body)
        }
    }

    /// Whether a closure body reads its own argument.
    pub(crate) fn uses_arg(&mut self, c: Clo<'t>) -> bool {
        !c.body.closed() && self.support_of(c.body).first() == Some(&0)
    }

    pub(crate) fn apply(&mut self, mut f: V<'t>, args: &[V<'t>]) -> R<V<'t>> {
        let mut i = 0;
        while i < args.len() {
            self.tick()?;
            match f.k {
                K::Lam(_, c) => {
                    f = self.inst(c, args[i])?;
                    i += 1;
                }
                K::Neu(h, sp) => {
                    let rest = &args[i..];
                    let open = f.open || rest.iter().any(|a| a.open);
                    let all: SmallVec<[V<'t>; 16]> = sp.iter().chain(rest).copied().collect();
                    let all = self.spine(&all);
                    return Ok(self.mk(K::Neu(h, all), open));
                }
                _ => reject!("expected a function"),
            }
        }
        Ok(f)
    }

    pub(crate) fn support_of(&mut self, e: ExprPtr<'t>) -> &'t [u16] {
        if e.closed() {
            return &[];
        }
        if let Some(&s) = self.t.support.get(&e) {
            return s;
        }
        let mut slots = Vec::new();
        match *e {
            Expr::Var { idx, .. } => slots.push(idx),
            Expr::App { fun, arg, .. } => {
                slots.extend_from_slice(self.support_of(fun));
                slots.extend_from_slice(self.support_of(arg));
            }
            Expr::Lam { ty, body, .. } | Expr::Pi { ty, body, .. } => {
                slots.extend_from_slice(self.support_of(ty));
                slots.extend(
                    self.support_of(body)
                        .iter()
                        .filter_map(|i| i.checked_sub(1)),
                );
            }
            Expr::Let { data, .. } => {
                slots.extend_from_slice(self.support_of(data.ty));
                slots.extend_from_slice(self.support_of(data.val));
                slots.extend(
                    self.support_of(data.body)
                        .iter()
                        .filter_map(|i| i.checked_sub(1)),
                );
            }
            Expr::Proj { e, .. } => slots.extend_from_slice(self.support_of(e)),
            _ => {}
        }
        slots.sort_unstable();
        slots.dedup();
        let s = &*self.ctx.arena.alloc_slice_copy(&slots);
        self.t.support.insert(e, s);
        s
    }

    /// The type of a constant at given levels, evaluated once per declaration.
    pub(crate) fn const_type(
        &mut self,
        n: crate::term::ptr::NamePtr<'t>,
        ls: crate::term::ptr::LevelsPtr<'t>,
    ) -> R<V<'t>> {
        if let Some(&v) = self.t.const_ty.get(&(n, ls)) {
            return Ok(v);
        }
        let Some(d) = self.declar(n) else {
            reject!("unknown constant {}", n.as_ref())
        };
        let sub = self.sub(d.uparams(), ls);
        let v = self.eval(Env::EMPTY, sub, d.ty())?;
        self.t.const_ty.insert((n, ls), v);
        Ok(v)
    }
}
