use super::value::*;
use super::{R, Vc, stat};
use crate::term::decl::Declar;
use crate::term::expr::{Expr, WIDE};
use crate::term::ptr::ExprPtr;
use crate::{ensure, reject};
use smallvec::SmallVec;
use std::cell::Cell;

/// Node chains up to this depth are kept as they are when dense.
const SHALLOW: u32 = 8;

impl<'t, 'a: 't> Vc<'t, 'a> {
    pub(crate) fn push(&mut self, env: Env<'t>, v: V<'t>) -> Env<'t> {
        stat!(self, push_req);
        let k = (key(v), env.key());
        let open = v.open || env.open();
        if let Some(&e) = self.t.envs[usize::from(open)].get(&k) {
            return e;
        }
        stat!(self, push_new);
        let e = Env::new(self.ctx.arena.alloc(EnvObj::Node(EnvNode {
            head: v,
            tail: env,
            open,
            depth: env.depth() + 1,
            len: env.size() as u32 + 1,
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
        #[cfg(feature = "vstats")]
        match *e {
            Expr::App { .. } => self.stats.ev_app += 1,
            Expr::Lam { .. } => self.stats.ev_lam += 1,
            Expr::Pi { .. } => self.stats.ev_pi += 1,
            Expr::Let { .. } => self.stats.ev_let += 1,
            _ => self.stats.ev_other += 1,
        }
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
        stat!(self, trims);
        let sup = self.slots(e);
        let Some((max, len)) = sup.bounds() else {
            return Env::EMPTY;
        };
        let n = usize::from(max) + 1;
        if len == n && env.size() == n && env.depth() <= SHALLOW {
            return env;
        }
        let mut buf = SmallVec::<[V<'t>; 32]>::from_elem(self.dummy, n);
        let mut it = sup.peekable();
        let mut e = env;
        let mut at = 0u16;
        while let Some(&j) = it.peek() {
            match e.view() {
                View::Nil => break,
                View::Node(node) => {
                    if j == at {
                        buf[usize::from(j)] = node.head;
                        it.next();
                    }
                    e = node.tail;
                    at += 1;
                }
                View::Frame(f) => {
                    for j in it.by_ref() {
                        match f.vals.get(usize::from(j - at)) {
                            Some(&v) => buf[usize::from(j)] = v,
                            None => reject!("unexpected bound variable"),
                        }
                    }
                }
            }
        }
        ensure!(it.peek().is_none(), "unexpected bound variable");
        self.frame(&buf)
    }

    fn frame(&mut self, vals: &[V<'t>]) -> Env<'t> {
        stat!(self, frame_req);
        let open = vals.iter().any(|v| v.open);
        let o = usize::from(open);
        if let Some(&f) = self.t.frames[o].get(super::Ptrs::new(vals)) {
            return f;
        }
        stat!(self, frame_new);
        let vals: &'t [V<'t>] = self.ctx.arena.alloc_slice_copy(vals);
        let f = Env::new(self.ctx.arena.alloc(EnvObj::Frame(Frame { vals, open })));
        self.t.frames[o].insert(super::Ptrs::new(vals), f);
        f
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
        !c.body.closed() && self.slots(c.body).next() == Some(0)
    }

    pub(crate) fn apply(&mut self, mut f: V<'t>, args: &[V<'t>]) -> R<V<'t>> {
        let mut i = 0;
        while i < args.len() {
            self.tick()?;
            match f.k {
                K::Lam(_, c) if !c.typed => {
                    // Bind successive arguments through nested lambdas and
                    // evaluate the innermost body once, skipping the
                    // intermediate closures.
                    stat!(self, applies);
                    stat!(self, beta_runs);
                    let (mut env, mut body) = (self.push(c.env, args[i]), c.body);
                    i += 1;
                    while i < args.len()
                        && let Expr::Lam { body: b, .. } = *body
                    {
                        self.tick()?;
                        stat!(self, beta_chain);
                        env = self.push(env, args[i]);
                        body = b;
                        i += 1;
                    }
                    f = self.eval(env, c.sub, body)?;
                }
                K::Lam(_, c) => {
                    f = self.inst(c, args[i])?;
                    i += 1;
                }
                K::Neu(h, sp) => {
                    stat!(self, beta_neu);
                    let rest = &args[i..];
                    #[cfg(feature = "vstats")]
                    {
                        self.stats.spine_old += sp.len() as u64;
                        self.stats.spine_new_args += rest.len() as u64;
                        if sp.is_empty() {
                            self.stats.spine_empty_prefix += 1;
                        }
                    }
                    let open = f.open || rest.iter().any(|a| a.open);
                    let all = if sp.is_empty() {
                        self.spine(rest)
                    } else {
                        let all: SmallVec<[V<'t>; 16]> = sp.iter().chain(rest).copied().collect();
                        self.spine(&all)
                    };
                    return Ok(self.mk(K::Neu(h, all), open));
                }
                _ => reject!("expected a function"),
            }
        }
        Ok(f)
    }

    /// Loose bound variables of `e` in ascending order.
    pub(crate) fn slots(&mut self, e: ExprPtr<'t>) -> Slots<'t> {
        #[cfg(debug_assertions)]
        assert!(e.sup() == WIDE || Slots::Mask(e.sup()).eq(naive_support(e)));
        match e.sup() {
            WIDE => Slots::Wide(self.support_of(e).iter()),
            m => Slots::Mask(m),
        }
    }

    fn support_of(&mut self, e: ExprPtr<'t>) -> &'t [u16] {
        if let Some(&s) = self.t.support.get(&e) {
            return s;
        }
        let mut slots = Vec::new();
        match *e {
            Expr::Var { idx, .. } => slots.push(idx),
            Expr::App { fun, arg, .. } => {
                slots.extend(self.slots(fun));
                slots.extend(self.slots(arg));
            }
            Expr::Lam { ty, body, .. } | Expr::Pi { ty, body, .. } => {
                slots.extend(self.slots(ty));
                slots.extend(self.slots(body).filter_map(|i| i.checked_sub(1)));
            }
            Expr::Let { data, .. } => {
                slots.extend(self.slots(data.ty));
                slots.extend(self.slots(data.val));
                slots.extend(self.slots(data.body).filter_map(|i| i.checked_sub(1)));
            }
            Expr::Proj { e, .. } => slots.extend(self.slots(e)),
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

/// Ascending loose bound variables: an inline mask, or a memoized wide list.
#[derive(Clone)]
pub(crate) enum Slots<'t> {
    Mask(u32),
    Wide(std::slice::Iter<'t, u16>),
}

impl Slots<'_> {
    /// Largest slot and slot count, if any.
    fn bounds(&self) -> Option<(u16, usize)> {
        match self {
            Slots::Mask(0) => None,
            Slots::Mask(m) => Some((31 - m.leading_zeros() as u16, m.count_ones() as usize)),
            Slots::Wide(it) => it.as_slice().last().map(|&m| (m, it.len())),
        }
    }
}

impl Iterator for Slots<'_> {
    type Item = u16;
    #[inline]
    fn next(&mut self) -> Option<u16> {
        match self {
            Slots::Mask(m) => (*m != 0).then(|| {
                let i = m.trailing_zeros() as u16;
                *m &= *m - 1;
                i
            }),
            Slots::Wide(it) => it.next().copied(),
        }
    }
}

#[cfg(debug_assertions)]
fn naive_support(e: ExprPtr<'_>) -> Vec<u16> {
    let under = |b| {
        naive_support(b)
            .into_iter()
            .filter_map(|i: u16| i.checked_sub(1))
    };
    let mut out: Vec<u16> = match *e {
        _ if e.closed() => vec![],
        Expr::Var { idx, .. } => vec![idx],
        Expr::App { fun, arg, .. } => [naive_support(fun), naive_support(arg)].concat(),
        Expr::Lam { ty, body, .. } | Expr::Pi { ty, body, .. } => {
            naive_support(ty).into_iter().chain(under(body)).collect()
        }
        Expr::Let { data, .. } => [naive_support(data.ty), naive_support(data.val)]
            .concat()
            .into_iter()
            .chain(under(data.body))
            .collect(),
        Expr::Proj { e, .. } => naive_support(e),
        _ => vec![],
    };
    out.sort_unstable();
    out.dedup();
    out
}
