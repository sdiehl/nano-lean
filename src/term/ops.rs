//! Term operations: level arithmetic, name manipulation, lifting, instantiation
//! and universe substitution. All memoised against the sharing in the term DAG.

use super::ctx::Ctx;
use super::expr::Expr;
use super::level::Level;
use super::ptr::{ExprPtr, LevelPtr, LevelsPtr};
use crate::reject;

const OP_LIFT: u32 = 1 << 24;
const OP_INST: u32 = 2 << 24;
const OP_ABST: u32 = 4 << 24;

impl<'t, 'a: 't> Ctx<'t, 'a> {
    // Levels

    fn combine(&mut self, l: LevelPtr<'t>, r: LevelPtr<'t>) -> LevelPtr<'t> {
        match (*l, *r) {
            (Level::Zero, _) => r,
            (_, Level::Zero) => l,
            (Level::Succ(a, _), Level::Succ(b, _)) => {
                let p = self.combine(a, b);
                self.succ(p)
            }
            _ => self.max(l, r),
        }
    }

    pub fn simplify(&mut self, l: LevelPtr<'t>) -> LevelPtr<'t> {
        if matches!(*l, Level::Zero | Level::Param(..)) {
            return l;
        }
        if let Some(&r) = self.simp_cache.get(&l) {
            return r;
        }
        let r = match *l {
            Level::Zero | Level::Param(..) => l,
            Level::Succ(a, _) => {
                let a = self.simplify(a);
                self.succ(a)
            }
            Level::Max(a, b, _) => {
                let a = self.simplify(a);
                let b = self.simplify(b);
                self.combine(a, b)
            }
            Level::IMax(a, b, _) => {
                let a = self.simplify(a);
                let b = self.simplify(b);
                if self.is_zero(a) || self.is_one(a) {
                    b
                } else {
                    match *b {
                        Level::Zero => b,
                        Level::Succ(..) => self.combine(a, b),
                        _ => self.imax(a, b),
                    }
                }
            }
        };
        self.simp_cache.insert(l, r);
        r
    }

    pub fn subst_level(
        &mut self,
        l: LevelPtr<'t>,
        ks: LevelsPtr<'t>,
        vs: LevelsPtr<'t>,
    ) -> LevelPtr<'t> {
        match *l {
            Level::Zero => l,
            Level::Succ(a, _) => {
                let a = self.subst_level(a, ks, vs);
                self.succ(a)
            }
            Level::Max(a, b, _) => {
                let a = self.subst_level(a, ks, vs);
                let b = self.subst_level(b, ks, vs);
                self.max(a, b)
            }
            Level::IMax(a, b, _) => {
                let a = self.subst_level(a, ks, vs);
                let b = self.subst_level(b, ks, vs);
                self.imax(a, b)
            }
            Level::Param(..) => ks.iter().position(|k| *k == l).map_or(l, |i| vs[i]),
        }
    }

    pub fn subst_levels(
        &mut self,
        ls: LevelsPtr<'t>,
        ks: LevelsPtr<'t>,
        vs: LevelsPtr<'t>,
    ) -> LevelsPtr<'t> {
        if ks.is_empty() || ks == vs {
            return ls;
        }
        let out: Vec<_> = ls.iter().map(|&l| self.subst_level(l, ks, vs)).collect();
        self.levels(&out)
    }

    fn leq_cases(&mut self, p: LevelPtr<'t>, l: LevelPtr<'t>, r: LevelPtr<'t>, diff: i32) -> bool {
        let zero = self.zero();
        let sp = self.succ(p);
        let (ps, zs, ss) = (self.levels(&[p]), self.levels(&[zero]), self.levels(&[sp]));
        let l0 = self.subst_level(l, ps, zs);
        let r0 = self.subst_level(r, ps, zs);
        let (l0, r0) = (self.simplify(l0), self.simplify(r0));
        if !self.leq_core(l0, r0, diff) {
            return false;
        }
        let l1 = self.subst_level(l, ps, ss);
        let r1 = self.subst_level(r, ps, ss);
        let (l1, r1) = (self.simplify(l1), self.simplify(r1));
        self.leq_core(l1, r1, diff)
    }

    fn leq_core(&mut self, l: LevelPtr<'t>, r: LevelPtr<'t>, diff: i32) -> bool {
        match (*l, *r) {
            (Level::Zero, _) if diff >= 0 => true,
            (_, Level::Zero) if diff < 0 => false,
            (Level::Param(a, _), Level::Param(b, _)) => a == b && diff >= 0,
            (Level::Param(..), Level::Zero) => false,
            (Level::Zero, Level::Param(..)) => diff >= 0,
            (Level::Succ(a, _), _) => self.leq_core(a, r, diff - 1),
            (_, Level::Succ(b, _)) => self.leq_core(l, b, diff + 1),
            (Level::Max(a, b, _), _) => self.leq_core(a, r, diff) && self.leq_core(b, r, diff),
            (Level::Param(..) | Level::Zero, Level::Max(a, b, _)) => {
                self.leq_core(l, a, diff) || self.leq_core(l, b, diff)
            }
            (Level::IMax(a, b, _), Level::IMax(x, y, _)) if a == x && b == y && diff >= 0 => true,
            (Level::IMax(_, b, _), _) if b.is_param() => self.leq_cases(b, l, r, diff),
            (_, Level::IMax(_, y, _)) if y.is_param() => self.leq_cases(y, l, r, diff),
            (Level::IMax(a, b, _), _) if b.is_any_max() => {
                let d = self.distribute_imax(a, b);
                self.leq_core(d, r, diff)
            }
            (_, Level::IMax(x, y, _)) if y.is_any_max() => {
                let d = self.distribute_imax(x, y);
                self.leq_core(l, d, diff)
            }
            _ => reject!("universe comparison reached an unexpected form"),
        }
    }

    fn distribute_imax(&mut self, a: LevelPtr<'t>, b: LevelPtr<'t>) -> LevelPtr<'t> {
        match *b {
            Level::IMax(x, y, _) => {
                let l = self.imax(a, y);
                let r = self.imax(x, y);
                self.max(l, r)
            }
            Level::Max(x, y, _) => {
                let l = self.imax(a, x);
                let r = self.imax(a, y);
                let m = self.max(l, r);
                self.simplify(m)
            }
            _ => unreachable!(),
        }
    }

    pub fn leq(&mut self, l: LevelPtr<'t>, r: LevelPtr<'t>) -> bool {
        if l == r {
            return true;
        }
        let l = self.simplify(l);
        let r = self.simplify(r);
        self.leq_core(l, r, 0)
    }

    pub fn level_eq(&mut self, l: LevelPtr<'t>, r: LevelPtr<'t>) -> bool {
        l == r || (self.leq(l, r) && self.leq(r, l))
    }

    pub fn levels_eq(&mut self, xs: LevelsPtr<'t>, ys: LevelsPtr<'t>) -> bool {
        xs == ys
            || (xs.len() == ys.len()
                && xs.iter().zip(ys.iter()).all(|(&x, &y)| self.level_eq(x, y)))
    }

    pub fn is_zero(&mut self, l: LevelPtr<'t>) -> bool {
        let z = self.zero();
        self.leq(l, z)
    }

    fn is_one(&mut self, l: LevelPtr<'t>) -> bool {
        matches!(*l, Level::Succ(p, _) if self.is_zero(p))
    }

    // Names

    // Expressions

    fn fresh(&mut self) -> u32 {
        self.generation = self.generation.wrapping_add(1);
        self.generation
    }

    #[inline]
    fn memo_get(&self, key: (ExprPtr<'t>, u32), g: u32) -> Option<ExprPtr<'t>> {
        match self.memo.get(&key) {
            Some(&(k, r)) if k == g => Some(r),
            _ => None,
        }
    }

    fn lift_rec(&mut self, e: ExprPtr<'t>, cutoff: u16, amount: u16, g: u32) -> ExprPtr<'t> {
        if amount == 0 || e.nlb() <= cutoff {
            return e;
        }
        let key = (e, OP_LIFT | u32::from(cutoff));
        if let Some(r) = self.memo_get(key, g) {
            return r;
        }
        let r = match *e {
            Expr::Var { idx, .. } => self.var(
                idx.checked_add(amount)
                    .unwrap_or_else(|| reject!("variable index overflow")),
            ),
            Expr::App { fun, arg, .. } => {
                let f = self.lift_rec(fun, cutoff, amount, g);
                let a = self.lift_rec(arg, cutoff, amount, g);
                self.app(f, a)
            }
            Expr::Lam { ty, body, .. } => {
                let t = self.lift_rec(ty, cutoff, amount, g);
                let b = self.lift_rec(body, cutoff + 1, amount, g);
                self.lam(t, b)
            }
            Expr::Pi { ty, body, .. } => {
                let t = self.lift_rec(ty, cutoff, amount, g);
                let b = self.lift_rec(body, cutoff + 1, amount, g);
                self.pi(t, b)
            }
            Expr::Let { data, .. } => {
                let t = self.lift_rec(data.ty, cutoff, amount, g);
                let v = self.lift_rec(data.val, cutoff, amount, g);
                let b = self.lift_rec(data.body, cutoff + 1, amount, g);
                self.let_(t, v, b, data.nondep)
            }
            Expr::Proj {
                name, idx, e: s, ..
            } => {
                let s = self.lift_rec(s, cutoff, amount, g);
                self.proj(name, idx, s)
            }
            _ => e,
        };
        self.memo.insert(key, (g, r));
        r
    }

    /// Substitute `subs` for the outermost loose variables: `Var(i)` becomes
    /// `subs[len - 1 - i]`, variables beyond are lowered by `len`. Substituted
    /// terms may be open; they are lifted past the binders they are moved under.
    pub fn inst(&mut self, e: ExprPtr<'t>, subs: &[ExprPtr<'t>]) -> ExprPtr<'t> {
        if subs.is_empty() || e.closed() {
            return e;
        }
        let g = self.fresh();
        self.inst_rec(e, subs, 0, g)
    }

    pub fn inst1(&mut self, e: ExprPtr<'t>, s: ExprPtr<'t>) -> ExprPtr<'t> {
        self.inst(e, &[s])
    }

    fn inst_rec(&mut self, e: ExprPtr<'t>, subs: &[ExprPtr<'t>], off: u16, g: u32) -> ExprPtr<'t> {
        if e.nlb() <= off {
            return e;
        }
        let key = (e, OP_INST | u32::from(off));
        if let Some(r) = self.memo_get(key, g) {
            return r;
        }
        let r = match *e {
            Expr::Var { idx, .. } => {
                let i = usize::from(idx - off);
                if i < subs.len() {
                    self.lift_rec(subs[subs.len() - 1 - i], 0, off, g)
                } else {
                    self.var(idx - subs.len() as u16)
                }
            }
            Expr::App { fun, arg, .. } => {
                let f = self.inst_rec(fun, subs, off, g);
                let a = self.inst_rec(arg, subs, off, g);
                self.app(f, a)
            }
            Expr::Lam { ty, body, .. } => {
                let t = self.inst_rec(ty, subs, off, g);
                let b = self.inst_rec(body, subs, off + 1, g);
                self.lam(t, b)
            }
            Expr::Pi { ty, body, .. } => {
                let t = self.inst_rec(ty, subs, off, g);
                let b = self.inst_rec(body, subs, off + 1, g);
                self.pi(t, b)
            }
            Expr::Let { data, .. } => {
                let t = self.inst_rec(data.ty, subs, off, g);
                let v = self.inst_rec(data.val, subs, off, g);
                let b = self.inst_rec(data.body, subs, off + 1, g);
                self.let_(t, v, b, data.nondep)
            }
            Expr::Proj {
                name, idx, e: s, ..
            } => {
                let s = self.inst_rec(s, subs, off, g);
                self.proj(name, idx, s)
            }
            _ => e,
        };
        self.memo.insert(key, (g, r));
        r
    }

    /// Replace each of `locals` by a bound variable, the last one becoming `Var(0)`.
    pub fn abstract_locals(&mut self, e: ExprPtr<'t>, locals: &[ExprPtr<'t>]) -> ExprPtr<'t> {
        if locals.is_empty() || !e.has_local() {
            return e;
        }
        let g = self.fresh();
        self.abst_rec(e, locals, 0, g)
    }

    fn abst_rec(
        &mut self,
        e: ExprPtr<'t>,
        locals: &[ExprPtr<'t>],
        off: u16,
        g: u32,
    ) -> ExprPtr<'t> {
        if !e.has_local() {
            return e;
        }
        let key = (e, OP_ABST | u32::from(off));
        if let Some(r) = self.memo_get(key, g) {
            return r;
        }
        let r = match *e {
            Expr::Local { .. } => match locals.iter().rposition(|&l| l == e) {
                Some(i) => self.var(off + (locals.len() - 1 - i) as u16),
                None => e,
            },
            Expr::App { fun, arg, .. } => {
                let f = self.abst_rec(fun, locals, off, g);
                let a = self.abst_rec(arg, locals, off, g);
                self.app(f, a)
            }
            Expr::Lam { ty, body, .. } => {
                let t = self.abst_rec(ty, locals, off, g);
                let b = self.abst_rec(body, locals, off + 1, g);
                self.lam(t, b)
            }
            Expr::Pi { ty, body, .. } => {
                let t = self.abst_rec(ty, locals, off, g);
                let b = self.abst_rec(body, locals, off + 1, g);
                self.pi(t, b)
            }
            Expr::Let { data, .. } => {
                let t = self.abst_rec(data.ty, locals, off, g);
                let v = self.abst_rec(data.val, locals, off, g);
                let b = self.abst_rec(data.body, locals, off + 1, g);
                self.let_(t, v, b, data.nondep)
            }
            Expr::Proj {
                name, idx, e: s, ..
            } => {
                let s = self.abst_rec(s, locals, off, g);
                self.proj(name, idx, s)
            }
            _ => e,
        };
        self.memo.insert(key, (g, r));
        r
    }

    /// Replace universe parameters `ks` by `vs` throughout `e`.
    pub fn subst_expr_levels(
        &mut self,
        e: ExprPtr<'t>,
        ks: LevelsPtr<'t>,
        vs: LevelsPtr<'t>,
    ) -> ExprPtr<'t> {
        if ks.is_empty() || ks == vs {
            return e;
        }
        if matches!(
            *e,
            Expr::Var { .. } | Expr::NatLit { .. } | Expr::StrLit { .. }
        ) {
            return e;
        }
        if let Some(&r) = self.subst_cache.get(&(e, ks, vs)) {
            return r;
        }
        let r = match *e {
            Expr::Sort { level, .. } => {
                let l = self.subst_level(level, ks, vs);
                self.sort(l)
            }
            Expr::Const { name, levels, .. } => {
                let ls = self.subst_levels(levels, ks, vs);
                self.konst(name, ls)
            }
            Expr::App { fun, arg, .. } => {
                let f = self.subst_expr_levels(fun, ks, vs);
                let a = self.subst_expr_levels(arg, ks, vs);
                self.app(f, a)
            }
            Expr::Lam { ty, body, .. } => {
                let t = self.subst_expr_levels(ty, ks, vs);
                let b = self.subst_expr_levels(body, ks, vs);
                self.lam(t, b)
            }
            Expr::Pi { ty, body, .. } => {
                let t = self.subst_expr_levels(ty, ks, vs);
                let b = self.subst_expr_levels(body, ks, vs);
                self.pi(t, b)
            }
            Expr::Let { data, .. } => {
                let t = self.subst_expr_levels(data.ty, ks, vs);
                let v = self.subst_expr_levels(data.val, ks, vs);
                let b = self.subst_expr_levels(data.body, ks, vs);
                self.let_(t, v, b, data.nondep)
            }
            Expr::Proj {
                name, idx, e: s, ..
            } => {
                let s = self.subst_expr_levels(s, ks, vs);
                self.proj(name, idx, s)
            }
            _ => e,
        };
        self.subst_cache.insert((e, ks, vs), r);
        r
    }

    /// Split an application spine into head and arguments.
    pub fn unfold_apps(&self, mut e: ExprPtr<'t>) -> (ExprPtr<'t>, Vec<ExprPtr<'t>>) {
        let mut args = Vec::with_capacity(e.num_args());
        while let Expr::App { fun, arg, .. } = *e {
            args.push(arg);
            e = fun;
        }
        args.reverse();
        (e, args)
    }

    /// Strip `n` leading Pi binders, instantiating them with `args`.
    pub fn inst_pis(&mut self, mut e: ExprPtr<'t>, args: &[ExprPtr<'t>]) -> ExprPtr<'t> {
        for _ in args {
            match *e {
                Expr::Pi { body, .. } => e = body,
                _ => reject!("expected a Pi binder"),
            }
        }
        self.inst(e, args)
    }

    /// Instantiate a declaration's type with concrete universe levels.
    pub fn declar_type(
        &mut self,
        d: &super::decl::Declar<'t>,
        levels: LevelsPtr<'t>,
    ) -> ExprPtr<'t> {
        self.subst_expr_levels(d.ty(), d.uparams(), levels)
    }
}
