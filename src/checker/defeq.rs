use super::Tc;
use crate::term::decl::{Declar, Hint};
use crate::term::expr::Expr;
use crate::term::ptr::ExprPtr;
use std::cmp::Ordering;

/// Which side lazy delta unfolds first: `Less` unfolds the left.
fn unfold_order(t: Hint, s: Hint) -> Ordering {
    match (t, s) {
        (Hint::Regular(a), Hint::Regular(b)) => b.cmp(&a),
        (Hint::Opaque, Hint::Opaque) | (Hint::Abbrev, Hint::Abbrev) => Ordering::Equal,
        (Hint::Opaque, _) | (_, Hint::Abbrev) => Ordering::Greater,
        (_, Hint::Opaque) | (Hint::Abbrev, _) => Ordering::Less,
    }
}

impl<'t, 'a: 't> Tc<'t, 'a> {
    pub fn def_eq(&mut self, t: ExprPtr<'t>, s: ExprPtr<'t>) -> bool {
        if t == s || self.eq_cache.contains(&(t, s)) {
            return true;
        }
        let r = self.def_eq_core(t, s);
        if r {
            self.eq_cache.insert((t, s));
            self.eq_cache.insert((s, t));
        }
        r
    }

    fn quick(&mut self, t: ExprPtr<'t>, s: ExprPtr<'t>) -> Option<bool> {
        if t == s || self.eq_cache.contains(&(t, s)) {
            return Some(true);
        }
        match (*t, *s) {
            (Expr::Lam { .. }, Expr::Lam { .. }) | (Expr::Pi { .. }, Expr::Pi { .. }) => {
                Some(self.def_eq_binding(t, s))
            }
            (Expr::Sort { level: a, .. }, Expr::Sort { level: b, .. }) => {
                Some(self.ctx.level_eq(a, b))
            }
            (Expr::NatLit { .. }, Expr::NatLit { .. })
            | (Expr::StrLit { .. }, Expr::StrLit { .. }) => Some(false),
            _ => None,
        }
    }

    fn def_eq_binding(&mut self, mut t: ExprPtr<'t>, mut s: ExprPtr<'t>) -> bool {
        let pi = t.is_pi();
        let mut locals = Vec::new();
        while let Expr::Lam {
            ty: tt, body: tb, ..
        }
        | Expr::Pi {
            ty: tt, body: tb, ..
        } = *t
        {
            let (Expr::Lam {
                ty: st, body: sb, ..
            }
            | Expr::Pi {
                ty: st, body: sb, ..
            }) = *s
            else {
                break;
            };
            if t.is_pi() != pi || s.is_pi() != pi {
                break;
            }
            let sd = self.ctx.inst(st, &locals);
            if tt != st {
                let td = self.ctx.inst(tt, &locals);
                if !self.def_eq(td, sd) {
                    return false;
                }
            }
            let l = if tb.nlb() > 0 || sb.nlb() > 0 {
                self.fresh_local(sd)
            } else {
                self.ctx.prop()
            };
            locals.push(l);
            t = tb;
            s = sb;
        }
        let t = self.ctx.inst(t, &locals);
        let s = self.ctx.inst(s, &locals);
        self.def_eq(t, s)
    }

    fn def_eq_core(&mut self, t: ExprPtr<'t>, s: ExprPtr<'t>) -> bool {
        if let Some(r) = self.quick(t, s) {
            return r;
        }
        if let Some(bt) = self.names.bool_true
            && !t.has_local()
            && s.const_name() == Some(bt)
            && self.whnf(t).const_name() == Some(bt)
        {
            return true;
        }
        let tn = self.whnf_core(t, true);
        let sn = self.whnf_core(s, true);
        if (tn != t || sn != s)
            && let Some(r) = self.quick(tn, sn)
        {
            return r;
        }
        if let Some(r) = self.proof_irrel(tn, sn) {
            return r;
        }
        let (tn, sn) = match self.lazy_delta(tn, sn) {
            Ok(r) => return r,
            Err(p) => p,
        };
        match (*tn, *sn) {
            (
                Expr::Const {
                    name: a,
                    levels: la,
                    ..
                },
                Expr::Const {
                    name: b,
                    levels: lb,
                    ..
                },
            ) => {
                if a == b && self.ctx.levels_eq(la, lb) {
                    return true;
                }
            }
            (Expr::Proj { idx: i, e: x, .. }, Expr::Proj { idx: j, e: y, .. })
                if i == j && self.def_eq(x, y) =>
            {
                return true;
            }
            _ => {}
        }
        let tnn = self.whnf_core(tn, false);
        let snn = self.whnf_core(sn, false);
        if tnn != tn || snn != sn {
            return self.def_eq_core(tnn, snn);
        }
        if self.def_eq_app(tn, sn)
            || self.eta(tn, sn)
            || self.eta(sn, tn)
            || self.eta_struct(tn, sn)
            || self.eta_struct(sn, tn)
        {
            return true;
        }
        if let Some(r) = self.string_expand(tn, sn) {
            return r;
        }
        self.unit_like(tn, sn)
    }

    fn proof_irrel(&mut self, t: ExprPtr<'t>, s: ExprPtr<'t>) -> Option<bool> {
        let tt = self.infer(t, true);
        if !self.is_prop(tt) {
            return None;
        }
        let st = self.infer(s, true);
        Some(self.def_eq(tt, st))
    }

    fn is_nat_zero(&self, e: ExprPtr<'t>) -> bool {
        match *e {
            Expr::NatLit { n, .. } => n.bits() == 0,
            Expr::Const { name, .. } => Some(name) == self.names.nat_zero,
            _ => false,
        }
    }

    fn nat_pred(&mut self, e: ExprPtr<'t>) -> Option<ExprPtr<'t>> {
        match *e {
            Expr::NatLit { n, .. } if n.bits() > 0 => Some(self.ctx.nat_lit(n.as_ref() - 1u32)),
            Expr::App { fun, arg, .. }
                if fun.const_name().is_some() && fun.const_name() == self.names.nat_succ =>
            {
                Some(arg)
            }
            _ => None,
        }
    }

    fn offset(&mut self, t: ExprPtr<'t>, s: ExprPtr<'t>) -> Option<bool> {
        if self.is_nat_zero(t) && self.is_nat_zero(s) {
            return Some(true);
        }
        let a = self.nat_pred(t)?;
        let b = self.nat_pred(s)?;
        Some(self.def_eq_core(a, b))
    }

    fn lazy_delta(
        &mut self,
        mut t: ExprPtr<'t>,
        mut s: ExprPtr<'t>,
    ) -> Result<bool, (ExprPtr<'t>, ExprPtr<'t>)> {
        loop {
            if let Some(r) = self.offset(t, s) {
                return Ok(r);
            }
            if !t.has_local() && !s.has_local() {
                if let Some(tv) = self.reduce_nat(t) {
                    return Ok(self.def_eq_core(tv, s));
                }
                if let Some(sv) = self.reduce_nat(s) {
                    return Ok(self.def_eq_core(t, sv));
                }
            }
            match (self.delta_hint(t), self.delta_hint(s)) {
                (None, None) => return Err((t, s)),
                (Some(_), None) => t = self.unfold_core(t),
                (None, Some(_)) => s = self.unfold_core(s),
                (Some(ht), Some(hs)) => match unfold_order(ht, hs) {
                    Ordering::Less => t = self.unfold_core(t),
                    Ordering::Greater => s = self.unfold_core(s),
                    Ordering::Equal => {
                        if let (Expr::App { .. }, Expr::App { .. }) = (*t, *s)
                            && matches!(ht, Hint::Regular(_))
                            && let (
                                Expr::Const {
                                    name: a,
                                    levels: la,
                                    ..
                                },
                                Expr::Const {
                                    name: b,
                                    levels: lb,
                                    ..
                                },
                            ) = (*t.head(), *s.head())
                            && a == b
                            && !self.fail_cache.contains(&(t, s))
                        {
                            if self.ctx.levels_eq(la, lb) && self.args_eq(t, s) {
                                return Ok(true);
                            }
                            self.fail_cache.insert((t, s));
                        }
                        t = self.unfold_core(t);
                        s = self.unfold_core(s);
                    }
                },
            }
            if let Some(r) = self.quick(t, s) {
                return Ok(r);
            }
        }
    }

    fn unfold_core(&mut self, e: ExprPtr<'t>) -> ExprPtr<'t> {
        let u = self.unfold(e).expect("delta hint without unfolding");
        self.whnf_core(u, true)
    }

    fn args_eq(&mut self, t: ExprPtr<'t>, s: ExprPtr<'t>) -> bool {
        let (_, ta) = self.ctx.unfold_apps(t);
        let (_, sa) = self.ctx.unfold_apps(s);
        ta.len() == sa.len() && ta.iter().zip(&sa).all(|(&a, &b)| self.def_eq(a, b))
    }

    fn def_eq_app(&mut self, t: ExprPtr<'t>, s: ExprPtr<'t>) -> bool {
        if !matches!(*t, Expr::App { .. })
            || !matches!(*s, Expr::App { .. })
            || t.num_args() != s.num_args()
        {
            return false;
        }
        let (th, ta) = self.ctx.unfold_apps(t);
        let (sh, sa) = self.ctx.unfold_apps(s);
        self.def_eq(th, sh) && ta.iter().zip(&sa).all(|(&a, &b)| self.def_eq(a, b))
    }

    fn eta(&mut self, t: ExprPtr<'t>, s: ExprPtr<'t>) -> bool {
        if !t.is_lambda() || s.is_lambda() {
            return false;
        }
        let st = self.infer(s, true);
        let st = self.whnf(st);
        let Expr::Pi { ty, .. } = *st else {
            return false;
        };
        let v = self.ctx.var(0);
        let b = self.ctx.app(s, v);
        let l = self.ctx.lam(ty, b);
        self.def_eq(t, l)
    }

    fn eta_struct(&mut self, t: ExprPtr<'t>, s: ExprPtr<'t>) -> bool {
        let Expr::Const { name, .. } = *s.head() else {
            return false;
        };
        let Some(Declar::Ctor(c)) = self.declar(name) else {
            return false;
        };
        if s.num_args() != usize::from(c.num_params) + usize::from(c.num_fields)
            || self.structure_like(c.induct).is_none()
        {
            return false;
        }
        let tt = self.infer(t, true);
        let st = self.infer(s, true);
        if !self.def_eq(tt, st) {
            return false;
        }
        let (_, args) = self.ctx.unfold_apps(s);
        (0..c.num_fields).all(|i| {
            let p = self.ctx.proj(c.induct, i, t);
            self.def_eq(p, args[usize::from(c.num_params + i)])
        })
    }

    fn string_expand(&mut self, t: ExprPtr<'t>, s: ExprPtr<'t>) -> Option<bool> {
        let of_list = self.names.string_of_list?;
        if let Expr::StrLit { s: x, .. } = *t
            && s.head().const_name() == Some(of_list)
        {
            let e = self.str_to_ctor(x);
            return Some(self.def_eq_core(e, s));
        }
        if let Expr::StrLit { s: x, .. } = *s
            && t.head().const_name() == Some(of_list)
        {
            let e = self.str_to_ctor(x);
            return Some(self.def_eq_core(t, e));
        }
        None
    }

    fn unit_like(&mut self, t: ExprPtr<'t>, s: ExprPtr<'t>) -> bool {
        let tt = self.infer(t, true);
        let tt = self.whnf(tt);
        let Expr::Const { name, .. } = *tt.head() else {
            return false;
        };
        match self.structure_like(name) {
            Some((_, c)) if c.num_fields == 0 => {
                let st = self.infer(s, true);
                self.def_eq_core(tt, st)
            }
            _ => false,
        }
    }
}
