use super::Tc;
use super::env::{Decls, positive, strip_pis, unfold_order};
use crate::resource::Budget;
use crate::term::decl::Hint;
use crate::term::expr::Expr;
use crate::term::outcome::{R, Stop};
use crate::term::ptr::ExprPtr;
use std::cell::Cell;
use std::cmp::Ordering;
use std::rc::Rc;

const ARENA_CHECK_MASK: u64 = 1023;
const SMALL_PROBE_STEPS: u32 = 32;
const PROBE_STEPS: u32 = 2048;
const SMALL_BODY_NODES: usize = 8;

struct ConversionScope(Rc<Cell<usize>>, usize);

impl Drop for ConversionScope {
    fn drop(&mut self) {
        self.0.set(self.1);
    }
}

impl<'t, 'a: 't> Tc<'t, 'a> {
    pub fn def_eq(&mut self, t: ExprPtr<'t>, s: ExprPtr<'t>) -> R<bool> {
        self.tick()?;
        if t == s || self.eq_cache.contains(&(t, s)) {
            return Ok(true);
        }
        let r = self.def_eq_core(t, s)?;
        if r {
            self.eq_cache.insert((t, s));
            self.eq_cache.insert((s, t));
        }
        Ok(r)
    }

    pub(crate) fn tick(&mut self) -> R<()> {
        if self.steps_left == 0 {
            return Err(self.decline(Budget::Work));
        }
        self.steps_left -= 1;
        if self.steps_left & ARENA_CHECK_MASK == 0
            && self.ctx.arena.used_bytes() > self.limits.arena_bytes
        {
            return Err(self.decline(Budget::Arena));
        }
        if let Some(remaining) = &mut self.probe_remaining {
            if *remaining == 0 {
                return Err(Stop);
            }
            *remaining -= 1;
        }
        Ok(())
    }

    /// Failure or exhaustion is inconclusive since delta may still prove equality.
    pub(super) fn probe_args(&mut self, t: ExprPtr<'t>, s: ExprPtr<'t>) -> R<bool> {
        if self.fail_cache.contains(&(t, s)) {
            return Ok(false);
        }
        if self.probe_remaining.is_some() {
            return self.args_eq(t, s);
        }
        self.probe_remaining = Some(if self.small_delta_body(t) {
            SMALL_PROBE_STEPS
        } else {
            PROBE_STEPS
        });
        let result = self.args_eq(t, s);
        self.probe_remaining = None;
        let equal = match result {
            Ok(equal) => equal,
            Err(Stop) if self.fail.is_none() => {
                #[cfg(test)]
                {
                    self.probe_exhaustions += 1;
                }
                false
            }
            Err(Stop) => return Err(Stop),
        };
        if !equal {
            // Caching an inconclusive probe only skips speculation, not reduction or eta.
            self.fail_cache.insert((t, s));
            self.fail_cache.insert((s, t));
        }
        Ok(equal)
    }

    fn small_delta_body(&self, e: ExprPtr<'t>) -> bool {
        let Some(name) = e.head().const_name() else {
            return false;
        };
        let Some((mut body, _)) = self.declar(name).and_then(|d| d.unfoldable()) else {
            return false;
        };
        for _ in 0..e.num_args() {
            let Expr::Lam { body: next, .. } = *body else {
                break;
            };
            body = next;
        }
        let mut head = body.head();
        while let Expr::Proj { e, .. } = *head {
            head = e.head();
        }
        if !matches!(*head, Expr::Var { .. }) {
            return false;
        }
        fn small(e: ExprPtr<'_>, remaining: &mut usize) -> bool {
            if *remaining == 0 {
                return false;
            }
            *remaining -= 1;
            match *e {
                Expr::App { fun, arg, .. } => small(fun, remaining) && small(arg, remaining),
                Expr::Proj { e, .. } => small(e, remaining),
                Expr::Lam { .. } | Expr::Pi { .. } | Expr::Let { .. } => false,
                _ => true,
            }
        }
        let mut budget = SMALL_BODY_NODES;
        small(body, &mut budget)
    }

    fn quick(&mut self, t: ExprPtr<'t>, s: ExprPtr<'t>) -> R<Option<bool>> {
        if t == s || self.eq_cache.contains(&(t, s)) {
            return Ok(Some(true));
        }
        Ok(match (*t, *s) {
            (Expr::Lam { .. }, Expr::Lam { .. }) | (Expr::Pi { .. }, Expr::Pi { .. }) => {
                Some(self.def_eq_binding(t, s)?)
            }
            (Expr::Sort { level: a, .. }, Expr::Sort { level: b, .. }) => {
                Some(self.level_eq(a, b)?)
            }
            (Expr::NatLit { .. }, Expr::NatLit { .. })
            | (Expr::StrLit { .. }, Expr::StrLit { .. }) => Some(false),
            _ => None,
        })
    }

    fn def_eq_binding(&mut self, mut t: ExprPtr<'t>, mut s: ExprPtr<'t>) -> R<bool> {
        let _scope = ConversionScope(self.conversion_depth.clone(), self.conversion_depth.get());
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
            let sd = self.inst(st, &locals)?;
            if tt != st {
                let td = self.inst(tt, &locals)?;
                if !self.def_eq(td, sd)? {
                    return Ok(false);
                }
            }
            if tb == sb {
                return Ok(true);
            }
            let l = if tb.nlb() > 0 || sb.nlb() > 0 {
                let key = (self.conversion_depth.get(), sd);
                if let Some(&local) = self.conversion_locals.get(&key) {
                    local
                } else {
                    let local = self.fresh_local(sd);
                    self.conversion_locals.insert(key, local);
                    local
                }
            } else {
                self.ctx.prop()
            };
            self.conversion_depth.set(self.conversion_depth.get() + 1);
            locals.push(l);
            t = tb;
            s = sb;
        }
        let t = self.inst(t, &locals)?;
        let s = self.inst(s, &locals)?;
        self.def_eq(t, s)
    }

    fn def_eq_core(&mut self, t: ExprPtr<'t>, s: ExprPtr<'t>) -> R<bool> {
        if let Some(r) = self.quick(t, s)? {
            return Ok(r);
        }
        if let Some(bt) = self.names.bool_true
            && !t.has_local()
            && s.const_name() == Some(bt)
            && self.whnf(t)?.const_name() == Some(bt)
        {
            return Ok(true);
        }
        if !self.statically_not_proof(t)
            && let Some(r) = self.proof_irrel(t, s)?
        {
            return Ok(r);
        }
        if t.num_args() == s.num_args()
            && t.num_args() > 0
            && self.delta_hint(t).is_some()
            && self.same_const_head(t, s)?
            && self.probe_args(t, s)?
        {
            return Ok(true);
        }
        let tn = self.whnf_core(t)?;
        let sn = self.whnf_core(s)?;
        if (tn != t || sn != s)
            && let Some(r) = self.quick(tn, sn)?
        {
            return Ok(r);
        }
        let (tn, sn) = match self.lazy_delta(tn, sn)? {
            Ok(r) => return Ok(r),
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
                if a == b && self.levels_eq(la, lb)? {
                    return Ok(true);
                }
            }
            (
                Expr::Proj {
                    name: m,
                    idx: i,
                    e: x,
                    ..
                },
                Expr::Proj {
                    name: n,
                    idx: j,
                    e: y,
                    ..
                },
            ) if m == n && i == j && self.def_eq(x, y)? => {
                return Ok(true);
            }
            _ => {}
        }
        let tnn = self.whnf_core(tn)?;
        let snn = self.whnf_core(sn)?;
        if tnn != tn || snn != sn {
            return self.def_eq_core(tnn, snn);
        }
        if self.def_eq_app(tn, sn)?
            || self.eta(tn, sn)?
            || self.eta(sn, tn)?
            || self.eta_struct(tn, sn)?
            || self.eta_struct(sn, tn)?
        {
            return Ok(true);
        }
        if let Some(r) = self.string_expand(tn, sn)? {
            return Ok(r);
        }
        self.unit_like(tn, sn)
    }

    fn statically_not_proof(&self, e: ExprPtr<'t>) -> bool {
        if matches!(
            *e,
            Expr::Sort { .. } | Expr::Pi { .. } | Expr::NatLit { .. } | Expr::StrLit { .. }
        ) {
            return true;
        }
        let Some(ty) = self.uninstantiated_type(e) else {
            return false;
        };
        if matches!(*ty, Expr::Sort { .. }) {
            return true;
        }
        self.uninstantiated_type(ty)
            .is_some_and(|sort| matches!(*sort, Expr::Sort { level, .. } if positive(level)))
    }

    fn uninstantiated_type(&self, e: ExprPtr<'t>) -> Option<ExprPtr<'t>> {
        let ty = match *e.head() {
            Expr::Const { name, .. } => self.declar(name)?.ty(),
            Expr::Local { ty, .. } => ty,
            _ => return None,
        };
        strip_pis(ty, e.num_args())
    }

    fn proof_irrel(&mut self, t: ExprPtr<'t>, s: ExprPtr<'t>) -> R<Option<bool>> {
        let tt = self.infer(t, true)?;
        if !self.is_prop(tt)? {
            return Ok(None);
        }
        let st = self.infer(s, true)?;
        Ok(Some(self.def_eq(tt, st)?))
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

    fn offset(&mut self, t: ExprPtr<'t>, s: ExprPtr<'t>) -> R<Option<bool>> {
        if self.is_nat_zero(t) && self.is_nat_zero(s) {
            return Ok(Some(true));
        }
        let (Some(a), Some(b)) = (self.nat_pred(t), self.nat_pred(s)) else {
            return Ok(None);
        };
        Ok(Some(self.def_eq_core(a, b)?))
    }

    #[allow(clippy::type_complexity)]
    fn lazy_delta(
        &mut self,
        mut t: ExprPtr<'t>,
        mut s: ExprPtr<'t>,
    ) -> R<Result<bool, (ExprPtr<'t>, ExprPtr<'t>)>> {
        loop {
            if let Some(r) = self.offset(t, s)? {
                return Ok(Ok(r));
            }
            if !t.has_local() && !s.has_local() {
                if let Some(tv) = self.reduce_nat(t)? {
                    return Ok(Ok(self.def_eq_core(tv, s)?));
                }
                if let Some(sv) = self.reduce_nat(s)? {
                    return Ok(Ok(self.def_eq_core(t, sv)?));
                }
            }
            match (self.delta_hint(t), self.delta_hint(s)) {
                (None, None) => return Ok(Err((t, s))),
                (Some(_), None) => t = self.unfold_core(t)?,
                (None, Some(_)) => s = self.unfold_core(s)?,
                (Some(ht), Some(hs)) => match unfold_order(ht, hs) {
                    Ordering::Less => t = self.unfold_core(t)?,
                    Ordering::Greater => s = self.unfold_core(s)?,
                    Ordering::Equal => {
                        if let (Expr::App { .. }, Expr::App { .. }) = (*t, *s)
                            && matches!(ht, Hint::Regular(_))
                            && self.same_const_head(t, s)?
                            && self.probe_args(t, s)?
                        {
                            return Ok(Ok(true));
                        }
                        t = self.unfold_core(t)?;
                        s = self.unfold_core(s)?;
                    }
                },
            }
            if let Some(r) = self.quick(t, s)? {
                return Ok(Ok(r));
            }
        }
    }

    #[inline]
    fn same_const_head(&mut self, t: ExprPtr<'t>, s: ExprPtr<'t>) -> R<bool> {
        let (
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
        else {
            return Ok(false);
        };
        Ok(a == b && self.levels_eq(la, lb)?)
    }

    fn unfold_core(&mut self, e: ExprPtr<'t>) -> R<ExprPtr<'t>> {
        let u = self.unfold(e).expect("delta hint without unfolding");
        self.whnf_core(u)
    }

    fn relevant_arguments(&mut self, head: ExprPtr<'t>, count: usize) -> Rc<[bool]> {
        let Some(name) = head.const_name() else {
            return vec![true; count].into();
        };
        if let Some(mask) = self.argument_support.get(&(name, count)) {
            return mask.clone();
        }
        let mut mask = vec![true; count];
        if let Some((mut body, _)) = self.declar(name).and_then(|d| d.unfoldable()) {
            let mut consumed = 0;
            while consumed < count
                && let Expr::Lam { body: next, .. } = *body
            {
                body = next;
                consumed += 1;
            }
            let support = self.support(body);
            for (i, used) in mask[..consumed].iter_mut().enumerate() {
                *used = support.binary_search(&((consumed - 1 - i) as u16)).is_ok();
            }
        }
        let mask: Rc<[bool]> = mask.into();
        self.argument_support.insert((name, count), mask.clone());
        mask
    }

    fn args_eq(&mut self, t: ExprPtr<'t>, s: ExprPtr<'t>) -> R<bool> {
        let (head, ta) = self.ctx.unfold_apps(t);
        let (_, sa) = self.ctx.unfold_apps(s);
        if ta.len() != sa.len() {
            return Ok(false);
        }
        let relevant = self.relevant_arguments(head, ta.len());
        for (i, (&a, &b)) in ta.iter().zip(&sa).enumerate() {
            if relevant[i] && !self.def_eq(a, b)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn def_eq_app(&mut self, t: ExprPtr<'t>, s: ExprPtr<'t>) -> R<bool> {
        if !matches!(*t, Expr::App { .. })
            || !matches!(*s, Expr::App { .. })
            || t.num_args() != s.num_args()
        {
            return Ok(false);
        }
        let (th, ta) = self.ctx.unfold_apps(t);
        let (sh, sa) = self.ctx.unfold_apps(s);
        if !self.def_eq(th, sh)? {
            return Ok(false);
        }
        for (&a, &b) in ta.iter().zip(&sa) {
            if !self.def_eq(a, b)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn eta(&mut self, t: ExprPtr<'t>, s: ExprPtr<'t>) -> R<bool> {
        if !t.is_lambda() || s.is_lambda() {
            return Ok(false);
        }
        let st = self.infer(s, true)?;
        let st = self.whnf(st)?;
        let Expr::Pi { ty, .. } = *st else {
            return Ok(false);
        };
        let v = self.ctx.var(0);
        let b = self.ctx.app(s, v);
        let l = self.ctx.lam(ty, b);
        self.def_eq(t, l)
    }

    fn eta_struct(&mut self, t: ExprPtr<'t>, s: ExprPtr<'t>) -> R<bool> {
        let Expr::Const { name, .. } = *s.head() else {
            return Ok(false);
        };
        let Some(c) = self.struct_ctor(name, s.num_args()) else {
            return Ok(false);
        };
        let tt = self.infer(t, true)?;
        let st = self.infer(s, true)?;
        if !self.def_eq(tt, st)? {
            return Ok(false);
        }
        let (_, args) = self.ctx.unfold_apps(s);
        for i in 0..c.num_fields {
            let p = self.ctx.proj(c.induct, i, t);
            if !self.def_eq(p, args[usize::from(c.num_params + i)])? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn string_expand(&mut self, t: ExprPtr<'t>, s: ExprPtr<'t>) -> R<Option<bool>> {
        let Some(of_list) = self.names.string_of_list else {
            return Ok(None);
        };
        if let Expr::StrLit { s: x, .. } = *t
            && s.head().const_name() == Some(of_list)
        {
            let e = self.str_to_ctor(x)?;
            return Ok(Some(self.def_eq_core(e, s)?));
        }
        if let Expr::StrLit { s: x, .. } = *s
            && t.head().const_name() == Some(of_list)
        {
            let e = self.str_to_ctor(x)?;
            return Ok(Some(self.def_eq_core(t, e)?));
        }
        Ok(None)
    }

    fn unit_like(&mut self, t: ExprPtr<'t>, s: ExprPtr<'t>) -> R<bool> {
        let tt = self.infer(t, true)?;
        let tt = self.whnf(tt)?;
        let Expr::Const { name, .. } = *tt.head() else {
            return Ok(false);
        };
        if !self.unit_struct(name) {
            return Ok(false);
        }
        let st = self.infer(s, true)?;
        self.def_eq_core(tt, st)
    }
}
