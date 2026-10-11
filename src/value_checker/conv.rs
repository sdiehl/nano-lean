use super::value::{Clo, Env, Head, K, V, View, key};
use super::{R, Stop, Vc, stat};
use crate::checker::env::{Decls, positive, strip_pis, unfold_order};
use crate::resource::grow;
use crate::term::decl::{Declar, Hint};
use crate::term::expr::Expr;
use crate::term::level::Level;
use crate::term::ptr::{ExprPtr, LevelPtr};
use std::cmp::Ordering;
use std::ptr;
use std::rc::Rc;

/// Steps a same-head argument probe takes before both sides unfold instead.
const PROBE_BUDGET: u32 = 2048;

const SAME_FUEL: u32 = 512;

fn zero(l: LevelPtr<'_>) -> bool {
    match *l {
        Level::Zero => true,
        Level::Max(a, b, _) => zero(a) && zero(b),
        Level::IMax(_, b, _) => zero(b),
        _ => false,
    }
}

#[inline]
fn same_code(a: Clo<'_>, b: Clo<'_>) -> bool {
    a.body == b.body && a.typed == b.typed && a.sub == b.sub
}

#[inline]
fn identical_clo(a: Clo<'_>, b: Clo<'_>) -> bool {
    same_code(a, b) && a.env.key() == b.env.key()
}

impl<'t, 'a: 't> Vc<'t, 'a> {
    pub(crate) fn def_eq(&mut self, t: V<'t>, s: V<'t>) -> R<bool> {
        self.tick()?;
        if let Some(r) = &mut self.probe_remaining {
            if *r == 0 {
                return Err(Stop);
            }
            *r -= 1;
        }
        stat!(self, deq_calls);
        if ptr::eq(t, s) || self.t.eq_cache.contains(&(key(t), key(s))) {
            stat!(self, deq_ptr_eq);
            return Ok(true);
        }
        let k = if key(t) < key(s) {
            (key(t), key(s))
        } else {
            (key(s), key(t))
        };
        if self.t.neq_cache.contains(&k) {
            stat!(self, neq_hit);
            return Ok(false);
        }
        let mut fuel = SAME_FUEL;
        let same = self.same(t, s, &mut fuel);
        if same {
            stat!(self, deq_same);
        }
        let r = same || grow(|| self.def_eq_core(t, s))?;
        if r {
            self.t.eq_cache.insert_both(key(t), key(s));
        } else if !matches!(t.k, K::Lam(..)) && !matches!(s.k, K::Lam(..)) {
            self.t.neq_cache.insert(k);
        }
        Ok(r)
    }

    /// Bounded structural equality on hash-consed values. False means unknown.
    fn same(&self, a: V<'t>, b: V<'t>, fuel: &mut u32) -> bool {
        if ptr::eq(a, b) {
            return true;
        }
        if *fuel == 0 {
            return false;
        }
        *fuel -= 1;
        match (a.k, b.k) {
            (K::Sort(x), K::Sort(y)) => x == y,
            (K::Nat(x), K::Nat(y)) => x == y,
            (K::Str(x), K::Str(y)) => x == y,
            (K::Neu(h, xs), K::Neu(g, ys)) => {
                xs.len() == ys.len()
                    && match (h, g) {
                        (Head::Local(i, _), Head::Local(j, _)) => i == j,
                        (Head::Const(m, ls), Head::Const(n, ks)) => m == n && ls == ks,
                        (Head::Proj(_, i, x), Head::Proj(_, j, y)) => {
                            i == j && self.same(x, y, fuel)
                        }
                        _ => false,
                    }
                    && xs.iter().zip(ys).all(|(x, y)| self.same(x, y, fuel))
            }
            (K::Pi(d, c), K::Pi(e, k)) => self.same(d, e, fuel) && self.same_clo(c, k, fuel),
            (K::Lam(d, c), K::Lam(e, k)) => {
                (ptr::eq(d, e)
                    || (d.e == e.e && d.sub == e.sub && self.same_env(d.env, e.env, fuel)))
                    && self.same_clo(c, k, fuel)
            }
            _ => false,
        }
    }

    fn same_clo(&self, c: Clo<'t>, k: Clo<'t>, fuel: &mut u32) -> bool {
        same_code(c, k) && self.same_env(c.env, k.env, fuel)
    }

    fn same_env(&self, mut a: Env<'t>, mut b: Env<'t>, fuel: &mut u32) -> bool {
        loop {
            if a.key() == b.key() {
                return true;
            }
            match (a.view(), b.view()) {
                (View::Node(x), View::Node(y)) => {
                    if !self.same(x.head, y.head, fuel) {
                        return false;
                    }
                    a = x.tail;
                    b = y.tail;
                }
                _ => {
                    let (mut i, mut j) = (a.iter(), b.iter());
                    loop {
                        match (i.next(), j.next()) {
                            (None, None) => return true,
                            (Some(x), Some(y)) if self.same(x, y, fuel) => {}
                            _ => return false,
                        }
                    }
                }
            }
        }
    }

    fn quick(&mut self, t: V<'t>, s: V<'t>) -> R<Option<bool>> {
        if ptr::eq(t, s) || self.t.eq_cache.contains(&(key(t), key(s))) {
            return Ok(Some(true));
        }
        Ok(match (t.k, s.k) {
            (K::Lam(..), K::Lam(..)) | (K::Pi(..), K::Pi(..)) => Some(self.def_eq_binding(t, s)?),
            (K::Sort(a), K::Sort(b)) => Some(self.ctx.level_eq(a, b)),
            (K::Nat(a), K::Nat(b)) => Some(a == b),
            (K::Str(a), K::Str(b)) => Some(a == b),
            _ => None,
        })
    }

    pub(crate) fn binder_local(&mut self, d: V<'t>) -> V<'t> {
        let x = self.conv_local(d);
        self.depth += 1;
        x
    }

    #[inline(always)]
    pub(crate) fn restoring_depth<T>(&mut self, f: impl FnOnce(&mut Self) -> R<T>) -> R<T> {
        let saved = self.depth;
        let r = f(self);
        self.depth = saved;
        r
    }

    /// Sibling scopes share a local per depth and domain, nested scopes never do.
    fn conv_local(&mut self, d: V<'t>) -> V<'t> {
        let k = (self.depth, key(d));
        if let Some(&x) = self.t.conv_locals.get(&k) {
            return x;
        }
        let x = self.fresh_local(d);
        self.t.conv_locals.insert(k, x);
        x
    }

    fn def_eq_binding(&mut self, t: V<'t>, s: V<'t>) -> R<bool> {
        self.restoring_depth(|vc| vc.def_eq_binding_in(t, s))
    }

    fn def_eq_binding_in(&mut self, mut t: V<'t>, mut s: V<'t>) -> R<bool> {
        stat!(self, deq_binding);
        loop {
            let (td, tc, sd, sc) = match (t.k, s.k) {
                (K::Pi(td, tc), K::Pi(sd, sc)) => (td, tc, sd, sc),
                (K::Lam(td, tc), K::Lam(sd, sc)) => {
                    if ptr::eq(td, sd) && identical_clo(tc, sc) {
                        return Ok(true);
                    }
                    let td = self.force(td)?;
                    let sd = self.force(sd)?;
                    (td, tc, sd, sc)
                }
                _ => return self.def_eq(t, s),
            };
            if !ptr::eq(td, sd) && !self.def_eq(td, sd)? {
                return Ok(false);
            }
            if identical_clo(tc, sc) {
                return Ok(true);
            }
            let x = if self.uses_arg(tc) || self.uses_arg(sc) {
                self.conv_local(sd)
            } else {
                self.dummy
            };
            self.depth += 1;
            t = self.inst(tc, x)?;
            s = self.inst(sc, x)?;
        }
    }

    fn def_eq_core(&mut self, t: V<'t>, s: V<'t>) -> R<bool> {
        if let Some(r) = self.quick(t, s)? {
            return Ok(r);
        }
        if let Some(bt) = self.names.bool_true
            && !t.open
            && matches!(s.k, K::Neu(Head::Const(n, _), []) if n == bt)
            && matches!(self.whnf(t)?.k, K::Neu(Head::Const(n, _), []) if n == bt)
        {
            return Ok(true);
        }
        if let (K::Neu(Head::Const(a, la), ta), K::Neu(Head::Const(b, lb), sa)) = (t.k, s.k)
            && ta.len() == sa.len()
            && !ta.is_empty()
            && self.delta_hint(t).is_some()
            && a == b
            && self.ctx.levels_eq(la, lb)
            && self.probe_args(t, s)?
        {
            return Ok(true);
        }
        if !self.statically_not_proof(t)
            && let Some(r) = self.proof_irrel(t, s)?
        {
            return Ok(r);
        }
        let tn = self.whnf_core(t)?;
        let sn = self.whnf_core(s)?;
        if (!ptr::eq(tn, t) || !ptr::eq(sn, s))
            && let Some(r) = self.quick(tn, sn)?
        {
            return Ok(r);
        }
        let (tn, sn) = match self.lazy_delta(tn, sn)? {
            Ok(r) => return Ok(r),
            Err(p) => p,
        };
        match (tn.k, sn.k) {
            (K::Neu(Head::Const(a, la), []), K::Neu(Head::Const(b, lb), [])) => {
                if a == b && self.ctx.levels_eq(la, lb) {
                    return Ok(true);
                }
            }
            (K::Neu(Head::Proj(_, i, x), []), K::Neu(Head::Proj(_, j, y), []))
                if i == j && self.def_eq(x, y)? =>
            {
                return Ok(true);
            }
            _ => {}
        }
        let tnn = self.whnf_core(tn)?;
        let snn = self.whnf_core(sn)?;
        if !ptr::eq(tnn, tn) || !ptr::eq(snn, sn) {
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

    fn statically_not_proof(&self, v: V<'t>) -> bool {
        match v.k {
            K::Sort(_) | K::Pi(..) | K::Nat(_) | K::Str(_) => true,
            K::Neu(Head::Const(n, _), args) => {
                let Some(d) = self.declar(n) else {
                    return false;
                };
                let Some(ty) = strip_pis(d.ty(), args.len()) else {
                    return false;
                };
                if matches!(*ty, Expr::Sort { .. }) {
                    return true;
                }
                let h = match *ty.head() {
                    Expr::Const { name, .. } => match self.declar(name) {
                        Some(d) => d.ty(),
                        None => return false,
                    },
                    _ => return false,
                };
                strip_pis(h, ty.num_args())
                    .is_some_and(|s| matches!(*s, Expr::Sort { level, .. } if positive(level)))
            }
            K::Neu(Head::Local(_, ty), []) => match ty.k {
                K::Sort(_) => true,
                K::Neu(Head::Const(n, _), args) => self
                    .declar(n)
                    .and_then(|d| strip_pis(d.ty(), args.len()))
                    .is_some_and(|s| matches!(*s, Expr::Sort { level, .. } if positive(level))),
                _ => false,
            },
            _ => false,
        }
    }

    fn proof_irrel(&mut self, t: V<'t>, s: V<'t>) -> R<Option<bool>> {
        let tt = self.type_of(t)?;
        if !self.is_prop(tt)? {
            return Ok(None);
        }
        let st = self.type_of(s)?;
        Ok(Some(self.def_eq(tt, st)?))
    }

    fn probe_args(&mut self, t: V<'t>, s: V<'t>) -> R<bool> {
        if self.t.fail_cache.contains(&(key(t), key(s))) {
            return Ok(false);
        }
        if self.probe_remaining.is_some() {
            return self.args_eq(t, s);
        }
        stat!(self, probes);
        self.probe_remaining = Some(PROBE_BUDGET);
        let r = self.args_eq(t, s);
        #[cfg(feature = "vstats")]
        {
            self.stats.probe_ticks += u64::from(PROBE_BUDGET - self.probe_remaining.unwrap_or(0));
        }
        self.probe_remaining = None;
        if r.is_err() {
            stat!(self, exhausted);
        }
        let equal = r.unwrap_or(false);
        if !equal {
            self.t.fail_cache.insert_both(key(t), key(s));
        }
        Ok(equal)
    }

    fn relevant(&mut self, v: V<'t>, count: usize) -> Rc<[bool]> {
        let K::Neu(Head::Const(n, _), _) = v.k else {
            return vec![true; count].into();
        };
        if let Some(m) = self.t.arg_support.get(&(n, count)) {
            return m.clone();
        }
        let mut mask = vec![true; count];
        if let Some((mut body, _)) = self.declar(n).and_then(|d| d.unfoldable()) {
            let mut consumed = 0;
            while consumed < count
                && let Expr::Lam { body: next, .. } = *body
            {
                body = next;
                consumed += 1;
            }
            mask[..consumed].fill(false);
            for j in self.slots(body) {
                if let Some(i) = consumed.checked_sub(usize::from(j) + 1) {
                    mask[i] = true;
                }
            }
        }
        if let Some(d) = self.declar(n) {
            let mut ty = d.ty();
            let mut doms = Vec::new();
            for m in &mut mask {
                let Expr::Pi { ty: dom, body, .. } = *ty else {
                    break;
                };
                if *m && self.prop_type(dom, &mut doms) {
                    *m = false;
                }
                doms.push(dom);
                ty = body;
            }
        }
        let m: Rc<[bool]> = mask.into();
        self.t.arg_support.insert((n, count), m.clone());
        m
    }

    fn prop_type(&self, e: ExprPtr<'t>, doms: &mut Vec<ExprPtr<'t>>) -> bool {
        if let Expr::Pi { ty, body, .. } = *e {
            doms.push(ty);
            let r = self.prop_type(body, doms);
            doms.pop();
            return r;
        }
        let ty = match *e.head() {
            Expr::Const { name, .. } => match self.declar(name) {
                Some(d) => d.ty(),
                None => return false,
            },
            Expr::Var { idx, .. } => match doms.len().checked_sub(usize::from(idx) + 1) {
                Some(i) => doms[i],
                None => return false,
            },
            _ => return false,
        };
        strip_pis(ty, e.num_args())
            .is_some_and(|s| matches!(*s, Expr::Sort { level, .. } if zero(level)))
    }

    fn args_eq(&mut self, t: V<'t>, s: V<'t>) -> R<bool> {
        stat!(self, deq_args);
        let (K::Neu(_, ta), K::Neu(_, sa)) = (t.k, s.k) else {
            return Ok(false);
        };
        if ta.len() != sa.len() {
            return Ok(false);
        }
        let rel = self.relevant(t, ta.len());
        for ((&a, &b), &r) in ta.iter().zip(sa).zip(rel.iter()) {
            if r && !self.def_eq(a, b)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn is_nat_zero(&self, v: V<'t>) -> bool {
        match v.k {
            K::Nat(n) => n.bits() == 0,
            K::Neu(Head::Const(n, _), []) => Some(n) == self.names.nat_zero,
            _ => false,
        }
    }

    fn nat_pred(&mut self, v: V<'t>) -> Option<V<'t>> {
        match v.k {
            K::Nat(n) if n.bits() > 0 => Some(self.nat(n - 1u32)),
            K::Neu(Head::Const(n, _), [a]) if Some(n) == self.names.nat_succ => Some(a),
            _ => None,
        }
    }

    fn offset(&mut self, t: V<'t>, s: V<'t>) -> R<Option<bool>> {
        if self.is_nat_zero(t) && self.is_nat_zero(s) {
            return Ok(Some(true));
        }
        let (Some(a), Some(b)) = (self.nat_pred(t), self.nat_pred(s)) else {
            return Ok(None);
        };
        Ok(Some(self.def_eq(a, b)?))
    }

    fn unfold_core(&mut self, v: V<'t>) -> R<V<'t>> {
        let u = self.unfold(v)?.expect("delta hint without unfolding");
        self.whnf_core(u)
    }

    #[allow(clippy::type_complexity)]
    fn lazy_delta(&mut self, mut t: V<'t>, mut s: V<'t>) -> R<Result<bool, (V<'t>, V<'t>)>> {
        loop {
            if let Some(r) = self.offset(t, s)? {
                return Ok(Ok(r));
            }
            if !t.open && !s.open {
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
                        if let (K::Neu(Head::Const(a, la), ta), K::Neu(Head::Const(b, lb), sa)) =
                            (t.k, s.k)
                            && !ta.is_empty()
                            && !sa.is_empty()
                            && matches!(ht, Hint::Regular(_))
                            && a == b
                            && self.ctx.levels_eq(la, lb)
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

    fn heads_eq(&mut self, a: Head<'t>, b: Head<'t>) -> R<bool> {
        Ok(match (a, b) {
            (Head::Local(x, _), Head::Local(y, _)) => x == y,
            (Head::Const(x, lx), Head::Const(y, ly)) => x == y && self.ctx.levels_eq(lx, ly),
            (Head::Proj(_, i, x), Head::Proj(_, j, y)) => i == j && self.def_eq(x, y)?,
            _ => false,
        })
    }

    fn def_eq_app(&mut self, t: V<'t>, s: V<'t>) -> R<bool> {
        let (K::Neu(th, ta), K::Neu(sh, sa)) = (t.k, s.k) else {
            return Ok(false);
        };
        if ta.is_empty() || ta.len() != sa.len() || !self.heads_eq(th, sh)? {
            return Ok(false);
        }
        if matches!(th, Head::Const(..)) {
            return self.args_eq(t, s);
        }
        for (&a, &b) in ta.iter().zip(sa) {
            if !self.def_eq(a, b)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn eta(&mut self, t: V<'t>, s: V<'t>) -> R<bool> {
        let K::Lam(td, tc) = t.k else {
            return Ok(false);
        };
        if matches!(s.k, K::Lam(..)) {
            return Ok(false);
        }
        let st = self.type_of(s)?;
        let K::Pi(d, _) = self.whnf(st)?.k else {
            return Ok(false);
        };
        let td = self.force(td)?;
        if !ptr::eq(td, d) && !self.def_eq(td, d)? {
            return Ok(false);
        }
        self.restoring_depth(|vc| {
            let x = vc.binder_local(d);
            let a = vc.inst(tc, x)?;
            let b = vc.apply(s, &[x])?;
            vc.def_eq(a, b)
        })
    }

    fn eta_struct(&mut self, t: V<'t>, s: V<'t>) -> R<bool> {
        let K::Neu(Head::Const(n, _), args) = s.k else {
            return Ok(false);
        };
        let Some(Declar::Ctor(c)) = self.declar(n) else {
            return Ok(false);
        };
        if args.len() != usize::from(c.num_params) + usize::from(c.num_fields)
            || self.structure_like(c.induct).is_none()
        {
            return Ok(false);
        }
        let tt = self.type_of(t)?;
        let st = self.type_of(s)?;
        if !self.def_eq(tt, st)? {
            return Ok(false);
        }
        for i in 0..c.num_fields {
            let p = self.proj(c.induct, i, t);
            if !self.def_eq(p, args[usize::from(c.num_params + i)])? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn string_expand(&mut self, t: V<'t>, s: V<'t>) -> R<Option<bool>> {
        let Some(of_list) = self.names.string_of_list else {
            return Ok(None);
        };
        let is_of_list = |v: V<'t>| matches!(v.k, K::Neu(Head::Const(n, _), _) if n == of_list);
        if let K::Str(x) = t.k
            && is_of_list(s)
        {
            let e = self.str_to_ctor(x)?;
            return Ok(Some(self.def_eq_core(e, s)?));
        }
        if let K::Str(x) = s.k
            && is_of_list(t)
        {
            let e = self.str_to_ctor(x)?;
            return Ok(Some(self.def_eq_core(t, e)?));
        }
        Ok(None)
    }

    fn unit_like(&mut self, t: V<'t>, s: V<'t>) -> R<bool> {
        let tt = self.type_of(t)?;
        let tt = self.whnf(tt)?;
        let K::Neu(Head::Const(n, _), _) = tt.k else {
            return Ok(false);
        };
        match self.structure_like(n) {
            Some((_, c)) if c.num_fields == 0 => {
                let st = self.type_of(s)?;
                self.def_eq_core(tt, st)
            }
            _ => Ok(false),
        }
    }
}
