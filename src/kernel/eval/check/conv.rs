use super::*;
use num_bigint::BigUint;

impl Session<'_, '_> {
    pub(super) fn conv(&mut self, a: &Type, b: &Type, types: bool) -> Result<bool> {
        if a.id() == b.id() {
            return Ok(true);
        }
        let key = (a.id().min(b.id()), a.id().max(b.id()), types);
        if let Some(result) = self.equal.get(&key) {
            return Ok(*result);
        }
        let result = grow(|| self.conv_core(a, b, types))?;
        self.equal.insert(key, result);
        Ok(result)
    }
    pub(super) fn conv_terms(&mut self, a: &Thunk, b: &Thunk, types: bool) -> Result<bool> {
        self.conv(&Type::Term(a.clone()), &Type::Term(b.clone()), types)
    }
    fn conv_core(&mut self, a: &Type, b: &Type, types: bool) -> Result<bool> {
        if let Some(fuel) = &mut self.ev.tc.probe_fuel {
            *fuel = fuel.checked_sub(1).ok_or(Error::ProbeExhausted)?;
        }
        self.ev.tc.tick()?;
        #[cfg(feature = "profile")]
        crate::profile::count("semantic_conversions");
        if !types && let (Type::Term(at), Type::Term(bt)) = (a, b) {
            let status = self.known_proof(at)?;
            if status != Some(false) {
                let ta = self.infer(at, false)?;
                let proof =
                    status == Some(true) || self.type_sort(&ta)?.equivalent(&Level::Nat(0))?;
                self.proof_status.insert(at.id, Some(proof));
                if proof {
                    let tb = self.infer(bt, false)?;
                    return self.conv(&ta, &tb, true);
                }
            }
        }
        let av = self.view(a, false)?;
        let bv = self.view(b, false)?;
        match (&av, &bv) {
            (View::Pi(ad, ab), View::Pi(bd, bb)) => {
                if !self.conv_terms(ad, bd, true)? {
                    return Ok(false);
                }
                let x = self.fresh(ad);
                let at = self.apply_body(ab, &x)?;
                let bt = self.apply_body(bb, &x)?;
                return self.conv(&at, &bt, true);
            }
            (View::Value(av), View::Value(bv)) if self.congruent(av, bv)? => return Ok(true),
            _ => {}
        }
        let da = self.delta(&av)?;
        let db = self.delta(&bv)?;
        match (da, db) {
            (Some((ao, at)), Some((bo, bt))) => {
                return if ao > bo {
                    self.conv(&at, b, types)
                } else if bo > ao {
                    self.conv(a, &bt, types)
                } else {
                    self.conv(&at, &bt, types)
                };
            }
            (Some((_, at)), None) => return self.conv(&at, b, types),
            (None, Some((_, bt))) => return self.conv(a, &bt, types),
            _ => {}
        }
        let (View::Value(av), View::Value(bv)) = (av, bv) else {
            return Ok(false);
        };
        let (Type::Term(at), Type::Term(bt)) = (a, b) else {
            return Ok(false);
        };
        if let Expr::Nat(n) = &av.head {
            return self.nat_eq(&n.0, &bv);
        }
        if let Expr::Nat(n) = &bv.head {
            return self.nat_eq(&n.0, &av);
        }
        if let Expr::Str(s) = &av.head {
            let expanded = self.ev.tc.string_constructor(s)?;
            let expanded = self.ev.term(expanded, None);
            return self.conv_terms(&expanded, bt, false);
        }
        if let Expr::Str(s) = &bv.head {
            let expanded = self.ev.tc.string_constructor(s)?;
            let expanded = self.ev.term(expanded, None);
            return self.conv_terms(at, &expanded, false);
        }
        if let Expr::Lam(d, binder) = &av.head {
            let domain = self.ev.term_at(d.clone(), av.context.clone(), 0);
            let bty = self.infer(bt, false)?;
            if let View::Pi(bdomain, _) = self.view(&bty, true)? {
                if !self.conv_terms(&domain, &bdomain, true)? {
                    return Ok(false);
                }
                let x = self.fresh(&domain);
                let body = self.body(binder, av.context.clone(), false);
                let lhs = self.apply_body(&body, &x)?;
                let rhs = Type::Term(self.app(bt, &x));
                return self.conv(&lhs, &rhs, false);
            }
        }
        if matches!(bv.head, Expr::Lam(..)) {
            return self.conv(b, a, types);
        }
        if !types {
            let ta = self.infer(at, false)?;
            if let View::Value(tv) = self.view(&ta, true)?
                && let Expr::Const(n, _) = &tv.head
                && self.ev.tc.structure(n).is_some_and(|c| c.num_fields == 0)
            {
                let tb = self.infer(bt, false)?;
                return self.conv(&ta, &tb, true);
            }
            if self.eta(at, bt, &bv)? || self.eta(bt, at, &av)? {
                return Ok(true);
            }
        }
        Ok(false)
    }
    pub(super) fn congruent(&mut self, a: &Value, b: &Value) -> Result<bool> {
        if a.id == b.id {
            return Ok(true);
        }
        if a.args.len() != b.args.len() {
            return Ok(false);
        }
        let heads = match (&a.head, &b.head) {
            (Expr::Sort(a), Expr::Sort(b)) => a.equivalent(b)?,
            (Expr::Nat(a), Expr::Nat(b)) => a == b,
            (Expr::Str(a), Expr::Str(b)) => a == b,
            (Expr::Var(a), Expr::Var(b)) => a == b,
            (Expr::Const(an, au), Expr::Const(bn, bu)) if an == bn && au.len() == bu.len() => {
                let mut equal = true;
                for (a, b) in au.iter().zip(bu) {
                    if !a.equivalent(b)? {
                        equal = false;
                        break;
                    }
                }
                equal
            }
            (Expr::Proj(an, ai, ae), Expr::Proj(bn, bi, be)) if an == bn && ai == bi => {
                let ae = self.ev.term_at(ae.clone(), a.context.clone(), 0);
                let be = self.ev.term_at(be.clone(), b.context.clone(), 0);
                self.conv_terms(&ae, &be, false)?
            }
            (Expr::Lam(ad, ab), Expr::Lam(bd, bb)) => {
                let ad = self.ev.term_at(ad.clone(), a.context.clone(), 0);
                let bd = self.ev.term_at(bd.clone(), b.context.clone(), 0);
                if !self.conv_terms(&ad, &bd, true)? {
                    return Ok(false);
                }
                let x = self.fresh(&ad);
                let ab = self.body(ab, a.context.clone(), false);
                let bb = self.body(bb, b.context.clone(), false);
                let at = self.apply_body(&ab, &x)?;
                let bt = self.apply_body(&bb, &x)?;
                self.conv(&at, &bt, false)?
            }
            _ => false,
        };
        if !heads {
            return Ok(false);
        }
        let summary = if let Expr::Const(name, levels) = &a.head {
            self.summary(name, levels)?
        } else {
            Summary::default()
        };
        let unfoldable = matches!(&a.head, Expr::Const(name, _)
            if self.ev.tc.env.declarations.get(name).is_some_and(|d| d.value.is_some()));
        for (i, (a, b)) in a.args.iter().zip(&b.args).enumerate() {
            if summary.proof_argument(i) {
                #[cfg(feature = "profile")]
                crate::profile::count("proof_arguments_skipped");
                continue;
            }
            // A per-argument bound avoids needlessly unfolding large functions.
            let probe = self.ev.tc.probe_fuel.is_none() && unfoldable;
            if probe {
                self.ev.tc.probe_fuel = Some(2048);
            }
            let result = self.conv_terms(a, b, false);
            if probe {
                self.ev.tc.probe_fuel = None;
            }
            match result {
                // An interrupted comparison is not a cached inequality.
                Err(Error::ProbeExhausted) if probe => return Ok(false),
                Err(e) => return Err(e),
                Ok(false) => return Ok(false),
                Ok(true) => {}
            }
        }
        Ok(true)
    }
    fn delta(&mut self, view: &View) -> Result<Option<(usize, Type)>> {
        let View::Value(v) = view else {
            return Ok(None);
        };
        let Expr::Const(n, us) = &v.head else {
            return Ok(None);
        };
        let d = self.ev.tc.decl(n)?;
        let Some(body) = &d.value else {
            return Ok(None);
        };
        let subst = self.ev.tc.level_arguments(&d.params, us)?;
        let body = self.ev.tc.substitute_levels(body, &subst)?;
        let mut term = self.ev.term(body, None);
        for arg in &v.args {
            term = self.app(&term, arg);
        }
        Ok(Some((d.order, Type::Term(term))))
    }
    fn nat_eq(&mut self, n: &BigUint, value: &Value) -> Result<bool> {
        use num_traits::{One, Zero};
        let mut n = n.clone();
        let mut value = value.clone();
        loop {
            match &value.head {
                Expr::Nat(m) => return Ok(value.args.is_empty() && n == m.0),
                Expr::Const(c, us) if us.is_empty() && *c == self.ev.tc.builtin_name(NAT_ZERO) => {
                    return Ok(value.args.is_empty() && n.is_zero());
                }
                Expr::Const(c, us)
                    if us.is_empty()
                        && *c == self.ev.tc.builtin_name(NAT_SUCC)
                        && value.args.len() == 1
                        && !n.is_zero() =>
                {
                    n -= BigUint::one();
                    value = self.ev.eval(&value.args[0], true)?;
                }
                _ => return Ok(false),
            }
        }
    }
    fn eta(&mut self, a: &Thunk, b: &Thunk, bv: &Value) -> Result<bool> {
        let Expr::Const(n, _) = &bv.head else {
            return Ok(false);
        };
        let Some(ctor) = self.ev.tc.env.constructors.get(n).cloned() else {
            return Ok(false);
        };
        if self.ev.tc.structure(&ctor.inductive).is_none()
            || bv.args.len() != ctor.num_params + ctor.num_fields
        {
            return Ok(false);
        }
        let at = self.infer(a, false)?;
        let bt = self.infer(b, false)?;
        if !self.conv(&at, &bt, true)? {
            return Ok(false);
        }
        for (i, field) in bv.args[ctor.num_params..].iter().enumerate() {
            let proj = self.projection(&ctor.inductive, i, a);
            if !self.conv_terms(&proj, field, false)? {
                return Ok(false);
            }
        }
        Ok(true)
    }
}
