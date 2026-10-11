use super::inductive;
use super::prelude::*;

impl Checker<'_> {
    pub(super) fn whnf(&mut self, e: &Expr) -> Result<Expr> {
        self.whnf_mode(e, true)
    }
    pub(super) fn whnf_mode(&mut self, e: &Expr, unfold: bool) -> Result<Expr> {
        let id = self.cache.id(e);
        let key = (id, self.cache.scope(id, self.scope), unfold);
        if let Some(value) = self.cache.reduced.get(&key) {
            return Ok(value.clone());
        }
        let value = grow(|| self.whnf_core(e, unfold))?;
        self.cache.reduced.insert(key, value.clone());
        Ok(value)
    }
    pub(super) fn nf(&mut self, e: &Expr) -> Result<Expr> {
        let head = self.whnf(e)?;
        let is_pi = matches!(head, Expr::Pi(..));
        match head {
            Expr::Pi(ty, b) | Expr::Lam(ty, b) => {
                let ty = self.nf(&ty)?;
                let (n, body) = b.unbind();
                let body = self.local(n.clone(), ty.clone(), |tc| tc.nf(&body))?;
                Ok(if is_pi {
                    Expr::pi(n, ty, body)
                } else {
                    Expr::lam(n, ty, body)
                })
            }
            Expr::App(f, a) => Ok(self.nf(&f)?.app(self.nf(&a)?)),
            Expr::Proj(n, i, e) => Ok(Expr::Proj(n, i, Shared::new(self.nf(&e)?))),
            other => Ok(other),
        }
    }
    pub(super) fn conv(&mut self, a: &Expr, b: &Expr) -> Result<bool> {
        if self.semantic {
            return self.semantic_conv(a, b);
        }
        #[cfg(feature = "profile")]
        crate::profile::count("conversions");
        let ai = self.cache.id(a);
        let bi = self.cache.id(b);
        if ai == bi {
            return Ok(true);
        }
        let scope = self
            .cache
            .scope(ai, self.scope)
            .max(self.cache.scope(bi, self.scope));
        let key = (ai.min(bi), ai.max(bi), scope);
        if let Some(result) = self.cache.equal.get(&key) {
            return Ok(*result);
        }
        let result = grow(|| self.conv_core(a, b))?;
        self.cache.equal.insert(key, result);
        Ok(result)
    }
    fn delta(&mut self, e: &Expr) -> Result<Option<(usize, Expr)>> {
        let (head, args) = inductive::spine(e);
        let Expr::Const(n, us) = head else {
            return Ok(None);
        };
        let d = self.decl(&n)?.clone();
        let Some(value) = &d.value else {
            return Ok(None);
        };
        let subst = self.level_arguments(&d.params, &us)?;
        let value = self.substitute_levels(value, &subst)?;
        Ok(Some((d.order, args.into_iter().fold(value, Expr::app))))
    }
    fn is_prop(&mut self, ty: &Expr) -> Result<bool> {
        let tty = self.type_of(ty)?;
        self.sort_type(ty, &tty)?.equivalent(&Level::Nat(0))
    }
    fn conv_core(&mut self, a: &Expr, b: &Expr) -> Result<bool> {
        self.tick()?;
        if let (Expr::Sort(a), Expr::Sort(b)) = (a, b) {
            return a.equivalent(b);
        }
        let ta = self.type_of(a)?;
        if self.is_prop(&ta)? {
            let tb = self.type_of(b)?;
            return self.conv(&ta, &tb);
        }
        match (a, b) {
            (Expr::Pi(at, ab), Expr::Pi(bt, bb)) | (Expr::Lam(at, ab), Expr::Lam(bt, bb)) => {
                if self.conv(at, bt)? {
                    let (n, body) = ab.unbind_ref();
                    let rhs = bb.instantiate(&Expr::Var(n.clone()));
                    if self.local(n, (**at).clone(), |tc| tc.conv(&body, &rhs))? {
                        return Ok(true);
                    }
                }
            }
            (Expr::App(..), Expr::App(..)) => {
                let (ah, aa) = inductive::spine(a);
                let (bh, ba) = inductive::spine(b);
                if self.cache.id(&ah) == self.cache.id(&bh) && aa.len() == ba.len() {
                    let mut equal = true;
                    for (a, b) in aa.iter().zip(&ba) {
                        if !self.conv(a, b)? {
                            equal = false;
                            break;
                        }
                    }
                    if equal {
                        return Ok(true);
                    }
                }
            }
            _ => {}
        }
        let a = self.whnf_mode(a, false)?;
        let b = self.whnf_mode(b, false)?;
        if self.cache.id(&a) == self.cache.id(&b) {
            return Ok(true);
        }
        let da = self.delta(&a)?;
        let db = self.delta(&b)?;
        match (da, db) {
            (Some((pa, va)), Some((pb, vb))) => {
                return if pa > pb {
                    self.conv(&va, &b)
                } else if pb > pa {
                    self.conv(&a, &vb)
                } else {
                    self.conv(&va, &vb)
                };
            }
            (Some((_, va)), None) => return self.conv(&va, &b),
            (None, Some((_, vb))) => return self.conv(&a, &vb),
            _ => {}
        }
        match (&a, &b) {
            (Expr::Nat(x), Expr::Nat(y)) => return Ok(x == y),
            (Expr::Str(x), Expr::Str(y)) => return Ok(x == y),
            (Expr::Nat(n), _) => {
                return self.nat_literal_eq(&n.0, &b);
            }
            (_, Expr::Nat(n)) => {
                return self.nat_literal_eq(&n.0, &a);
            }
            (Expr::Str(s), _) => {
                let expanded = self.string_constructor(s)?;
                return self.conv(&expanded, &b);
            }
            (_, Expr::Str(s)) => {
                let expanded = self.string_constructor(s)?;
                return self.conv(&a, &expanded);
            }
            _ => {}
        }
        let ta = self.type_of(&a)?;
        if self.is_prop(&ta)? || self.unit_like(&ta)? {
            let tb = self.type_of(&b)?;
            return self.conv(&ta, &tb);
        }
        if self.structure_eta(&a, &b)? || self.structure_eta(&b, &a)? {
            return Ok(true);
        }
        match (&a, &b) {
            (Expr::Proj(an, ai, ae), Expr::Proj(bn, bi, be)) if an == bn && ai == bi => {
                self.conv(ae, be)
            }
            (Expr::Sort(a), Expr::Sort(b)) => a.equivalent(b),
            (Expr::Const(a, aus), Expr::Const(b, bus)) if a == b && aus.len() == bus.len() => {
                for (a, b) in aus.iter().zip(bus) {
                    if !a.equivalent(b)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            (Expr::Pi(at, ab), Expr::Pi(bt, bb)) | (Expr::Lam(at, ab), Expr::Lam(bt, bb)) => {
                if !self.conv(at, bt)? {
                    return Ok(false);
                }
                let (n, body) = ab.unbind_ref();
                let rhs = bb.instantiate(&Expr::Var(n.clone()));
                self.local(n, (**at).clone(), |tc| tc.conv(&body, &rhs))
            }
            (Expr::App(af, aa), Expr::App(bf, ba)) => Ok(self.conv(af, bf)? && self.conv(aa, ba)?),
            (Expr::Lam(ty, body), _) => {
                let (n, lhs) = body.unbind_ref();
                let rhs = b.clone().app(Expr::Var(n.clone()));
                let tb = self.type_of(&b)?;
                let Expr::Pi(bt, _) = self.whnf(&tb)? else {
                    return Ok(false);
                };
                if !self.conv(ty, &bt)? {
                    return Ok(false);
                }
                self.local(n, (**ty).clone(), |tc| tc.conv(&lhs, &rhs))
            }
            (_, Expr::Lam(..)) => self.conv(&b, &a),
            _ => Ok(false),
        }
    }
}
