use super::*;
use crate::term::names::{NAT, STRING};

impl Checker<'_> {
    pub(super) fn sort(&mut self, e: &Expr) -> Result<Level> {
        if self.semantic {
            return self.semantic_sort(e);
        }
        let ty = self.infer(e)?;
        self.sort_type(e, ty)
    }
    pub(super) fn sort_type(&mut self, e: &Expr, ty: Expr) -> Result<Level> {
        match self.whnf(&ty)? {
            Expr::Sort(u) => Ok(u),
            other => Err(Error(format!("expected a type, but {e} has type {other}"))),
        }
    }
    pub(super) fn check(&mut self, e: &Expr, expected: &Expr) -> Result<()> {
        if self.semantic {
            return self.semantic_check(e, expected);
        }
        let actual = self.infer(e)?;
        self.check_type(e, actual, expected)
    }
    pub(super) fn check_type(&mut self, e: &Expr, actual: Expr, expected: &Expr) -> Result<()> {
        if self.conv(&actual, expected)? {
            Ok(())
        } else {
            Err(Error(format!(
                "type mismatch: {e}\n  expected: {expected}\n  inferred: {actual}"
            )))
        }
    }
    pub(super) fn type_of(&mut self, e: &Expr) -> Result<Expr> {
        let previous = self.checking;
        self.checking = false;
        let result = self.infer(e);
        self.checking = previous;
        result
    }
    pub(super) fn infer(&mut self, e: &Expr) -> Result<Expr> {
        if self.semantic {
            return self.semantic_infer(e);
        }
        self.infer_at(e, &mut Vec::new())
    }
    fn infer_at(&mut self, e: &Expr, context: &mut Vec<Name<Expr>>) -> Result<Expr> {
        let id = self.cache.id(e);
        let key = (
            id,
            self.cache.context_key(id, context, self.scope),
            self.checking,
        );
        if let Some(ty) = self.cache.inferred.get(&key) {
            return Ok(ty.clone());
        }
        let ty = grow(|| self.infer_core(e, context))?;
        self.cache.inferred.insert(key, ty.clone());
        Ok(ty)
    }
    fn sort_at(&mut self, e: &Expr, context: &mut Vec<Name<Expr>>) -> Result<Level> {
        let ty = self.infer_at(e, context)?;
        self.sort_type(e, ty)
    }
    fn infer_core(&mut self, e: &Expr, context: &mut Vec<Name<Expr>>) -> Result<Expr> {
        self.tick()?;
        match e {
            Expr::Nat(_) => self.literal_type(NAT),
            Expr::Str(_) => self.literal_type(STRING),
            Expr::Var(n) => {
                let n = if let Some((depth, 0)) = n.coordinates() {
                    depth
                        .checked_add(1)
                        .and_then(|d| context.len().checked_sub(d))
                        .and_then(|i| context.get(i))
                        .unwrap_or(n)
                } else {
                    n
                };
                self.locals
                    .iter()
                    .rev()
                    .find(|(m, _)| n == m)
                    .map(|(_, ty)| ty.clone())
                    .ok_or_else(|| Error(format!("unbound variable: {n}")))
            }
            Expr::Sort(u) => {
                self.valid_level(u)?;
                Ok(Expr::Sort(u.clone().succ()?))
            }
            Expr::Const(n, us) => {
                let d = self.decl(n)?.clone();
                let subst = self.level_arguments(&d.params, us)?;
                self.substitute_levels(&d.ty, &subst)
            }
            Expr::Proj(n, i, e) => {
                if self.checking {
                    self.infer_at(e, context)?;
                }
                let e = Shared::new(self.cache.open_at(e, context, 0, self.scope));
                self.infer_projection(n, *i, &e)
            }
            Expr::Pi(domain, binder) | Expr::Lam(domain, binder) => {
                let is_pi = matches!(e, Expr::Pi(..));
                let u = if is_pi || self.checking {
                    self.sort_at(domain, context)?
                } else {
                    Level::Nat(0)
                };
                let domain = self.cache.open_at(domain, context, 0, self.scope);
                let n = Name::new(binder.pattern().string().unwrap_or("_"));
                context.push(n.clone());
                let result = self.local(n.clone(), domain.clone(), |tc| {
                    if is_pi {
                        tc.sort_at(binder.body(), context)
                            .map(|v| Expr::Sort(Level::imax(u, v)))
                    } else {
                        tc.infer_at(binder.body(), context)
                            .map(|ty| Expr::pi(n, domain, ty))
                    }
                });
                context.pop();
                result
            }
            Expr::App(fun, arg) => {
                let ty = self.infer_at(fun, context)?;
                match self.whnf(&ty)? {
                    Expr::Pi(domain, body) => {
                        if self.checking {
                            let actual = self.infer_at(arg, context)?;
                            self.check_type(arg, actual, &domain)?;
                        }
                        if self.cache.has_loose(body.body()) {
                            let arg = self.cache.open_at(arg, context, 0, self.scope);
                            Ok((*body.instantiate(&arg)).clone())
                        } else {
                            Ok((**body.body()).clone())
                        }
                    }
                    other => Err(Error(format!(
                        "expected a function, but {fun} has type {other}"
                    ))),
                }
            }
            Expr::Let(ty, value, body) => {
                if self.checking {
                    self.sort_at(ty, context)?;
                    let actual = self.infer_at(value, context)?;
                    let expected = self.cache.open_at(ty, context, 0, self.scope);
                    self.check_type(value, actual, &expected)?;
                }
                let ty = self.cache.open_at(ty, context, 0, self.scope);
                let value = self.cache.open_at(value, context, 0, self.scope);
                let n = Name::new(body.pattern().string().unwrap_or("_"));
                self.definitions.insert(n.clone(), value.clone());
                context.push(n.clone());
                let result = self.local(n.clone(), ty, |tc| tc.infer_at(body.body(), context));
                context.pop();
                self.definitions.remove(&n);
                Ok(result?.subst(&n, &value))
            }
        }
    }
}
