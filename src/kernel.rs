use crate::Expr;
use std::{collections::BTreeMap, fmt};
use unbound::prelude::*;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Error(pub String);
impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}
impl std::error::Error for Error {}
type Result<T> = std::result::Result<T, Error>;

#[derive(Clone, Debug)]
struct Declaration {
    ty: Expr,
    value: Option<Expr>,
}

#[derive(Default, Clone, Debug)]
pub struct Environment {
    declarations: BTreeMap<String, Declaration>,
}

impl Environment {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn axiom(&mut self, name: impl Into<String>, ty: Expr) -> Result<()> {
        self.insert(name.into(), ty, None)
    }
    pub fn define(&mut self, name: impl Into<String>, ty: Expr, value: Expr) -> Result<()> {
        self.insert(name.into(), ty, Some(value))
    }
    fn insert(&mut self, name: String, ty: Expr, value: Option<Expr>) -> Result<()> {
        if self.declarations.contains_key(&name) {
            return Err(Error(format!("duplicate declaration: {name}")));
        }
        let mut tc = Checker::new(self);
        tc.sort(&ty)?;
        if let Some(v) = &value {
            tc.check(v, &ty)?;
        }
        self.declarations.insert(name, Declaration { ty, value });
        Ok(())
    }
    pub fn infer(&self, expr: &Expr) -> Result<Expr> {
        Checker::new(self).infer(expr)
    }
    pub fn check(&self, expr: &Expr, ty: &Expr) -> Result<()> {
        let mut tc = Checker::new(self);
        tc.sort(ty)?;
        tc.check(expr, ty)
    }
    pub fn normalize(&self, expr: &Expr) -> Result<Expr> {
        let mut tc = Checker::new(self);
        tc.infer(expr)?;
        tc.nf(expr)
    }
    pub fn def_eq(&self, a: &Expr, b: &Expr) -> Result<bool> {
        let mut tc = Checker::new(self);
        let ta = tc.infer(a)?;
        let tb = tc.infer(b)?;
        Ok(tc.conv(&ta, &tb)? && tc.conv(a, b)?)
    }
}

struct Checker<'a> {
    env: &'a Environment,
    locals: Vec<(Name<Expr>, Expr)>,
    fuel: usize,
}

impl<'a> Checker<'a> {
    fn new(env: &'a Environment) -> Self {
        Self {
            env,
            locals: Vec::new(),
            fuel: 100_000,
        }
    }
    fn tick(&mut self) -> Result<()> {
        self.fuel = self
            .fuel
            .checked_sub(1)
            .ok_or_else(|| Error("checking budget exhausted".into()))?;
        Ok(())
    }
    fn local<T>(
        &mut self,
        name: Name<Expr>,
        ty: Expr,
        f: impl FnOnce(&mut Self) -> Result<T>,
    ) -> Result<T> {
        self.locals.push((name, ty));
        let result = f(self);
        self.locals.pop();
        result
    }
    fn decl(&self, name: &str) -> Result<&Declaration> {
        self.env
            .declarations
            .get(name)
            .ok_or_else(|| Error(format!("unknown constant: {name}")))
    }
    fn sort(&mut self, e: &Expr) -> Result<u32> {
        let ty = self.infer(e)?;
        match self.whnf(&ty)? {
            Expr::Sort(u) => Ok(u),
            other => Err(Error(format!("expected a type, but {e} has type {other}"))),
        }
    }
    fn check(&mut self, e: &Expr, expected: &Expr) -> Result<()> {
        let actual = self.infer(e)?;
        if self.conv(&actual, expected)? {
            Ok(())
        } else {
            Err(Error(format!(
                "type mismatch: {e}\n  expected: {expected}\n  inferred: {actual}"
            )))
        }
    }
    fn infer(&mut self, e: &Expr) -> Result<Expr> {
        self.tick()?;
        match e {
            Expr::Var(n) => self
                .locals
                .iter()
                .rev()
                .find(|(m, _)| n == m)
                .map(|(_, ty)| ty.clone())
                .ok_or_else(|| Error(format!("unbound variable: {n}"))),
            Expr::Sort(u) => Ok(Expr::Sort(
                u.checked_add(1)
                    .ok_or_else(|| Error("universe overflow".into()))?,
            )),
            Expr::Const(n) => Ok(self.decl(n)?.ty.clone()),
            Expr::Pi(domain, binder) => {
                let u = self.sort(domain)?;
                let (n, body) = binder.unbind_ref();
                let v = self.local(n, *domain.clone(), |tc| tc.sort(&body))?;
                Ok(Expr::Sort(if v == 0 { 0 } else { u.max(v) }))
            }
            Expr::Lam(domain, binder) => {
                self.sort(domain)?;
                let (n, body) = binder.unbind_ref();
                let ty = self.local(n.clone(), *domain.clone(), |tc| tc.infer(&body))?;
                Ok(Expr::pi(n, *domain.clone(), ty))
            }
            Expr::App(fun, arg) => {
                let ty = self.infer(fun)?;
                match self.whnf(&ty)? {
                    Expr::Pi(domain, body) => {
                        self.check(arg, &domain)?;
                        Ok(*body.instantiate(arg.as_ref()))
                    }
                    other => Err(Error(format!(
                        "expected a function, but {fun} has type {other}"
                    ))),
                }
            }
            Expr::Let(ty, value, body) => {
                self.sort(ty)?;
                self.check(value, ty)?;
                self.infer(&body.instantiate(value.as_ref()))
            }
        }
    }
    fn whnf(&mut self, e: &Expr) -> Result<Expr> {
        let mut e = e.clone();
        loop {
            self.tick()?;
            match e {
                Expr::Const(ref name) => match self.decl(name)?.value.clone() {
                    Some(value) => e = value,
                    None => return Ok(e),
                },
                Expr::Let(_, value, body) => e = *body.instantiate(value.as_ref()),
                Expr::App(fun, arg) => match self.whnf(&fun)? {
                    Expr::Lam(_, body) => e = *body.instantiate(arg.as_ref()),
                    fun => return Ok(fun.app(*arg)),
                },
                _ => return Ok(e),
            }
        }
    }
    fn nf(&mut self, e: &Expr) -> Result<Expr> {
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
            other => Ok(other),
        }
    }
    fn conv(&mut self, a: &Expr, b: &Expr) -> Result<bool> {
        self.tick()?;
        if a.aeq(b) {
            return Ok(true);
        }
        let a = self.whnf(a)?;
        let b = self.whnf(b)?;
        if a.aeq(&b) {
            return Ok(true);
        }
        let ta = self.infer(&a)?;
        if self.sort(&ta)? == 0 {
            let tb = self.infer(&b)?;
            return self.conv(&ta, &tb);
        }
        match (&a, &b) {
            (Expr::Pi(at, ab), Expr::Pi(bt, bb)) | (Expr::Lam(at, ab), Expr::Lam(bt, bb)) => {
                if !self.conv(at, bt)? {
                    return Ok(false);
                }
                let (n, body) = ab.unbind_ref();
                let rhs = bb.instantiate(&Expr::Var(n.clone()));
                self.local(n, *at.clone(), |tc| tc.conv(&body, &rhs))
            }
            (Expr::App(af, aa), Expr::App(bf, ba)) => Ok(self.conv(af, bf)? && self.conv(aa, ba)?),
            (Expr::Lam(ty, body), _) => {
                let (n, lhs) = body.unbind_ref();
                let rhs = b.clone().app(Expr::Var(n.clone()));
                let tb = self.infer(&b)?;
                let Expr::Pi(bt, _) = self.whnf(&tb)? else {
                    return Ok(false);
                };
                if !self.conv(ty, &bt)? {
                    return Ok(false);
                }
                self.local(n, *ty.clone(), |tc| tc.conv(&lhs, &rhs))
            }
            (_, Expr::Lam(..)) => self.conv(&b, &a),
            _ => Ok(false),
        }
    }
}
