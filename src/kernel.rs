use crate::{Expr, Level};
use std::{
    collections::{BTreeMap, BTreeSet, HashMap},
    fmt,
};
use unbound::prelude::*;
mod inductive;
pub use inductive::{Constructor, InductiveBlock, InductiveType, Recursor, RecursorRule};

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
    params: Vec<String>,
    ty: Expr,
    value: Option<Expr>,
}

#[derive(Default, Clone, Debug)]
pub struct Environment {
    declarations: BTreeMap<String, Declaration>,
    inductives: BTreeMap<String, InductiveType>,
    constructors: BTreeMap<String, Constructor>,
    recursors: BTreeMap<String, Recursor>,
}

impl Environment {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn axiom(&mut self, name: impl Into<String>, ty: Expr) -> Result<()> {
        self.declare(name.into(), Vec::new(), ty, None, true)
    }
    pub fn define(&mut self, name: impl Into<String>, ty: Expr, value: Expr) -> Result<()> {
        self.declare(name.into(), Vec::new(), ty, Some(value), true)
    }
    pub fn declare(
        &mut self,
        name: String,
        params: Vec<String>,
        ty: Expr,
        value: Option<Expr>,
        transparent: bool,
    ) -> Result<()> {
        if self.declarations.contains_key(&name) {
            return Err(Error(format!("duplicate declaration: {name}")));
        }
        let mut tc = Checker::new(self);
        tc.uparams = params.iter().cloned().collect();
        if tc.uparams.len() != params.len() {
            return Err(Error("duplicate universe parameter".into()));
        }
        tc.sort(&ty)?;
        if let Some(v) = &value {
            tc.check(v, &ty)?;
        }
        self.declarations.insert(
            name,
            Declaration {
                params,
                ty,
                value: if transparent { value } else { None },
            },
        );
        Ok(())
    }
    pub fn infer(&self, expr: &Expr) -> Result<Expr> {
        Checker::new(self).infer(expr)
    }
    pub fn declare_theorem(
        &mut self,
        name: String,
        params: Vec<String>,
        ty: Expr,
        value: Expr,
    ) -> Result<()> {
        let mut tc = Checker::new(self);
        tc.uparams = params.iter().cloned().collect();
        if !tc.sort(&ty)?.equivalent(&Level::Nat(0))? {
            return Err(Error("theorem type is not a proposition".into()));
        }
        self.declare(name, params, ty, Some(value), false)
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
    uparams: BTreeSet<String>,
    locals: Vec<(Name<Expr>, Expr)>,
    fuel: usize,
    scope: usize,
    next_scope: usize,
    inferred: HashMap<(usize, usize), (Shared<Expr>, Expr)>,
}

impl<'a> Checker<'a> {
    fn new(env: &'a Environment) -> Self {
        Self {
            env,
            uparams: BTreeSet::new(),
            locals: Vec::new(),
            fuel: 100_000,
            scope: 0,
            next_scope: 1,
            inferred: HashMap::new(),
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
        let previous = self.scope;
        self.scope = self.next_scope;
        self.next_scope += 1;
        let result = f(self);
        self.scope = previous;
        self.locals.pop();
        result
    }
    fn decl(&self, name: &str) -> Result<&Declaration> {
        self.env
            .declarations
            .get(name)
            .ok_or_else(|| Error(format!("unknown constant: {name}")))
    }
    fn valid_level(&self, level: &Level) -> Result<()> {
        let mut params = BTreeSet::new();
        level.params(&mut params);
        if let Some(n) = params.difference(&self.uparams).next() {
            return Err(Error(format!("undeclared universe: {n}")));
        }
        Ok(())
    }
    fn level_arguments(
        &self,
        params: &[String],
        values: &[Level],
    ) -> Result<BTreeMap<String, Level>> {
        if params.len() != values.len() {
            return Err(Error("universe argument count mismatch".into()));
        }
        for value in values {
            self.valid_level(value)?;
        }
        Ok(params.iter().cloned().zip(values.iter().cloned()).collect())
    }
    fn sort(&mut self, e: &Expr) -> Result<Level> {
        let ty = self.infer(e)?;
        self.sort_type(e, ty)
    }
    fn sort_shared(&mut self, e: &Shared<Expr>) -> Result<Level> {
        let ty = self.infer_shared(e)?;
        self.sort_type(e, ty)
    }
    fn sort_type(&mut self, e: &Expr, ty: Expr) -> Result<Level> {
        match self.whnf(&ty)? {
            Expr::Sort(u) => Ok(u),
            other => Err(Error(format!("expected a type, but {e} has type {other}"))),
        }
    }
    fn check(&mut self, e: &Expr, expected: &Expr) -> Result<()> {
        let actual = self.infer(e)?;
        self.check_type(e, actual, expected)
    }
    fn check_shared(&mut self, e: &Shared<Expr>, expected: &Expr) -> Result<()> {
        let actual = self.infer_shared(e)?;
        self.check_type(e, actual, expected)
    }
    fn check_type(&mut self, e: &Expr, actual: Expr, expected: &Expr) -> Result<()> {
        if self.conv(&actual, expected)? {
            Ok(())
        } else {
            Err(Error(format!(
                "type mismatch: {e}\n  expected: {expected}\n  inferred: {actual}"
            )))
        }
    }
    fn infer_shared(&mut self, e: &Shared<Expr>) -> Result<Expr> {
        let key = (e.as_ptr() as usize, self.scope);
        if let Some((_, ty)) = self.inferred.get(&key) {
            return Ok(ty.clone());
        }
        let ty = self.infer(e)?;
        // Keep the input alive so allocator address reuse cannot alias cache keys.
        self.inferred.insert(key, (e.clone(), ty.clone()));
        Ok(ty)
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
            Expr::Sort(u) => {
                self.valid_level(u)?;
                Ok(Expr::Sort(u.clone().succ()?))
            }
            Expr::Const(n, us) => {
                let d = self.decl(n)?;
                let subst = self.level_arguments(&d.params, us)?;
                d.ty.substitute_levels(&subst)
            }
            Expr::Proj(n, i, e) => self.infer_projection(n, *i, e),
            Expr::Pi(domain, binder) => {
                let u = self.sort_shared(domain)?;
                let (n, body) = binder.unbind_ref();
                let v = self.local(n, (**domain).clone(), |tc| tc.sort_shared(&body))?;
                Ok(Expr::Sort(Level::imax(u, v)))
            }
            Expr::Lam(domain, binder) => {
                self.sort_shared(domain)?;
                let (n, body) = binder.unbind_ref();
                let ty = self.local(n.clone(), (**domain).clone(), |tc| tc.infer_shared(&body))?;
                Ok(Expr::pi(n, (**domain).clone(), ty))
            }
            Expr::App(fun, arg) => {
                let ty = self.infer_shared(fun)?;
                match self.whnf(&ty)? {
                    Expr::Pi(domain, body) => {
                        self.check_shared(arg, &domain)?;
                        Ok((*body.instantiate(&**arg)).clone())
                    }
                    other => Err(Error(format!(
                        "expected a function, but {fun} has type {other}"
                    ))),
                }
            }
            Expr::Let(ty, value, body) => {
                self.sort_shared(ty)?;
                self.check_shared(value, ty)?;
                self.infer_shared(&body.instantiate(&**value))
            }
        }
    }
    fn whnf(&mut self, e: &Expr) -> Result<Expr> {
        let mut e = e.clone();
        loop {
            self.tick()?;
            match e {
                Expr::Const(ref name, ref levels) => {
                    let d = self.decl(name)?;
                    let args = self.level_arguments(&d.params, levels)?;
                    match &d.value {
                        Some(value) => e = value.substitute_levels(&args)?,
                        None => return Ok(e),
                    }
                }
                Expr::Let(_, value, body) => e = (*body.instantiate(&*value)).clone(),
                Expr::Proj(ref name, index, ref value) => {
                    let value = self.whnf(value)?;
                    let (head, args) = inductive::spine(&value);
                    if let Expr::Const(c, _) = head
                        && let Some(info) = self.env.constructors.get(&c)
                        && info.inductive == *name
                        && index < info.num_fields
                        && args.len() == info.num_params + info.num_fields
                    {
                        e = args[info.num_params + index].clone();
                    } else {
                        return Ok(Expr::Proj(name.clone(), index, Shared::new(value)));
                    }
                }
                Expr::App(..) => {
                    let (head, args) = inductive::spine(&e);
                    let head = self.whnf(&head)?;
                    if let Expr::Lam(_, body) = &head {
                        e = (*body.instantiate(&args[0])).clone();
                        for arg in args.into_iter().skip(1) {
                            e = e.app(arg);
                        }
                    } else if let Some(reduced) = self.reduce_recursor(&head, &args)? {
                        e = reduced;
                    } else {
                        return Ok(args.into_iter().fold(head, Expr::app));
                    }
                }
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
            Expr::Proj(n, i, e) => Ok(Expr::Proj(n, i, Shared::new(self.nf(&e)?))),
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
        if self.sort(&ta)?.equivalent(&Level::Nat(0))? {
            let tb = self.infer(&b)?;
            return self.conv(&ta, &tb);
        }
        if self.unit_like(&ta)? {
            let tb = self.infer(&b)?;
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
                let tb = self.infer(&b)?;
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
