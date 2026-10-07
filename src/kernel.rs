use crate::{Expr, Level};
use rustc_hash::FxHashMap as HashMap;
use std::{
    collections::{BTreeMap, BTreeSet},
    fmt,
    rc::Rc,
};
use unbound::prelude::*;
mod cache;
mod eval;
pub mod export_validation;
mod inductive;
mod primitive;
mod quotient;
pub use inductive::{Constructor, InductiveBlock, InductiveType, Recursor, RecursorRule};
pub use quotient::primitives as quotient_primitives;

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
    order: usize,
    relevance: std::cell::RefCell<Vec<(Vec<Level>, eval::Summary)>>,
}

#[derive(Default, Clone, Debug)]
pub struct Environment {
    declarations: HashMap<String, Rc<Declaration>>,
    inductives: HashMap<String, Rc<InductiveType>>,
    constructors: HashMap<String, Rc<Constructor>>,
    recursors: HashMap<String, Rc<Recursor>>,
    quotients: BTreeSet<String>,
    export_work: Option<Rc<std::cell::Cell<u64>>>,
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
            Rc::new(Declaration {
                params,
                ty,
                order: self.declarations.len(),
                value: if transparent { value } else { None },
                relevance: Default::default(),
            }),
        );
        Ok(())
    }
    // Conditional environment used only by export workers. The coordinator must
    // verify every declaration in another worker before accepting the export.
    pub(crate) fn assume_export_declaration(
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
        self.declarations.insert(
            name,
            Rc::new(Declaration {
                params,
                ty,
                order: self.declarations.len(),
                value: if transparent { value } else { None },
                relevance: Default::default(),
            }),
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
        // Unlike opaque declarations, theorem bodies may reduce in the kernel
        // when a recursor needs to expose a proof's constructor.
        self.declare(name, params, ty, Some(value), true)
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
        Checker::new(self).semantic_def_eq(a, b)
    }
}

struct Checker<'a> {
    env: &'a Environment,
    uparams: BTreeSet<String>,
    locals: Vec<(Name<Expr>, Expr)>,
    fuel: usize,
    probe_fuel: Option<usize>,
    scope: usize,
    next_scope: usize,
    cache: cache::Cache,
    evaluation: eval::State,
    checking: bool,
    // Disabled inside value sessions when bridging to syntax reduction rules.
    semantic: bool,
    definitions: HashMap<Name<Expr>, Expr>,
}

impl<'a> Checker<'a> {
    fn new(env: &'a Environment) -> Self {
        Self {
            env,
            uparams: BTreeSet::new(),
            locals: Vec::new(),
            fuel: 100_000_000,
            probe_fuel: None,
            scope: 0,
            next_scope: 1,
            cache: cache::Cache::default(),
            evaluation: eval::State::default(),
            checking: true,
            semantic: true,
            definitions: HashMap::default(),
        }
    }
    fn tick(&mut self) -> Result<()> {
        if let Some(work) = &self.env.export_work {
            work.set(
                work.get()
                    .checked_sub(1)
                    .ok_or_else(|| Error("checking budget exhausted".into()))?,
            );
        }
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
    fn decl(&self, name: &str) -> Result<Rc<Declaration>> {
        self.env
            .declarations
            .get(name)
            .cloned()
            .ok_or_else(|| Error(format!("unknown constant: {name}")))
    }
    fn substitute_levels(&mut self, e: &Expr, subst: &BTreeMap<String, Level>) -> Result<Expr> {
        if subst.is_empty() {
            return Ok(e.clone());
        }
        let key = (
            self.cache.id(e),
            subst.iter().map(|(n, u)| (n.clone(), u.clone())).collect(),
        );
        if let Some(value) = self.cache.universes.get(&key) {
            return Ok(value.clone());
        }
        let value = e.substitute_levels(subst)?;
        self.cache.universes.insert(key, value.clone());
        Ok(value)
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
        if self.semantic {
            return self.semantic_sort(e);
        }
        let ty = self.infer(e)?;
        self.sort_type(e, ty)
    }
    fn sort_type(&mut self, e: &Expr, ty: Expr) -> Result<Level> {
        match self.whnf(&ty)? {
            Expr::Sort(u) => Ok(u),
            other => Err(Error(format!("expected a type, but {e} has type {other}"))),
        }
    }
    fn check(&mut self, e: &Expr, expected: &Expr) -> Result<()> {
        if self.semantic {
            return self.semantic_check(e, expected);
        }
        let actual = self.infer(e)?;
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
    fn type_of(&mut self, e: &Expr) -> Result<Expr> {
        let previous = self.checking;
        self.checking = false;
        let result = self.infer(e);
        self.checking = previous;
        result
    }
    fn infer(&mut self, e: &Expr) -> Result<Expr> {
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
        let ty = stacker::maybe_grow(256 * 1024, 16 * 1024 * 1024, || self.infer_core(e, context))?;
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
            Expr::Nat(_) => self.literal_type("Nat"),
            Expr::Str(_) => self.literal_type("String"),
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
                // Checking the source before inference prevents a projection from hiding bad arguments.
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
    fn whnf(&mut self, e: &Expr) -> Result<Expr> {
        self.whnf_mode(e, true)
    }
    fn whnf_mode(&mut self, e: &Expr, unfold: bool) -> Result<Expr> {
        let id = self.cache.id(e);
        let key = (id, self.cache.scope(id, self.scope), unfold);
        if let Some(value) = self.cache.reduced.get(&key) {
            return Ok(value.clone());
        }
        let value =
            stacker::maybe_grow(256 * 1024, 16 * 1024 * 1024, || self.whnf_core(e, unfold))?;
        self.cache.reduced.insert(key, value.clone());
        Ok(value)
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
        let result = stacker::maybe_grow(256 * 1024, 16 * 1024 * 1024, || self.conv_core(a, b))?;
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
    fn conv_core(&mut self, a: &Expr, b: &Expr) -> Result<bool> {
        self.tick()?;
        if let (Expr::Sort(a), Expr::Sort(b)) = (a, b) {
            return a.equivalent(b);
        }
        // Proofs must be identified before evaluating their potentially costly bodies.
        let ta = self.type_of(a)?;
        if {
            let tty = self.type_of(&ta)?;
            self.sort_type(&ta, tty)?
        }
        .equivalent(&Level::Nat(0))?
        {
            let tb = self.type_of(b)?;
            return self.conv(&ta, &tb);
        }
        // Congruence can establish equality without exposing a definition's body.
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
        if {
            let tty = self.type_of(&ta)?;
            self.sort_type(&ta, tty)?
        }
        .equivalent(&Level::Nat(0))?
        {
            let tb = self.type_of(&b)?;
            return self.conv(&ta, &tb);
        }
        if self.unit_like(&ta)? {
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
