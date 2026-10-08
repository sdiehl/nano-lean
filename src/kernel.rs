use crate::resource::Budget;
use crate::{Expr, Level};
use rustc_hash::FxHashMap as HashMap;
use std::{
    cell::{Cell, RefCell},
    collections::{BTreeMap, BTreeSet},
    fmt,
    rc::Rc,
};
use unbound::prelude::*;
mod cache;
mod conv;
mod eval;
pub mod export_validation;
mod inductive;
mod infer;
mod prelude;
mod primitive;
mod quotient;

pub use inductive::{Constructor, InductiveBlock, InductiveType, Recursor, RecursorRule};
pub use quotient::primitives as quotient_primitives;

#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum Error {
    #[error("{0}")]
    Rejected(String),
    #[error("unsupported: {0}")]
    Unsupported(String),
    #[error("{0}")]
    Exhausted(Budget),
    #[error("conversion probe exhausted")]
    ProbeExhausted,
}

impl Error {
    pub fn context(self, context: impl fmt::Display) -> Self {
        match self {
            Self::Rejected(s) => Self::Rejected(format!("{context}: {s}")),
            Self::Unsupported(s) => Self::Unsupported(format!("{context}: {s}")),
            e => Self::Unsupported(format!("{context}: {e}")),
        }
    }
}

type Result<T> = std::result::Result<T, Error>;

#[derive(Clone, Debug)]
struct Declaration {
    params: Vec<String>,
    ty: Expr,
    value: Option<Expr>,
    order: usize,
    relevance: RefCell<Vec<(Vec<Level>, eval::Summary)>>,
}

#[derive(Default, Clone, Debug)]
pub struct Environment {
    declarations: HashMap<String, Rc<Declaration>>,
    inductives: HashMap<String, Rc<InductiveType>>,
    constructors: HashMap<String, Rc<Constructor>>,
    recursors: HashMap<String, Rc<Recursor>>,
    quotients: BTreeSet<String>,
    export_work: Option<Rc<Cell<u64>>>,
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
            return Err(Error::Rejected(format!("duplicate declaration: {name}")));
        }
        let mut tc = Checker::new(self);
        tc.uparams = params.iter().cloned().collect();
        if tc.uparams.len() != params.len() {
            return Err(Error::Rejected("duplicate universe parameter".into()));
        }
        tc.sort(&ty)?;
        if let Some(v) = &value {
            tc.check(v, &ty)?;
        }
        self.insert(name, params, ty, value.filter(|_| transparent));
        Ok(())
    }
    fn insert(&mut self, name: String, params: Vec<String>, ty: Expr, value: Option<Expr>) {
        let order = self.declarations.len();
        self.declarations.insert(
            name,
            Rc::new(Declaration {
                params,
                ty,
                order,
                value,
                relevance: Default::default(),
            }),
        );
    }
    // Export workers only, since the coordinator re-verifies every declaration.
    pub(crate) fn assume_export_declaration(
        &mut self,
        name: String,
        params: Vec<String>,
        ty: Expr,
        value: Option<Expr>,
        transparent: bool,
    ) -> Result<()> {
        if self.declarations.contains_key(&name) {
            return Err(Error::Rejected(format!("duplicate declaration: {name}")));
        }
        self.insert(name, params, ty, value.filter(|_| transparent));
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
            return Err(Error::Rejected("theorem type is not a proposition".into()));
        }
        // Theorem bodies may reduce when a recursor needs a proof's constructor.
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
                    .ok_or_else(|| Error::from(Budget::Checking))?,
            );
        }
        self.fuel = self
            .fuel
            .checked_sub(1)
            .ok_or_else(|| Error::from(Budget::Checking))?;
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
            .ok_or_else(|| Error::Rejected(format!("unknown constant: {name}")))
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
            return Err(Error::Rejected(format!("undeclared universe: {n}")));
        }
        Ok(())
    }
    fn level_arguments(
        &self,
        params: &[String],
        values: &[Level],
    ) -> Result<BTreeMap<String, Level>> {
        if params.len() != values.len() {
            return Err(Error::Rejected("universe argument count mismatch".into()));
        }
        for value in values {
            self.valid_level(value)?;
        }
        Ok(params.iter().cloned().zip(values.iter().cloned()).collect())
    }
}
