use super::prelude::*;
mod elim;
mod generate;
mod nested;
mod reduce;
mod validate;
use crate::syntax::Binder;
use nested::NestedExpansion;
use serde_json::Value;

#[derive(Clone, Debug)]
pub struct InductiveType {
    pub name: String,
    pub params: Vec<String>,
    pub ty: Expr,
    pub all: Vec<String>,
    pub constructors: Vec<String>,
    pub num_params: usize,
    pub num_indices: usize,
    pub num_nested: usize,
    pub recursive: bool,
    pub reflexive: bool,
}

#[derive(Clone, Debug)]
pub struct Constructor {
    pub name: String,
    pub params: Vec<String>,
    pub ty: Expr,
    pub inductive: String,
    pub index: usize,
    pub num_params: usize,
    pub num_fields: usize,
}

#[derive(Clone, Debug)]
pub struct RecursorRule {
    pub constructor: String,
    pub num_fields: usize,
    pub rhs: Expr,
}

#[derive(Clone, Debug)]
pub struct Recursor {
    pub name: String,
    pub params: Vec<String>,
    pub ty: Expr,
    pub all: Vec<String>,
    pub num_params: usize,
    pub num_indices: usize,
    pub num_motives: usize,
    pub num_minors: usize,
    pub k: bool,
    pub rules: Vec<RecursorRule>,
}

#[derive(Clone, Debug)]
pub struct InductiveBlock {
    pub types: Vec<InductiveType>,
    pub constructors: Vec<Constructor>,
    pub recursors: Vec<Recursor>,
}

type Local = (Name<Expr>, Expr);
type RecursiveField = (Vec<Local>, usize, Vec<Expr>);

const LOCAL_NAME: &str = "x";
const DUPLICATE_NAME: &str = "duplicate inductive declaration name";

trait Signature {
    fn signature(&self) -> (&str, &[String], &Expr);
}

impl Signature for InductiveType {
    fn signature(&self) -> (&str, &[String], &Expr) {
        (&self.name, &self.params, &self.ty)
    }
}

impl Signature for Constructor {
    fn signature(&self) -> (&str, &[String], &Expr) {
        (&self.name, &self.params, &self.ty)
    }
}

impl Signature for Recursor {
    fn signature(&self) -> (&str, &[String], &Expr) {
        (&self.name, &self.params, &self.ty)
    }
}

impl InductiveBlock {
    fn type_names(&self) -> Vec<String> {
        self.types.iter().map(|t| t.name.clone()).collect()
    }
}

fn demand(ok: bool, message: &str) -> Result<()> {
    if ok {
        Ok(())
    } else {
        Err(Error::Rejected(message.into()))
    }
}

fn is_zero(level: &Level) -> Result<bool> {
    level.equivalent(&Level::Nat(0))
}

fn variable(local: &Local) -> Expr {
    Expr::Var(local.0.clone())
}

fn apply(f: Expr, args: impl IntoIterator<Item = Expr>) -> Expr {
    args.into_iter().fold(f, Expr::app)
}

fn pis(locals: &[Local], body: Expr) -> Expr {
    locals
        .iter()
        .rev()
        .fold(body, |body, (n, ty)| Expr::pi(n.clone(), ty.clone(), body))
}

fn lambdas(locals: &[Local], body: Expr) -> Expr {
    locals
        .iter()
        .rev()
        .fold(body, |body, (n, ty)| Expr::lam(n.clone(), ty.clone(), body))
}

type Closed = (Shared<Expr>, Shared<Expr>);

/// Closes every local of a telescope in one memoized pass, so the domains are shared by every term bound over it.
pub(super) struct Telescope<'a> {
    locals: &'a [Local],
    position: HashMap<usize, usize>,
    memo: HashMap<(usize, usize, usize), Closed>,
    domains: Vec<Shared<Expr>>,
}

impl<'a> Telescope<'a> {
    pub(super) fn new(locals: &'a [Local]) -> Self {
        let position = locals
            .iter()
            .enumerate()
            .filter_map(|(i, (n, _))| Some((n.index()?, i)))
            .collect();
        let mut t = Self {
            locals,
            position,
            memo: HashMap::default(),
            domains: Vec::with_capacity(locals.len()),
        };
        for (j, (_, ty)) in locals.iter().enumerate() {
            let domain = t.close(&Shared::new(ty.clone()), j, 0);
            t.domains.push(domain);
        }
        t
    }

    pub(super) fn lambdas(&mut self, body: Expr) -> Expr {
        self.wrap(body, Expr::Lam)
    }

    pub(super) fn pis(&mut self, body: Expr) -> Expr {
        self.wrap(body, Expr::Pi)
    }

    fn wrap(&mut self, body: Expr, binder: fn(Shared<Expr>, Binder) -> Expr) -> Expr {
        let mut out = self.close(&Shared::new(body), self.locals.len(), 0);
        for (j, (n, _)) in self.locals.iter().enumerate().rev() {
            out = Shared::new(binder(self.domains[j].clone(), bind(n.clone(), out)));
        }
        (*out).clone()
    }

    fn close(&mut self, e: &Shared<Expr>, k: usize, d: usize) -> Shared<Expr> {
        let key = (e.as_ptr() as usize, k, d);
        if let Some((_, out)) = self.memo.get(&key) {
            return out.clone();
        }
        let binder = |b: &Binder, t: &mut Self| {
            let body = t.close(b.body(), k, d + 1);
            (!body.ptr_eq(b.body())).then(|| bind(b.pattern().clone(), body))
        };
        let out = match &**e {
            Expr::Var(n) => match n.index().and_then(|i| self.position.get(&i)) {
                Some(&i) if i < k => Some(Expr::Var(Name::bound(d + k - 1 - i, 0))),
                _ => None,
            },
            Expr::Nat(_) | Expr::Str(_) | Expr::Sort(_) | Expr::Const(..) => None,
            Expr::App(f, a) => {
                let (f2, a2) = (self.close(f, k, d), self.close(a, k, d));
                (!f2.ptr_eq(f) || !a2.ptr_eq(a)).then_some(Expr::App(f2, a2))
            }
            Expr::Proj(n, i, x) => {
                let x2 = self.close(x, k, d);
                (!x2.ptr_eq(x)).then(|| Expr::Proj(n.clone(), *i, x2))
            }
            Expr::Pi(a, b) | Expr::Lam(a, b) => {
                let a2 = self.close(a, k, d);
                let b2 = binder(b, self);
                (!a2.ptr_eq(a) || b2.is_some()).then(|| {
                    let b2 = b2.unwrap_or_else(|| b.clone());
                    match &**e {
                        Expr::Pi(..) => Expr::Pi(a2, b2),
                        _ => Expr::Lam(a2, b2),
                    }
                })
            }
            Expr::Let(a, v, b) => {
                let (a2, v2) = (self.close(a, k, d), self.close(v, k, d));
                let b2 = binder(b, self);
                (!a2.ptr_eq(a) || !v2.ptr_eq(v) || b2.is_some())
                    .then(|| Expr::Let(a2, v2, b2.unwrap_or_else(|| b.clone())))
            }
        };
        let out = out.map_or_else(|| e.clone(), Shared::new);
        self.memo.insert(key, (e.clone(), out.clone()));
        out
    }
}

fn level_substitution(params: &[String], levels: &[Level]) -> BTreeMap<String, Level> {
    params.iter().cloned().zip(levels.iter().cloned()).collect()
}

pub(super) fn spine(e: &Expr) -> (Expr, Vec<Expr>) {
    let mut args = Vec::new();
    let mut head = e;
    while let Expr::App(f, a) = head {
        args.push((**a).clone());
        head = f;
    }
    args.reverse();
    (head.clone(), args)
}

fn append_name(name: &str, suffix: &str) -> String {
    if let Ok(mut parts) = serde_json::from_str::<Vec<Value>>(name) {
        parts.push(Value::String(suffix.into()));
        serde_json::to_string(&parts).expect("serializing strings cannot fail")
    } else {
        format!("{name}.{suffix}")
    }
}

fn rec_name(name: &str) -> String {
    append_name(name, Recursor::SUFFIX)
}

fn occurs(e: &Expr, names: &BTreeSet<String>) -> bool {
    fn go(e: &Expr, names: &BTreeSet<String>, seen: &mut BTreeSet<usize>) -> bool {
        let mut shared = |e: &Shared<Expr>| seen.insert(e.as_ptr() as usize) && go(e, names, seen);
        match e {
            Expr::Const(n, _) => names.contains(n),
            Expr::App(f, a) => shared(f) || shared(a),
            Expr::Proj(_, _, e) => shared(e),
            Expr::Pi(t, b) | Expr::Lam(t, b) => shared(t) || shared(b.body()),
            Expr::Let(t, v, b) => shared(t) || shared(v) || shared(b.body()),
            _ => false,
        }
    }
    go(e, names, &mut BTreeSet::new())
}

impl Checker<'_> {
    fn fresh_local(&mut self, ty: Expr) -> Local {
        let n = Name::new(LOCAL_NAME);
        self.locals.push((n.clone(), ty.clone()));
        self.scope = self.next_scope;
        self.next_scope += 1;
        (n, ty)
    }

    fn telescope(&mut self, e: &Expr) -> Result<(Vec<Local>, Expr)> {
        let mut e = self.whnf(e)?;
        let mut locals = Vec::new();
        while let Expr::Pi(ty, body) = e {
            let local = self.fresh_local((*ty).clone());
            e = self.whnf(&body.instantiate(&variable(&local)))?;
            locals.push(local);
        }
        Ok((locals, e))
    }

    fn open_params(&mut self, ty: &Expr, count: usize) -> Result<(Vec<Local>, Expr)> {
        let mut ty = ty.clone();
        let mut params = Vec::with_capacity(count);
        for _ in 0..count {
            let Expr::Pi(domain, body) = self.whnf(&ty)? else {
                return Err(Error::Rejected("missing inductive parameter".into()));
            };
            let local = self.fresh_local((*domain).clone());
            ty = (*body.instantiate(&variable(&local))).clone();
            params.push(local);
        }
        Ok((params, ty))
    }

    fn consume_params(&mut self, ty: &Expr, params: &[Local]) -> Result<Expr> {
        let mut ty = ty.clone();
        for local in params {
            let Expr::Pi(domain, body) = self.whnf(&ty)? else {
                return Err(Error::Rejected("missing inductive parameter".into()));
            };
            demand(
                self.conv(&domain, &local.1)?,
                "inductive parameter type mismatch",
            )?;
            ty = (*body.instantiate(&variable(local))).clone();
        }
        Ok(ty)
    }
}

impl Environment {
    pub fn declare_inductive(&mut self, block: &InductiveBlock) -> Result<()> {
        let mut added = Vec::new();
        let result = self.build_inductive(block, &mut added);
        if result.is_err() {
            for name in added {
                self.declarations.remove(&name);
                self.inductives.remove(&name);
                self.constructors.remove(&name);
                self.recursors.remove(&name);
            }
        }
        result
    }

    fn checker(&self, params: &[String]) -> Checker<'_> {
        let mut tc = Checker::new(self);
        tc.uparams = params.iter().cloned().collect();
        tc
    }

    fn reserve_names<'a>(&self, names: impl IntoIterator<Item = &'a String>) -> Result<()> {
        let mut reserved = BTreeSet::new();
        for name in names {
            demand(
                reserved.insert(name.clone()) && !self.declarations.contains_key(name),
                DUPLICATE_NAME,
            )?;
        }
        Ok(())
    }

    fn insert_generated(&mut self, decl: &impl Signature, added: &mut Vec<String>) -> Result<()> {
        let (name, params, ty) = decl.signature();
        demand(!self.declarations.contains_key(name), DUPLICATE_NAME)?;
        demand(!super::quotient::reserved(name), "reserved quotient name")?;
        self.declarations.insert(
            name.into(),
            Rc::new(Declaration {
                order: self.declarations.len(),
                params: params.to_vec(),
                ty: ty.clone(),
                value: None,
                relevance: Default::default(),
            }),
        );
        added.push(name.into());
        Ok(())
    }

    fn insert_all(&mut self, decls: &[impl Signature], added: &mut Vec<String>) -> Result<()> {
        decls
            .iter()
            .try_for_each(|decl| self.insert_generated(decl, added))
    }

    fn remove_added(&mut self, added: &mut Vec<String>) {
        for name in added.drain(..) {
            self.declarations.remove(&name);
        }
    }

    pub fn complete_inductive(&self, block: &InductiveBlock) -> Result<InductiveBlock> {
        self.clone().expected_inductive(block, &mut Vec::new())
    }

    fn build_inductive(&mut self, actual: &InductiveBlock, added: &mut Vec<String>) -> Result<()> {
        let expected = self.expected_inductive(actual, added)?;
        self.validate_inductive_export(actual, &expected)?;
        for t in expected.types {
            self.inductives.insert(t.name.clone(), Rc::new(t));
        }
        for c in expected.constructors {
            self.constructors.insert(c.name.clone(), Rc::new(c));
        }
        for r in expected.recursors {
            self.recursors.insert(r.name.clone(), Rc::new(r));
        }
        Ok(())
    }

    fn expected_inductive(
        &mut self,
        actual: &InductiveBlock,
        added: &mut Vec<String>,
    ) -> Result<InductiveBlock> {
        demand(!actual.types.is_empty(), "empty inductive block")?;
        self.reserve_names(
            actual
                .types
                .iter()
                .map(|t| &t.name)
                .chain(actual.constructors.iter().map(|c| &c.name))
                .chain(actual.recursors.iter().map(|r| &r.name)),
        )?;
        for (name, params, ty) in actual
            .types
            .iter()
            .map(|t| (&t.name, &t.params, &t.ty))
            .chain(
                actual
                    .constructors
                    .iter()
                    .map(|c| (&c.name, &c.params, &c.ty)),
            )
        {
            super::primitive::validate(name, params, ty)?;
        }
        let expansion = NestedExpansion::new(self, actual)?;
        if expansion.is_nested() {
            // Check before specialization: an unused container parameter must not erase an ill-typed argument.
            for t in &actual.types {
                self.checker(&t.params).sort(&t.ty)?;
                self.insert_generated(t, added)?;
            }
            for c in &actual.constructors {
                self.checker(&c.params).sort(&c.ty)?;
            }
            self.remove_added(added);
        }
        let generated = self.generate_inductive(&expansion.block, added)?;
        let expected = expansion.restore(generated)?;
        if expansion.is_nested() {
            self.remove_added(added);
            self.insert_all(&expected.types, added)?;
            self.insert_all(&expected.constructors, added)?;
            self.insert_all(&expected.recursors, added)?;
        }
        Ok(expected)
    }
}
