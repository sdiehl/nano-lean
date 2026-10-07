use crate::kernel::{Constructor, InductiveBlock, InductiveType};
use crate::{Environment, Error, Expr, Level, lexer::lex};
use unbound::{Name, Shared};

lalrpop_util::lalrpop_mod!(
    #[allow(clippy::all)]
    grammar
);

#[derive(Clone, Debug)]
pub(crate) enum Term {
    Name(String),
    Const(String, Vec<Level>),
    Sort(Level),
    App(Box<Term>, Box<Term>),
    Pi(String, Box<Term>, Box<Term>),
    Lam(String, Box<Term>, Box<Term>),
    Let(String, Box<Term>, Box<Term>, Box<Term>),
    Nat(String),
    Str(String),
    Proj(String, usize, Box<Term>),
}

pub(crate) type Binding = (String, Term);
pub(crate) type LocalDef = (String, Term, Term);
pub(crate) type Signature = (String, Vec<String>);

pub(crate) fn offset(u: Level, n: u32) -> Level {
    (0..n).fold(u, |u, _| match u {
        Level::Nat(k) => Level::Nat(k.saturating_add(1)),
        u => Level::Succ(Box::new(u)),
    })
}

/// Names in scope while resolving a term. Inside an inductive block, a bare
/// reference to the type being defined is applied to its universe parameters.
#[derive(Default)]
struct Scope {
    locals: Vec<(String, Name<Expr>)>,
    implicit: Option<(String, Vec<Level>)>,
}

impl Term {
    pub(crate) fn binders(params: Vec<Binding>, body: Term, pi: bool) -> Term {
        params.into_iter().rev().fold(body, |body, (n, ty)| {
            if pi {
                Term::Pi(n, Box::new(ty), Box::new(body))
            } else {
                Term::Lam(n, Box::new(ty), Box::new(body))
            }
        })
    }
    pub(crate) fn lets(defs: Vec<LocalDef>, body: Term) -> Term {
        defs.into_iter().rev().fold(body, |body, (n, ty, value)| {
            Term::Let(n, Box::new(ty), Box::new(value), Box::new(body))
        })
    }
    fn resolve(self, scope: &mut Scope) -> Expr {
        let is_pi = matches!(self, Self::Pi(..));
        match self {
            Self::Name(n) => {
                if let Some((_, v)) = scope.locals.iter().rev().find(|(s, _)| s == &n) {
                    Expr::Var(v.clone())
                } else if let Some((_, us)) = scope.implicit.as_ref().filter(|(s, _)| s == &n) {
                    Expr::Const(n, us.clone())
                } else {
                    Expr::constant(n)
                }
            }
            Self::Const(n, us) => Expr::Const(n, us),
            Self::Sort(u) => Expr::Sort(u),
            Self::Nat(n) => Expr::nat(n.parse::<num_bigint::BigUint>().unwrap()),
            Self::Str(s) => Expr::Str(s),
            Self::Proj(n, i, e) => Expr::Proj(n, i, Shared::new(e.resolve(scope))),
            Self::App(f, a) => f.resolve(scope).app(a.resolve(scope)),
            Self::Pi(n, ty, body) | Self::Lam(n, ty, body) => {
                let ty = ty.resolve(scope);
                let name = Name::new(if n.is_empty() { "_" } else { &n });
                scope.locals.push((n, name.clone()));
                let body = body.resolve(scope);
                scope.locals.pop();
                if is_pi {
                    Expr::pi(name, ty, body)
                } else {
                    Expr::lam(name, ty, body)
                }
            }
            Self::Let(n, ty, value, body) => {
                let ty = ty.resolve(scope);
                let value = value.resolve(scope);
                let name = Name::new(&n);
                scope.locals.push((n, name.clone()));
                let body = body.resolve(scope);
                scope.locals.pop();
                Expr::let_(name, ty, value, body)
            }
        }
    }
}

#[derive(Debug)]
pub(crate) enum Command {
    Axiom(Signature, Term),
    Define(Signature, Term, Term),
    Theorem(Signature, Term, Term),
    Inductive(Signature, Vec<Binding>, Term, Vec<(String, Term)>),
    InitQuot,
    Infer(Term),
    Check(Term, Term),
    Eval(Term),
    Equal(Term, Term),
}

/// A declaration as submitted to the kernel, whether or not it was accepted.
#[derive(Clone, Debug)]
pub enum Declaration {
    Axiom(String, Vec<String>, Expr),
    Definition(String, Vec<String>, Expr, Expr),
    Theorem(String, Vec<String>, Expr, Expr),
    Inductive(InductiveBlock),
    Quotient,
}

fn pis(mut e: &Expr) -> usize {
    let mut n = 0;
    while let Expr::Pi(_, b) = e {
        e = b.body();
        n += 1;
    }
    n
}

fn drop_pis(mut e: &Expr, n: usize) -> &Expr {
    for _ in 0..n {
        if let Expr::Pi(_, b) = e {
            e = b.body();
        }
    }
    e
}

/// The type, constructors and metadata of a single inductive, without a recursor.
fn inductive(
    (name, params): Signature,
    binders: Vec<Binding>,
    ty: Term,
    ctors: Vec<(String, Term)>,
) -> InductiveBlock {
    let num_params = binders.len();
    let levels = params.iter().cloned().map(Level::Param).collect();
    let mut scope = Scope {
        implicit: Some((name.clone(), levels)),
        ..Scope::default()
    };
    let ty = Term::binders(binders.clone(), ty, true).resolve(&mut scope);
    let constructors: Vec<_> = ctors
        .into_iter()
        .enumerate()
        .map(|(index, (n, t))| {
            let ty = Term::binders(binders.clone(), t, true).resolve(&mut scope);
            Constructor {
                name: n,
                params: params.clone(),
                num_fields: pis(drop_pis(&ty, num_params)),
                ty,
                inductive: name.clone(),
                index,
                num_params,
            }
        })
        .collect();
    InductiveBlock {
        types: vec![InductiveType {
            num_indices: pis(drop_pis(&ty, num_params)),
            name: name.clone(),
            params,
            ty,
            all: vec![name],
            constructors: constructors.iter().map(|c| c.name.clone()).collect(),
            num_params,
            num_nested: 0,
            recursive: false,
            reflexive: false,
        }],
        constructors,
        recursors: Vec::new(),
    }
}

pub fn parse_expr(source: &str) -> Result<Expr, Error> {
    grammar::ExprParser::new()
        .parse(lex(source, false))
        .map(|term| term.resolve(&mut Scope::default()))
        .map_err(|e| Error(e.to_string()))
}

fn program(source: &str) -> Result<Vec<Command>, Error> {
    grammar::ProgramParser::new()
        .parse(lex(source, true))
        .map_err(|e| Error(e.to_string()))
}

fn declare(d: Declaration, env: &mut Environment) -> Result<String, Error> {
    match d {
        Declaration::Axiom(n, ps, ty) => {
            env.declare(n.clone(), ps, ty, None, true)?;
            Ok(format!("axiom {n}"))
        }
        Declaration::Definition(n, ps, ty, value) => {
            env.declare(n.clone(), ps, ty, Some(value), true)?;
            Ok(format!("defined {n}"))
        }
        Declaration::Theorem(n, ps, ty, value) => {
            env.declare_theorem(n.clone(), ps, ty, value)?;
            Ok(format!("theorem {n}"))
        }
        Declaration::Inductive(block) => {
            let names = block
                .types
                .iter()
                .map(|t| &t.name)
                .chain(block.constructors.iter().map(|c| &c.name))
                .chain(block.recursors.iter().map(|r| &r.name))
                .cloned()
                .collect::<Vec<_>>()
                .join(" ");
            env.declare_inductive(block)?;
            Ok(format!("inductive {names}"))
        }
        Declaration::Quotient => {
            env.init_quotient()?;
            Ok("quotient".into())
        }
    }
}

fn execute(
    command: Command,
    env: &mut Environment,
    submitted: &mut Vec<Declaration>,
) -> Result<String, Error> {
    let resolve = |t: Term| t.resolve(&mut Scope::default());
    let d = match command {
        Command::Axiom((n, ps), ty) => Declaration::Axiom(n, ps, resolve(ty)),
        Command::Define((n, ps), ty, v) => Declaration::Definition(n, ps, resolve(ty), resolve(v)),
        Command::Theorem((n, ps), ty, v) => Declaration::Theorem(n, ps, resolve(ty), resolve(v)),
        Command::Inductive(signature, binders, ty, ctors) => Declaration::Inductive(
            env.complete_inductive(&inductive(signature, binders, ty, ctors))?,
        ),
        Command::InitQuot => Declaration::Quotient,
        command => return query(command, env),
    };
    submitted.push(d.clone());
    declare(d, env)
}

fn query(command: Command, env: &mut Environment) -> Result<String, Error> {
    let resolve = |t: Term| t.resolve(&mut Scope::default());
    match command {
        Command::Infer(e) => {
            let e = resolve(e);
            Ok(format!("{e} : {}", env.infer(&e)?))
        }
        Command::Check(e, ty) => {
            let e = resolve(e);
            let ty = resolve(ty);
            env.check(&e, &ty)?;
            Ok(format!("checked {e} : {ty}"))
        }
        Command::Eval(e) => Ok(env.normalize(&resolve(e))?.to_string()),
        Command::Equal(a, b) => {
            if !env.def_eq(&resolve(a), &resolve(b))? {
                return Err(Error("terms are not definitionally equal".into()));
            }
            Ok("equal".into())
        }
        _ => unreachable!("declarations are handled by execute"),
    }
}

/// Runs every command, stopping at the first failure.
pub fn run(source: &str, env: &mut Environment) -> Result<Vec<String>, Error> {
    program(source)?
        .into_iter()
        .enumerate()
        .map(|(i, command)| {
            execute(command, env, &mut Vec::new())
                .map_err(|e| Error(format!("command {}: {e}", i + 1)))
        })
        .collect()
}

/// Runs every command, keeping going past rejected ones.
pub fn session(source: &str, env: &mut Environment) -> Result<Vec<Result<String, Error>>, Error> {
    Ok(program(source)?
        .into_iter()
        .map(|command| execute(command, env, &mut Vec::new()))
        .collect())
}

/// Every declaration a script submits, including rejected ones, in order.
pub fn declarations(source: &str) -> Result<Vec<Declaration>, Error> {
    let mut env = Environment::new();
    let mut submitted = Vec::new();
    for command in program(source)? {
        let _ = execute(command, &mut env, &mut submitted);
    }
    Ok(submitted)
}
