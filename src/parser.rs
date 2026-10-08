use crate::kernel::{Constructor, InductiveBlock, InductiveType};
use crate::{Environment, Error, Expr, Level, lexer::lex};
use num_bigint::BigUint;
use offsides::LayoutMode;
use unbound::{Name, Shared};

lalrpop_util::lalrpop_mod!(
    #[allow(clippy::all, clippy::pedantic, clippy::restriction)]
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

#[derive(Default)]
struct Scope {
    locals: Vec<(String, Name<Expr>)>,
    implicit: Option<(String, Vec<Level>)>,
}

impl Term {
    pub(crate) fn binders(
        params: Vec<Binding>,
        body: Term,
        binder: fn(String, Box<Term>, Box<Term>) -> Term,
    ) -> Term {
        params.into_iter().rev().fold(body, |body, (n, ty)| {
            binder(n, Box::new(ty), Box::new(body))
        })
    }
    pub(crate) fn lets(defs: Vec<LocalDef>, body: Term) -> Term {
        defs.into_iter().rev().fold(body, |body, (n, ty, value)| {
            Term::Let(n, Box::new(ty), Box::new(value), Box::new(body))
        })
    }
    fn resolve(self, scope: &mut Scope) -> Expr {
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
            Self::Nat(n) => Expr::nat(n.parse::<BigUint>().expect("lexer yields digits")),
            Self::Str(s) => Expr::Str(s),
            Self::Proj(n, i, e) => Expr::Proj(n, i, Shared::new(e.resolve(scope))),
            Self::App(f, a) => f.resolve(scope).app(a.resolve(scope)),
            Self::Pi(n, ty, body) => scope.binder(n, *ty, *body, Expr::pi),
            Self::Lam(n, ty, body) => scope.binder(n, *ty, *body, Expr::lam),
            Self::Let(n, ty, value, body) => {
                let ty = ty.resolve(scope);
                let value = value.resolve(scope);
                let name = Name::new(&n);
                let body = scope.under(n, name.clone(), *body);
                Expr::let_(name, ty, value, body)
            }
        }
    }
}

impl Scope {
    fn under(&mut self, local: String, name: Name<Expr>, body: Term) -> Expr {
        self.locals.push((local, name));
        let body = body.resolve(self);
        self.locals.pop();
        body
    }

    fn binder(
        &mut self,
        local: String,
        ty: Term,
        body: Term,
        make: fn(Name<Expr>, Expr, Expr) -> Expr,
    ) -> Expr {
        let ty = ty.resolve(self);
        let name = Name::new(if local.is_empty() { "_" } else { &local });
        let body = self.under(local, name.clone(), body);
        make(name, ty, body)
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

#[derive(Clone, Debug)]
pub enum Declaration {
    Axiom(String, Vec<String>, Expr),
    Definition(String, Vec<String>, Expr, Expr),
    Theorem(String, Vec<String>, Expr, Expr),
    Inductive(InductiveBlock),
    Quotient,
}

fn resolve(term: Term) -> Expr {
    term.resolve(&mut Scope::default())
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

fn inductive(
    (name, params): Signature,
    binders: &[Binding],
    ty: Term,
    ctors: Vec<(String, Term)>,
) -> InductiveBlock {
    let num_params = binders.len();
    let levels = params.iter().cloned().map(Level::Param).collect();
    let mut scope = Scope {
        implicit: Some((name.clone(), levels)),
        ..Scope::default()
    };
    let ty = Term::binders(binders.to_vec(), ty, Term::Pi).resolve(&mut scope);
    let constructors: Vec<_> = ctors
        .into_iter()
        .enumerate()
        .map(|(index, (n, t))| {
            let ty = Term::binders(binders.to_vec(), t, Term::Pi).resolve(&mut scope);
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
        .parse(lex(source, LayoutMode::Lazy))
        .map(resolve)
        .map_err(|e| Error::Rejected(e.to_string()))
}

fn program(source: &str) -> Result<Vec<Command>, Error> {
    grammar::ProgramParser::new()
        .parse(lex(source, LayoutMode::Eager))
        .map_err(|e| Error::Rejected(e.to_string()))
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
            env.declare_inductive(&block)?;
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
    let d = match command {
        Command::Axiom((n, ps), ty) => Declaration::Axiom(n, ps, resolve(ty)),
        Command::Define((n, ps), ty, v) => Declaration::Definition(n, ps, resolve(ty), resolve(v)),
        Command::Theorem((n, ps), ty, v) => Declaration::Theorem(n, ps, resolve(ty), resolve(v)),
        Command::Inductive(signature, binders, ty, ctors) => {
            let block = inductive(signature, &binders, ty, ctors);
            match env.complete_inductive(&block) {
                Ok(block) => Declaration::Inductive(block),
                Err(e) => {
                    submitted.push(Declaration::Inductive(block));
                    return Err(e);
                }
            }
        }
        Command::InitQuot => Declaration::Quotient,
        command => return query(command, env),
    };
    submitted.push(d.clone());
    declare(d, env)
}

fn query(command: Command, env: &mut Environment) -> Result<String, Error> {
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
                return Err(Error::Rejected("terms are not definitionally equal".into()));
            }
            Ok("equal".into())
        }
        _ => unreachable!("declarations are handled by execute"),
    }
}

pub fn run(source: &str, env: &mut Environment) -> Result<Vec<String>, Error> {
    program(source)?
        .into_iter()
        .enumerate()
        .map(|(i, command)| {
            execute(command, env, &mut Vec::new())
                .map_err(|e| e.context(format_args!("command {}", i + 1)))
        })
        .collect()
}

pub fn session(source: &str, env: &mut Environment) -> Result<Vec<Result<String, Error>>, Error> {
    Ok(program(source)?
        .into_iter()
        .map(|command| execute(command, env, &mut Vec::new()))
        .collect())
}

pub fn declarations(source: &str) -> Result<Vec<Declaration>, Error> {
    let mut env = Environment::new();
    let mut submitted = Vec::new();
    for command in program(source)? {
        execute(command, &mut env, &mut submitted).ok();
    }
    Ok(submitted)
}
