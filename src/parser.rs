use crate::{Environment, Error, Expr, lexer::lex};
use unbound::Name;

lalrpop_util::lalrpop_mod!(
    #[allow(clippy::all)]
    grammar
);

#[derive(Debug)]
pub(crate) enum Term {
    Name(String),
    Global(String),
    Sort(u32),
    App(Box<Term>, Box<Term>),
    Pi(String, Box<Term>, Box<Term>),
    Lam(String, Box<Term>, Box<Term>),
    Let(String, Box<Term>, Box<Term>, Box<Term>),
}

pub(crate) type Binding = (String, Term);
pub(crate) type LocalDef = (String, Term, Term);

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
    fn resolve(self, locals: &mut Vec<(String, Name<Expr>)>) -> Expr {
        let is_pi = matches!(self, Self::Pi(..));
        match self {
            Self::Name(n) => locals
                .iter()
                .rev()
                .find(|(s, _)| s == &n)
                .map_or_else(|| Expr::constant(&n), |(_, n)| Expr::Var(n.clone())),
            Self::Global(n) => Expr::constant(n),
            Self::Sort(u) => Expr::Sort(u),
            Self::App(f, a) => f.resolve(locals).app(a.resolve(locals)),
            Self::Pi(n, ty, body) | Self::Lam(n, ty, body) => {
                let ty = ty.resolve(locals);
                let name = Name::new(if n.is_empty() { "_" } else { &n });
                locals.push((n, name.clone()));
                let body = body.resolve(locals);
                locals.pop();
                if is_pi {
                    Expr::pi(name, ty, body)
                } else {
                    Expr::lam(name, ty, body)
                }
            }
            Self::Let(n, ty, value, body) => {
                let ty = ty.resolve(locals);
                let value = value.resolve(locals);
                let name = Name::new(&n);
                locals.push((n, name.clone()));
                let body = body.resolve(locals);
                locals.pop();
                Expr::let_(name, ty, value, body)
            }
        }
    }
}

#[derive(Debug)]
pub(crate) enum Command {
    Axiom(String, Term),
    Define(String, Term, Term),
    Infer(Term),
    Check(Term, Term),
    Eval(Term),
    Equal(Term, Term),
}

pub fn parse_expr(source: &str) -> Result<Expr, Error> {
    grammar::ExprParser::new()
        .parse(lex(source, false))
        .map(|term| term.resolve(&mut Vec::new()))
        .map_err(|e| Error(e.to_string()))
}

pub fn run(source: &str, env: &mut Environment) -> Result<Vec<String>, Error> {
    let commands = grammar::ProgramParser::new()
        .parse(lex(source, true))
        .map_err(|e| Error(e.to_string()))?;
    commands
        .into_iter()
        .enumerate()
        .map(|(i, command)| {
            let resolve = |t: Term| t.resolve(&mut Vec::new());
            let execute = || -> Result<String, Error> {
                match command {
                    Command::Axiom(n, ty) => {
                        env.axiom(&n, resolve(ty))?;
                        Ok(format!("axiom {n}"))
                    }
                    Command::Define(n, ty, value) => {
                        env.define(&n, resolve(ty), resolve(value))?;
                        Ok(format!("defined {n}"))
                    }
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
                }
            };
            execute().map_err(|e| Error(format!("command {}: {e}", i + 1)))
        })
        .collect()
}
