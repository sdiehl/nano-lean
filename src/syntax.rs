use crate::{Error, Level};
use std::{
    collections::{BTreeMap, HashMap},
    fmt,
};
use unbound::prelude::*;

pub type Binder = Bind<Name<Expr>, Shared<Expr>>;

#[derive(Clone, Debug, Alpha, Subst)]
pub enum Expr {
    Var(Name<Expr>),
    Sort(Level),
    Const(String, Vec<Level>),
    App(Shared<Expr>, Shared<Expr>),
    Proj(String, usize, Shared<Expr>),
    Pi(Shared<Expr>, Binder),
    Lam(Shared<Expr>, Binder),
    Let(Shared<Expr>, Shared<Expr>, Binder),
}

impl Expr {
    pub fn substitute_levels(&self, levels: &BTreeMap<String, Level>) -> Result<Self, Error> {
        if levels
            .iter()
            .all(|(name, value)| value == &Level::Param(name.clone()))
        {
            return Ok(self.clone());
        }
        fn shared(
            e: &Shared<Expr>,
            levels: &BTreeMap<String, Level>,
            memo: &mut HashMap<usize, Shared<Expr>>,
        ) -> Result<Shared<Expr>, Error> {
            let key = e.as_ptr() as usize;
            if let Some(e) = memo.get(&key) {
                return Ok(e.clone());
            }
            let out = Shared::new(go(e, levels, memo)?);
            memo.insert(key, out.clone());
            Ok(out)
        }
        fn go(
            e: &Expr,
            levels: &BTreeMap<String, Level>,
            memo: &mut HashMap<usize, Shared<Expr>>,
        ) -> Result<Expr, Error> {
            let binder =
                |b: &Binder, memo: &mut HashMap<usize, Shared<Expr>>| -> Result<Binder, Error> {
                    Ok(bind(b.pattern().clone(), shared(b.body(), levels, memo)?))
                };
            Ok(match e {
                Expr::Var(n) => Expr::Var(n.clone()),
                Expr::Sort(u) => Expr::Sort(u.substitute(levels)?),
                Expr::Const(n, us) => Expr::Const(
                    n.clone(),
                    us.iter()
                        .map(|u| u.substitute(levels))
                        .collect::<Result<_, _>>()?,
                ),
                Expr::App(f, a) => Expr::App(shared(f, levels, memo)?, shared(a, levels, memo)?),
                Expr::Proj(n, i, e) => Expr::Proj(n.clone(), *i, shared(e, levels, memo)?),
                Expr::Pi(a, b) => Expr::Pi(shared(a, levels, memo)?, binder(b, memo)?),
                Expr::Lam(a, b) => Expr::Lam(shared(a, levels, memo)?, binder(b, memo)?),
                Expr::Let(a, v, b) => Expr::Let(
                    shared(a, levels, memo)?,
                    shared(v, levels, memo)?,
                    binder(b, memo)?,
                ),
            })
        }
        go(self, levels, &mut HashMap::new())
    }
    pub fn constant(name: impl Into<String>) -> Self {
        Self::Const(name.into(), Vec::new())
    }
    pub fn app(self, arg: Self) -> Self {
        Self::App(Shared::new(self), Shared::new(arg))
    }
    pub fn pi(name: Name<Self>, domain: Self, body: Self) -> Self {
        Self::Pi(Shared::new(domain), bind(name, Shared::new(body)))
    }
    pub fn lam(name: Name<Self>, domain: Self, body: Self) -> Self {
        Self::Lam(Shared::new(domain), bind(name, Shared::new(body)))
    }
    pub fn let_(name: Name<Self>, ty: Self, value: Self, body: Self) -> Self {
        Self::Let(
            Shared::new(ty),
            Shared::new(value),
            bind(name, Shared::new(body)),
        )
    }
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fn go(e: &Expr, scope: &mut NameScope, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match e {
                Expr::Var(n) => write!(f, "{}", scope.get(n)),
                Expr::Sort(Level::Nat(0)) => write!(f, "Prop"),
                Expr::Sort(Level::Nat(1)) => write!(f, "Type"),
                Expr::Sort(n) => write!(f, "(Sort {n})"),
                Expr::Const(n, us) => {
                    write!(f, "@{n}")?;
                    if !us.is_empty() {
                        write!(
                            f,
                            ".{{{}}}",
                            us.iter()
                                .map(ToString::to_string)
                                .collect::<Vec<_>>()
                                .join(", ")
                        )?;
                    }
                    Ok(())
                }
                Expr::App(a, b) => {
                    write!(f, "(")?;
                    go(a, scope, f)?;
                    write!(f, " ")?;
                    go(b, scope, f)?;
                    write!(f, ")")
                }
                Expr::Proj(n, i, e) => {
                    write!(f, "(proj {n} {i} ")?;
                    go(e, scope, f)?;
                    write!(f, ")")
                }
                Expr::Pi(ty, b) | Expr::Lam(ty, b) | Expr::Let(ty, _, b) => {
                    let (n, body) = b.unbind_ref();
                    let hint = match n.string() {
                        Some(
                            "Sort" | "Prop" | "Type" | "forall" | "fun" | "let" | "in" | "axiom"
                            | "def" | "infer" | "check" | "eval" | "equal",
                        ) => Name::<Expr>::new(format!("{}_", n.string().unwrap())),
                        _ => n.clone(),
                    };
                    let display = scope.pick(&hint, &body.fv());
                    let tag = match e {
                        Expr::Pi(..) => "forall",
                        Expr::Lam(..) => "fun",
                        _ => "let",
                    };
                    if matches!(e, Expr::Let(..)) {
                        write!(f, "(let {display} : ")?;
                    } else {
                        write!(f, "({tag} ({display} : ")?;
                    }
                    go(ty, scope, f)?;
                    match e {
                        Expr::Pi(..) => write!(f, "), ")?,
                        Expr::Lam(..) => write!(f, ") => ")?,
                        Expr::Let(_, value, _) => {
                            write!(f, " := ")?;
                            go(value, scope, f)?;
                            write!(f, " in ")?;
                        }
                        _ => unreachable!(),
                    }
                    scope.push(&n, display);
                    go(&body, scope, f)?;
                    scope.pop();
                    write!(f, ")")
                }
            }
        }
        go(self, &mut NameScope::new(&self.fv()), f)
    }
}
