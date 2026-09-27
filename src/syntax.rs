use std::fmt;
use unbound::prelude::*;

pub type Binder = Bind<Name<Expr>, Box<Expr>>;

#[derive(Clone, Debug, Alpha, Subst)]
pub enum Expr {
    Var(Name<Expr>),
    Sort(u32),
    Const(String),
    App(Box<Expr>, Box<Expr>),
    Pi(Box<Expr>, Binder),
    Lam(Box<Expr>, Binder),
    Let(Box<Expr>, Box<Expr>, Binder),
}

impl Expr {
    pub fn constant(name: impl Into<String>) -> Self {
        Self::Const(name.into())
    }
    pub fn app(self, arg: Self) -> Self {
        Self::App(Box::new(self), Box::new(arg))
    }
    pub fn pi(name: Name<Self>, domain: Self, body: Self) -> Self {
        Self::Pi(Box::new(domain), bind(name, Box::new(body)))
    }
    pub fn lam(name: Name<Self>, domain: Self, body: Self) -> Self {
        Self::Lam(Box::new(domain), bind(name, Box::new(body)))
    }
    pub fn let_(name: Name<Self>, ty: Self, value: Self, body: Self) -> Self {
        Self::Let(Box::new(ty), Box::new(value), bind(name, Box::new(body)))
    }
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fn go(e: &Expr, scope: &mut NameScope, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match e {
                Expr::Var(n) => write!(f, "{}", scope.get(n)),
                Expr::Sort(0) => write!(f, "Prop"),
                Expr::Sort(1) => write!(f, "Type"),
                Expr::Sort(n) => write!(f, "(Sort {n})"),
                Expr::Const(n) => write!(f, "@{n}"),
                Expr::App(a, b) => {
                    write!(f, "(")?;
                    go(a, scope, f)?;
                    write!(f, " ")?;
                    go(b, scope, f)?;
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
