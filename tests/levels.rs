#![allow(clippy::unwrap_used, clippy::panic)]

use nano_lean::{Environment, Expr, Level};
use std::collections::BTreeMap;
use unbound::Name;

fn p(n: &str) -> Level {
    Level::Param(n.into())
}
fn eval(l: &Level, u: u32, v: u32) -> u32 {
    match l {
        Level::Nat(n) => *n,
        Level::Param(n) => {
            if n == "u" {
                u
            } else {
                v
            }
        }
        Level::Succ(a) => eval(a, u, v) + 1,
        Level::Max(a, b) => eval(a, u, v).max(eval(b, u, v)),
        Level::IMax(a, b) => {
            let b = eval(b, u, v);
            if b == 0 { 0 } else { eval(a, u, v).max(b) }
        }
    }
}

#[test]
fn max_and_imax_laws() {
    let u = p("u");
    let v = p("v");
    let w = p("w");
    for (a, b) in [
        (
            Level::max(u.clone(), v.clone()),
            Level::max(v.clone(), u.clone()),
        ),
        (Level::max(u.clone(), u.clone()), u.clone()),
        (
            Level::max(Level::max(u.clone(), v.clone()), w.clone()),
            Level::max(u.clone(), Level::max(v.clone(), w)),
        ),
        (
            Level::max(u.clone(), u.clone().succ().unwrap()),
            u.clone().succ().unwrap(),
        ),
        (Level::imax(u.clone(), Level::Nat(0)), Level::Nat(0)),
        (
            Level::imax(u.clone(), v.clone().succ().unwrap()),
            Level::max(u.clone(), v.clone().succ().unwrap()),
        ),
        (Level::imax(u.clone(), u.clone()), u.clone()),
        (
            Level::imax(u.clone(), Level::imax(v.clone(), u.clone())),
            Level::imax(v.clone(), u.clone()),
        ),
    ] {
        assert!(a.equivalent(&b).unwrap(), "{a} != {b}");
    }
    assert!(
        !Level::imax(u.clone(), v.clone())
            .equivalent(&Level::max(u, v))
            .unwrap()
    );
}

#[test]
fn accepted_symbolic_equalities_agree_with_numeric_evaluation() {
    let mut terms = vec![Level::Nat(0), Level::Nat(1), p("u"), p("v")];
    let base = terms.clone();
    for a in &base {
        terms.push(a.clone().succ().unwrap());
        for b in &base {
            terms.push(Level::max(a.clone(), b.clone()));
            terms.push(Level::imax(a.clone(), b.clone()));
        }
    }
    for a in &terms {
        for b in &terms {
            let equivalent = a.equivalent(b).unwrap();
            let samples = (0..5).all(|u| (0..5).all(|v| eval(a, u, v) == eval(b, u, v)));
            assert_eq!(equivalent, samples, "{a} versus {b}");
        }
    }
}

#[test]
fn polymorphic_constants_require_declared_parameters_and_correct_arity() {
    let mut env = Environment::new();
    let a = Name::new("A");
    let x = Name::new("x");
    let ty = Expr::pi(
        a.clone(),
        Expr::Sort(p("u")),
        Expr::pi(x.clone(), Expr::Var(a.clone()), Expr::Var(a.clone())),
    );
    let body = Expr::lam(
        a.clone(),
        Expr::Sort(p("u")),
        Expr::lam(x.clone(), Expr::Var(a), Expr::Var(x)),
    );
    assert!(env.define("bad", ty.clone(), body.clone()).is_err());
    assert!(
        env.declare(
            "bad".into(),
            vec!["u".into(), "u".into()],
            ty.clone(),
            Some(body.clone()),
            true
        )
        .is_err()
    );
    env.declare("id".into(), vec!["u".into()], ty, Some(body), true)
        .unwrap();
    assert!(env.infer(&Expr::constant("id")).is_err());
    assert!(env.infer(&Expr::Const("id".into(), vec![p("v")])).is_err());
    let id = Expr::Const("id".into(), vec![Level::Nat(2)]);
    let term = id
        .app(Expr::Sort(Level::Nat(1)))
        .app(Expr::Sort(Level::Nat(0)));
    env.check(&term, &Expr::Sort(Level::Nat(1))).unwrap();
    assert!(env.def_eq(&term, &Expr::Sort(Level::Nat(0))).unwrap());
}

#[test]
fn substitution_and_opaque_bodies() {
    let level = Level::imax(p("u"), p("v"));
    assert_eq!(
        level
            .substitute(&BTreeMap::from([
                ("u".into(), Level::Nat(5)),
                ("v".into(), Level::Nat(0))
            ]))
            .unwrap(),
        Level::Nat(0)
    );
    let mut env = Environment::new();
    env.declare(
        "T".into(),
        vec![],
        Expr::Sort(Level::Nat(1)),
        Some(Expr::Sort(Level::Nat(0))),
        false,
    )
    .unwrap();
    assert!(
        !env.def_eq(&Expr::constant("T"), &Expr::Sort(Level::Nat(0)))
            .unwrap()
    );
    assert!(
        env.declare_theorem(
            "invalid".into(),
            vec![],
            Expr::Sort(Level::Nat(1)),
            Expr::Sort(Level::Nat(0))
        )
        .is_err()
    );
}
