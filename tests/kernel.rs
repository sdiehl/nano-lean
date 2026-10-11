#![allow(clippy::unwrap_used, clippy::panic)]

use nano_lean::{Environment, kernel::Expr, parser::parse_expr};
use unbound::{Alpha, Name, Subst};

fn expr(s: &str) -> Expr {
    parse_expr(s).unwrap()
}

#[test]
fn open_declaration_types_are_rejected() {
    let mut env = Environment::new();
    assert!(env.axiom("open", Expr::Var(Name::new("x"))).is_err());
}

#[test]
fn substitution_cannot_capture_and_alpha_ignores_spelling() {
    let x = Name::new("x");
    let y = Name::new("x");
    let lam = Expr::lam(y.clone(), expr("A"), Expr::Var(x.clone()));
    let replaced = lam.subst(&x, &Expr::Var(y.clone()));
    assert_eq!(replaced.fv(), vec![y.to_any().unwrap()]);
    assert!(!replaced.aeq(&Expr::lam(y.clone(), expr("A"), Expr::Var(y))));
    assert!(
        expr("(fun (x : Type) => (fun (y : x) => y))")
            .aeq(&expr("(fun (A : Type) => (fun (a : A) => a))"))
    );
}

#[test]
fn normal_forms_reparse_with_outer_binders_intact() {
    let mut env = Environment::new();
    env.axiom("A", expr("Type")).unwrap();
    let source = expr("(fun (x : A) => ((fun (y : A) => (fun (x : A) => y)) x))");
    let expected = expr("(fun (outer : A) => (fun (inner : A) => outer))");
    let normal = env.normalize(&source).unwrap();
    assert!(normal.aeq(&expected));
    assert!(expr(&normal.to_string()).aeq(&expected));
}
