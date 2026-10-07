use super::*;
use crate::parser::{parse_expr, run};

fn expr(source: &str) -> Expr {
    parse_expr(source).unwrap()
}
#[test]
fn relevance_respects_universes_and_unknown_telescope_tails() {
    let mut env = Environment::new();
    let a = Name::new("A");
    let x = Name::new("x");
    env.declare(
        "poly".into(),
        vec!["u".into()],
        Expr::pi(
            a.clone(),
            Expr::Sort(Level::Param("u".into())),
            Expr::pi(x, Expr::Var(a.clone()), Expr::Var(a)),
        ),
        None,
        true,
    )
    .unwrap();
    run("axiom P : Prop", &mut env).unwrap();
    let mut ty = Expr::constant("P");
    for _ in 0..65 {
        ty = Expr::pi(Name::new("h"), Expr::constant("P"), ty);
    }
    env.axiom("many", ty).unwrap();
    let mut tc = Checker::new(&env);
    tc.uparams.insert("u".into());
    let mut s = Session::new(&mut tc);
    let prop = s.summary("poly", &[Level::Nat(0)]).unwrap();
    let data = s.summary("poly", &[Level::Nat(1)]).unwrap();
    let unknown = s.summary("poly", &[Level::Param("u".into())]).unwrap();
    assert!(prop.proof_argument(1));
    assert_eq!(prop.result(2), Some(true));
    assert!(!data.proof_argument(1));
    assert_eq!(data.result(2), Some(false));
    assert!(!unknown.proof_argument(1));
    assert_eq!(unknown.result(2), None);
    let many = s.summary("many", &[]).unwrap();
    assert!(many.proof_argument(63));
    assert!(!many.proof_argument(64));
    assert_eq!(many.result(65), None);
    drop(s);
    let mut undeclared = Checker::new(&env);
    let mut undeclared = Session::new(&mut undeclared);
    assert!(
        undeclared
            .summary("poly", &[Level::Param("u".into())])
            .is_err()
    );
}
#[test]
fn speculative_comparison_falls_back_without_caching_failure() {
    let mut env = Environment::new();
    run("axiom A : Type; axiom a : A; axiom b : A; def hold : (forall (x : A), A) := fun (x : A) => a", &mut env).unwrap();
    let mut previous = Expr::constant("a");
    for i in 0..2200 {
        let name = format!("d{i}");
        env.define(&name, Expr::constant("A"), previous).unwrap();
        previous = Expr::constant(name);
    }
    let mut tc = Checker::new(&env);
    let mut s = Session::new(&mut tc);
    let slow = s.ev.term(previous, None);
    let fast = s.ev.term(Expr::constant("a"), None);
    let hold = s.ev.term(Expr::constant("hold"), None);
    let left = s.app(&hold, &slow);
    let right = s.app(&hold, &fast);
    let lv = s.ev.eval(&left, false).unwrap();
    let rv = s.ev.eval(&right, false).unwrap();
    assert!(!s.congruent(&lv, &rv).unwrap());
    assert!(s.ev.tc.probe_fuel.is_none());
    assert!(s.conv_terms(&left, &right, false).unwrap());
    assert!(s.conv_terms(&slow, &fast, false).unwrap());
    let different = s.ev.term(Expr::constant("b"), None);
    assert!(!s.conv_terms(&slow, &different, false).unwrap());
}

#[test]
fn dependent_inference_and_conversion_keep_closures() {
    let mut env = Environment::new();
    run("axiom A : Type; axiom a : A; axiom B : (forall (x : A), Type); axiom f : (forall (x : A), B x)", &mut env).unwrap();
    let mut tc = Checker::new(&env);
    let mut s = Session::new(&mut tc);
    let value = s.ev.term(expr("fun (T : Type) => fun (x : T) => x"), None);
    let expected =
        s.ev.term(expr("forall (T : Type), forall (x : T), T"), None);
    let actual = s.infer(&value, true).unwrap();
    s.check_type(&actual, &expected).unwrap();
    let value =
        s.ev.term(expr("(fun (g : (forall (x : A), B x)) => g a) f"), None);
    let expected = s.ev.term(expr("B a"), None);
    let actual = s.infer(&value, true).unwrap();
    s.check_type(&actual, &expected).unwrap();
    assert!(s.ev.state.quoted.is_empty());
}

#[test]
fn unchecked_inference_does_not_validate_discarded_arguments() {
    let mut env = Environment::new();
    run("axiom A : Type; axiom a : A", &mut env).unwrap();
    let mut tc = Checker::new(&env);
    let mut s = Session::new(&mut tc);
    for source in ["(fun (x : A) => a) Type", "let x : A := Type in a"] {
        let value = s.ev.term(expr(source), None);
        assert!(s.infer(&value, false).is_ok());
        assert!(s.infer(&value, true).is_err());
    }
}

#[test]
fn inference_closures_do_not_capture_sibling_binders() {
    let env = Environment::new();
    for source in [
        "fun (T : Type) => fun (x : T) => x",
        "fun (T : Type) => fun (U : Type) => fun (x : T) => fun (y : U) => x",
        "fun (T : Type) => let U : Type := T in fun (x : U) => x",
    ] {
        let e = expr(source);
        let actual = env.infer(&e).unwrap();
        let mut legacy = Checker::new(&env);
        legacy.semantic = false;
        let expected = legacy.infer(&e).unwrap();
        assert!(actual.fv().is_empty());
        assert!(legacy.conv(&actual, &expected).unwrap());
        env.check(&e, &actual).unwrap();
    }
}

#[test]
fn semantic_conversion_agrees_with_syntax_kernel() {
    let mut env = Environment::new();
    run("axiom A : Type; axiom a : A; axiom b : A; axiom P : Prop; axiom p : P; axiom q : P; axiom f : (forall (x : A), A); def id : (forall (x : A), A) := fun (x : A) => x", &mut env).unwrap();
    let terms = [
        "a",
        "b",
        "id a",
        "let x : A := a in x",
        "f a",
        "p",
        "q",
        "f",
        "fun (x : A) => f x",
        "fun (x : A) => x",
        "fun (x : A) => a",
    ];
    for a in terms.map(expr) {
        for b in terms.map(expr) {
            let mut legacy = Checker::new(&env);
            legacy.semantic = false;
            let ta = legacy.infer(&a).unwrap();
            let tb = legacy.infer(&b).unwrap();
            let expected = legacy.conv(&ta, &tb).unwrap() && legacy.conv(&a, &b).unwrap();
            assert_eq!(env.def_eq(&a, &b).unwrap(), expected, "{a} vs {b}");
        }
    }
}
