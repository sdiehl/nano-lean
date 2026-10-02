use nano_lean::{
    Environment, Expr,
    parser::{parse_expr as e, run},
};
use unbound::{Alpha, Name, Subst};

fn expr(s: &str) -> Expr {
    e(s).unwrap()
}
fn env() -> Environment {
    let mut env = Environment::new();
    run("axiom A : Type; axiom a : A; axiom b : A", &mut env).unwrap();
    env
}

#[test]
fn complete_example() {
    run(
        include_str!("../examples/core.ltc"),
        &mut Environment::new(),
    )
    .unwrap();
}

#[test]
fn universes_are_stratified_and_not_cumulative() {
    let env = env();
    assert!(env.infer(&expr("Prop")).unwrap().aeq(&expr("Type")));
    assert!(env.check(&expr("Type"), &expr("Type")).is_err());
    assert!(env.check(&expr("A"), &expr("(Sort 2)")).is_err());
    assert!(env.infer(&Expr::Sort(u32::MAX.into())).is_err());
    assert!(
        env.check(
            &expr("(forall (T : (Sort 3)), (forall (p : Prop), p))"),
            &expr("Prop")
        )
        .is_ok()
    );
    assert!(
        env.check(&expr("(forall (T : (Sort 3)), Type)"), &expr("(Sort 4)"))
            .is_ok()
    );
}

#[test]
fn dependent_application_and_bad_arguments() {
    let mut env = env();
    run(
        "axiom B : (forall (x : A), Type); axiom f : (forall (x : A), (B x))",
        &mut env,
    )
    .unwrap();
    env.check(&expr("(f a)"), &expr("(B a)")).unwrap();
    assert!(env.check(&expr("(f a)"), &expr("(B b)")).is_err());
    assert!(env.infer(&expr("(f Type)")).is_err());
    assert!(env.infer(&expr("(a a)")).is_err());
}

#[test]
fn rejected_declarations_do_not_change_environment() {
    let mut env = env();
    assert!(env.define("bad", expr("A"), expr("Type")).is_err());
    assert!(env.infer(&expr("bad")).is_err());
    assert!(env.define("loop", expr("A"), expr("loop")).is_err());
    assert!(env.axiom("A", expr("Prop")).is_err());
    assert!(env.axiom("badType", expr("a")).is_err());
    assert!(env.axiom("open", Expr::Var(Name::new("x"))).is_err());
    env.check(&expr("a"), &expr("A")).unwrap();
}

#[test]
fn beta_delta_zeta_and_nested_shadowing() {
    let mut env = env();
    run(
        "def id : (forall (T : Type), (forall (x : T), T)) := (fun (T : Type) => (fun (x : T) => x))",
        &mut env,
    )
    .unwrap();
    assert!(env.normalize(&expr("(id A a)")).unwrap().aeq(&expr("a")));
    assert!(
        env.def_eq(
            &expr("(let T : Type := A in (let x : T := a in x))"),
            &expr("a")
        )
        .unwrap()
    );
    assert!(
        env.def_eq(
            &expr("((fun (x : A) => (fun (x : A) => x)) a b)"),
            &expr("b")
        )
        .unwrap()
    );
    assert!(env.infer(&expr("(let x : A := Type in a)")).is_err());
    assert!(env.infer(&expr("(fun (x : a) => x)")).is_err());
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
fn reduction_preserves_outer_binders() {
    let env = env();
    let source = expr("(fun (x : A) => ((fun (y : A) => (fun (x : A) => y)) x))");
    let expected = expr("(fun (outer : A) => (fun (inner : A) => outer))");
    let normal = env.normalize(&source).unwrap();
    assert!(normal.aeq(&expected));
    assert!(expr(&normal.to_string()).aeq(&expected));
}

#[test]
fn eta_and_proof_irrelevance_but_not_proposition_irrelevance() {
    let mut env = env();
    run(
        "axiom f : (forall (x : A), A); axiom P : Prop; axiom Q : Prop; axiom p : P; axiom q : P; axiom r : Q",
        &mut env,
    )
    .unwrap();
    assert!(
        env.def_eq(&expr("f"), &expr("(fun (x : A) => (f x))"))
            .unwrap()
    );
    assert!(env.def_eq(&expr("p"), &expr("q")).unwrap());
    assert!(!env.def_eq(&expr("p"), &expr("r")).unwrap());
    assert!(!env.def_eq(&expr("P"), &expr("Q")).unwrap());
    assert!(!env.def_eq(&expr("a"), &expr("b")).unwrap());
    assert!(env.def_eq(&expr("missing"), &expr("missing")).is_err());
}

#[test]
fn parser_rejects_malformed_input_and_reports_command() {
    for s in [
        "(",
        ")",
        "()",
        "(Sort nope)",
        "(Sort 1 2)",
        "(fun x x)",
        "(let (x Type) Type)",
    ] {
        assert!(e(s).is_err(), "accepted {s}");
    }
    let err = run("axiom A : Type; check A : Prop", &mut Environment::new()).unwrap_err();
    assert!(err.0.starts_with("command 2:"));
}

#[test]
fn constants_survive_printing_under_same_spelled_binders() {
    let original = expr("(fun (A : Type) => @A)");
    assert!(expr(&original.to_string()).aeq(&original));
}

#[test]
fn lazy_conversion_can_discard_unequal_arguments() {
    let mut env = env();
    run("def erase : A -> A := fun (x : A) => a", &mut env).unwrap();
    assert!(env.def_eq(&expr("erase a"), &expr("erase b")).unwrap());
    assert!(!env.def_eq(&expr("a"), &expr("b")).unwrap());
    assert!(env.infer(&expr("erase Type")).is_err());
}

#[test]
fn suspended_arguments_keep_their_lexical_context() {
    let env = env();
    for (input, expected) in [
        (
            "(fun (x : A) => (fun (y : A) => fun (z : A) => x) b) a",
            "fun (z : A) => a",
        ),
        (
            "(fun (x : A) => (fun (y : A) => fun (z : A) => y) x) b",
            "fun (z : A) => b",
        ),
        ("(fun (T : Type) => fun (x : T) => x) A", "fun (x : A) => x"),
        (
            "let T : Type := A in let x : T := a in (fun (y : T) => x) b",
            "a",
        ),
    ] {
        assert!(
            env.normalize(&expr(input)).unwrap().aeq(&expr(expected)),
            "{input}"
        );
    }
}
