use nano_lean::{
    Environment, Expr,
    parser::{parse_expr, run},
};
use unbound::{Alpha, Name};

fn expr(s: &str) -> Expr {
    parse_expr(s).unwrap()
}

#[test]
fn precedence_and_multiple_binders() {
    assert!(expr("A -> B -> C").aeq(&expr("forall (x : A), forall (y : B), C")));
    assert!(expr("f a b").aeq(&expr("(f a) b")));
    assert!(!expr("f (a b)").aeq(&expr("f a b")));
    assert!(expr("fun (A : Type) (x : A) => x").aeq(&expr("fun (A : Type) => fun (x : A) => x")));
    assert!(expr("∀ (A : Type), A → A").aeq(&expr("forall (A : Type), A -> A")));
    assert!(expr("λ (A : Type) => A").aeq(&expr("fun (A : Type) => A")));
}

#[test]
fn layout_with_comments_blank_lines_and_continuations() {
    let source = "-- identity\n\ndef id : forall (A : Type), A -> A :=\n  fun (A : Type) (x : A) => x\n\naxiom A : Type -- a type\naxiom a : A\nequal id A a == a\n";
    assert_eq!(
        run(source, &mut Environment::new())
            .unwrap()
            .last()
            .unwrap(),
        "equal"
    );
    assert!(run(&source.replace('\n', "\r\n"), &mut Environment::new()).is_ok());
    assert!(
        run("-- empty\n", &mut Environment::new())
            .unwrap()
            .is_empty()
    );
}

#[test]
fn sequential_and_nested_let_layout() {
    let block = "let\n  T : Type := A\n  x : T := let\n    y : T := a\n  in y\nin x";
    let inline = "let T : Type := A in let x : T := (let y : T := a in y) in x";
    assert!(expr(block).aeq(&expr(inline)));
    assert!(
        expr("let\n\tT : Type := A\n\tx : T := a\nin x")
            .aeq(&expr("let T : Type := A in let x : T := a in x"))
    );
    let mut env = Environment::new();
    run("axiom A : Type; axiom a : A;", &mut env).unwrap();
    assert!(env.def_eq(&expr(block), &expr("a")).unwrap());
}

#[test]
fn parentheses_suppress_layout_and_semicolons_mix_with_newlines() {
    let source = "axiom A : Type;\naxiom a : A;\ndef id : (\nforall (T : Type),\nT -> T\n) := (\nfun (T : Type) (x : T) =>\nx\n);\nequal id A a == a;\n";
    run(source, &mut Environment::new()).unwrap();
}

#[test]
fn malformed_layout_and_lexical_errors_are_rejected() {
    for source in [
        "def id : Type :=\nType",
        "axiom A : Type\n  axiom a : A",
        "eval let\n  T : Type := Type\n  T",
        "eval $",
        "eval Sort 4294967296",
        "def fun : Type := Type",
    ] {
        assert!(
            run(source, &mut Environment::new()).is_err(),
            "accepted {source}"
        );
    }
}

#[test]
fn binder_scopes_exclude_domains_and_let_values() {
    assert!(
        expr("fun (A : Type) => fun (A : A) => A").aeq(&expr("fun (T : Type) => fun (x : T) => x"))
    );
    assert!(
        expr("fun (x : A) => let x : A := x in x").aeq(&expr("fun (a : A) => let b : A := a in b"))
    );
    assert!(
        expr("fun (_ : Type) => A -> _").aeq(&expr("fun (T : Type) => forall (unused : A), T"))
    );
}

#[test]
fn printed_terms_roundtrip_even_with_keyword_binder_hints() {
    for spelling in [
        "Sort", "Prop", "Type", "forall", "fun", "let", "in", "axiom", "def", "infer", "check",
        "eval", "equal",
    ] {
        let n = Name::new(spelling);
        let original = Expr::lam(
            n.clone(),
            expr("Type -> Type"),
            Expr::Var(n).app(expr("Type")),
        );
        assert!(expr(&original.to_string()).aeq(&original));
    }
    let original = expr("fun (x : A) => let y : A := x in fun (x : A) => y");
    assert!(expr(&original.to_string()).aeq(&original));
}
