use nano_lean::{Environment, Expr, Level, parser::parse_expr};
use num_bigint::BigUint;
use unbound::{Alpha, Name, Shared};

fn expr(s: &str) -> Expr {
    parse_expr(s).unwrap()
}
fn naturals() -> Environment {
    let mut env = Environment::new();
    env.axiom("Nat", expr("Type")).unwrap();
    env.axiom("Nat.zero", expr("Nat")).unwrap();
    env.axiom("Nat.succ", expr("Nat -> Nat")).unwrap();
    env.axiom("Bool", expr("Type")).unwrap();
    env.axiom("Bool.true", expr("Bool")).unwrap();
    env.axiom("Bool.false", expr("Bool")).unwrap();
    for op in [
        "add",
        "sub",
        "mul",
        "pow",
        "div",
        "mod",
        "gcd",
        "land",
        "lor",
        "xor",
        "shiftLeft",
        "shiftRight",
        "beq",
        "ble",
    ] {
        let ty = if matches!(op, "beq" | "ble") {
            "Nat -> Nat -> Bool"
        } else {
            "Nat -> Nat -> Nat"
        };
        env.axiom(format!("Nat.{op}"), expr(ty)).unwrap();
    }
    env
}
fn operation(op: &str, a: u32, b: u32) -> Expr {
    Expr::constant(format!("Nat.{op}"))
        .app(Expr::nat(a))
        .app(Expr::nat(b))
}

#[test]
fn primitive_natural_operations_and_zero_divisors() {
    let env = naturals();
    for (op, a, b, expected) in [
        ("add", 17, 23, 40),
        ("sub", 17, 23, 0),
        ("sub", 23, 17, 6),
        ("mul", 17, 23, 391),
        ("pow", 3, 5, 243),
        ("pow", 0, 0, 1),
        ("div", 23, 5, 4),
        ("div", 23, 0, 0),
        ("mod", 23, 5, 3),
        ("mod", 23, 0, 23),
        ("gcd", 54, 24, 6),
        ("gcd", 0, 0, 0),
        ("land", 10, 12, 8),
        ("lor", 10, 12, 14),
        ("xor", 10, 12, 6),
        ("shiftLeft", 3, 5, 96),
        ("shiftRight", 96, 5, 3),
    ] {
        assert!(
            env.normalize(&operation(op, a, b))
                .unwrap()
                .aeq(&Expr::nat(expected as u32)),
            "{op} {a} {b}"
        );
    }
    for (op, a, b, expected) in [
        ("beq", 4, 4, true),
        ("beq", 4, 5, false),
        ("ble", 4, 5, true),
        ("ble", 5, 4, false),
    ] {
        assert!(
            env.normalize(&operation(op, a, b))
                .unwrap()
                .aeq(&Expr::constant(if expected {
                    "Bool.true"
                } else {
                    "Bool.false"
                }))
        );
    }
}

#[test]
fn large_naturals_stay_exact_and_resource_limits_are_explicit() {
    let env = naturals();
    let big = BigUint::parse_bytes(b"340282366920938463463374607431768211457", 10).unwrap();
    let term = Expr::constant("Nat.mul")
        .app(Expr::nat(big.clone()))
        .app(Expr::nat(big.clone()));
    assert!(env.normalize(&term).unwrap().aeq(&Expr::nat(&big * &big)));
    assert!(
        env.normalize(
            &Expr::constant("Nat.shiftRight")
                .app(Expr::nat(123u32))
                .app(Expr::nat(big.clone()))
        )
        .unwrap()
        .aeq(&Expr::nat(0u32))
    );
    let huge_shift = Expr::constant("Nat.shiftLeft")
        .app(Expr::nat(1u32))
        .app(Expr::nat(big.clone()));
    assert!(
        env.normalize(&huge_shift)
            .unwrap_err()
            .0
            .starts_with("unsupported:")
    );
    for a in [0u32, 1] {
        let term = Expr::constant("Nat.pow")
            .app(Expr::nat(a))
            .app(Expr::nat(big.clone()));
        assert!(env.normalize(&term).unwrap().aeq(&Expr::nat(a)));
    }
}

#[test]
fn natural_literals_compare_with_constructor_chains_and_neutral_terms() {
    let mut env = naturals();
    let two =
        Expr::constant("Nat.succ").app(Expr::constant("Nat.succ").app(Expr::constant("Nat.zero")));
    assert!(env.def_eq(&Expr::nat(2u32), &two).unwrap());
    assert!(!env.def_eq(&Expr::nat(3u32), &two).unwrap());
    assert!(
        env.def_eq(&Expr::nat(0u32), &Expr::constant("Nat.zero"))
            .unwrap()
    );
    env.axiom("n", expr("Nat")).unwrap();
    assert!(
        !env.def_eq(&Expr::nat(2u32), &Expr::constant("Nat.succ").app(expr("n")))
            .unwrap()
    );
    // The literal must remain closed while instantiating a binder around it.
    let x = Name::new("x");
    let value = Expr::nat(123u32);
    let term = Expr::lam(x, expr("Nat"), value.clone()).app(Expr::nat(7u32));
    assert!(env.normalize(&term).unwrap().aeq(&value));
    assert!(Shared::new(value).fv().is_empty());
}

#[test]
fn literals_require_declared_well_formed_types() {
    let env = Environment::new();
    assert!(env.infer(&Expr::nat(0u32)).is_err());
    assert!(env.infer(&Expr::Str("x".into())).is_err());
    let mut env = Environment::new();
    env.axiom("Nat", expr("Prop")).unwrap();
    assert!(env.infer(&Expr::nat(0u32)).is_err());
}

#[test]
fn unicode_strings_compare_with_lists_of_codepoints() {
    let mut env = naturals();
    env.axiom("Char", expr("Type")).unwrap();
    env.axiom("Char.ofNat", expr("Nat -> Char")).unwrap();
    let u = Level::Param("u".into());
    let a = Name::new("A");
    let av = Expr::Var(a.clone());
    let list_a = Expr::Const("List".into(), vec![u.clone()]).app(av.clone());
    env.declare(
        "List".into(),
        vec!["u".into()],
        Expr::pi(
            a.clone(),
            Expr::Sort(u.clone().succ().unwrap()),
            Expr::Sort(u.clone().succ().unwrap()),
        ),
        None,
        false,
    )
    .unwrap();
    env.declare(
        "List.nil".into(),
        vec!["u".into()],
        Expr::pi(
            a.clone(),
            Expr::Sort(u.clone().succ().unwrap()),
            list_a.clone(),
        ),
        None,
        false,
    )
    .unwrap();
    env.declare(
        "List.cons".into(),
        vec!["u".into()],
        Expr::pi(
            a,
            Expr::Sort(u.succ().unwrap()),
            Expr::pi(
                Name::new("head"),
                av,
                Expr::pi(Name::new("tail"), list_a.clone(), list_a),
            ),
        ),
        None,
        false,
    )
    .unwrap();
    env.axiom("String", expr("Type")).unwrap();
    let chars = Expr::Const("List".into(), vec![Level::Nat(0)]).app(expr("Char"));
    env.axiom(
        "String.ofList",
        Expr::pi(Name::new("xs"), chars, expr("String")),
    )
    .unwrap();
    for (text, codepoints) in [("", vec![]), ("Aé水🦀\0", vec![65, 233, 27700, 129408, 0])] {
        let mut list = Expr::Const("List.nil".into(), vec![Level::Nat(0)]).app(expr("Char"));
        for cp in codepoints.into_iter().rev() {
            list = Expr::Const("List.cons".into(), vec![Level::Nat(0)])
                .app(expr("Char"))
                .app(Expr::constant("Char.ofNat").app(Expr::nat(cp as u32)))
                .app(list);
        }
        let constructor = Expr::constant("String.ofList").app(list);
        assert!(env.def_eq(&Expr::Str(text.into()), &constructor).unwrap());
        assert!(env.def_eq(&constructor, &Expr::Str(text.into())).unwrap());
    }
    assert!(
        !env.def_eq(&Expr::Str("é".into()), &Expr::Str("e\u{301}".into()))
            .unwrap()
    );
}
