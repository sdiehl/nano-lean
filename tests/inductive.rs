use nano_lean::{
    Environment, Expr, Level,
    kernel::{Constructor, InductiveBlock, InductiveType, Recursor, RecursorRule},
    parser::parse_expr,
};

fn expr(source: &str) -> Expr {
    parse_expr(source).unwrap()
}

fn poly(source: &str) -> Expr {
    let Expr::Lam(_, body) = expr(&format!("fun (U : Sort 2) => {source}")) else {
        unreachable!()
    };
    (*body.instantiate(&Expr::Sort(Level::Param("u".into())))).clone()
}

fn switch() -> InductiveBlock {
    InductiveBlock {
        types: vec![InductiveType {
            name: "Switch".into(),
            params: vec![],
            ty: expr("Type"),
            all: vec!["Switch".into()],
            constructors: vec!["left".into(), "right".into()],
            num_params: 0,
            num_indices: 0,
            num_nested: 0,
            recursive: false,
            reflexive: false,
        }],
        constructors: ["left", "right"]
            .into_iter()
            .enumerate()
            .map(|(index, name)| Constructor {
                name: name.into(),
                params: vec![],
                ty: expr("Switch"),
                inductive: "Switch".into(),
                index,
                num_params: 0,
                num_fields: 0,
            })
            .collect(),
        recursors: vec![Recursor {
            name: "Switch.rec".into(),
            params: vec!["u".into()],
            ty: poly("forall (m : Switch -> U), m left -> m right -> forall (s : Switch), m s"),
            all: vec!["Switch".into()],
            num_params: 0,
            num_indices: 0,
            num_motives: 1,
            num_minors: 2,
            k: false,
            rules: [("left", "l"), ("right", "r")]
                .into_iter()
                .map(|(constructor, result)| RecursorRule {
                    constructor: constructor.into(),
                    num_fields: 0,
                    rhs: poly(&format!(
                        "fun (m : Switch -> U) (l : m left) (r : m right) => {result}"
                    )),
                })
                .collect(),
        }],
    }
}

#[test]
fn negative_recursive_occurrences_are_rejected() {
    Environment::new().declare_inductive(switch()).unwrap();
    for ty in [
        "(Switch -> Switch) -> Switch",
        "((Switch -> Switch) -> Switch) -> Switch",
    ] {
        let mut block = switch();
        block.constructors[0].ty = expr(ty);
        block.constructors[0].num_fields = 1;
        let error = Environment::new().declare_inductive(block).unwrap_err();
        assert_eq!(error.0, "negative inductive occurrence");
    }
}

#[test]
fn forged_recursor_rules_are_rejected() {
    Environment::new().declare_inductive(switch()).unwrap();
    let mut block = switch();
    let Expr::Lam(_, body) =
        poly("fun (R : Type) (m : Switch -> U) (l : m left) (r : m right) => R m l r left")
    else {
        unreachable!()
    };
    block.recursors[0].rules[0].rhs = (*body.instantiate(&Expr::Const(
        "Switch.rec".into(),
        vec![Level::Param("u".into())],
    )))
    .clone();
    let error = Environment::new().declare_inductive(block).unwrap_err();
    assert_eq!(error.0, "incorrect recursor computation rule");

    let mut block = switch();
    block.recursors[0].rules.swap(0, 1);
    let error = Environment::new().declare_inductive(block).unwrap_err();
    assert_eq!(error.0, "incorrect recursor rule metadata");
}

#[test]
fn incorrect_constructor_metadata_is_rejected() {
    Environment::new().declare_inductive(switch()).unwrap();
    for field in ["owner", "index", "params", "fields", "universes"] {
        let mut block = switch();
        let constructor = &mut block.constructors[0];
        match field {
            "owner" => constructor.inductive = "Other".into(),
            "index" => constructor.index = 1,
            "params" => constructor.num_params = 1,
            "fields" => constructor.num_fields = 1,
            "universes" => constructor.params.push("u".into()),
            _ => unreachable!(),
        }
        let error = Environment::new().declare_inductive(block).unwrap_err();
        assert_eq!(
            error.0,
            if field == "fields" {
                "incorrect constructor field count"
            } else {
                "incorrect constructor metadata"
            }
        );
    }
}

#[test]
fn large_elimination_from_prop_is_rejected() {
    let mut block = switch();
    block.types[0].ty = expr("Prop");
    let error = Environment::new()
        .declare_inductive(block.clone())
        .unwrap_err();
    assert_eq!(error.0, "invalid large elimination from proposition");

    let levels = [("u".into(), Level::Nat(0))].into_iter().collect();
    let recursor = &mut block.recursors[0];
    recursor.params.clear();
    recursor.ty = recursor.ty.substitute_levels(&levels).unwrap();
    for rule in &mut recursor.rules {
        rule.rhs = rule.rhs.substitute_levels(&levels).unwrap();
    }
    Environment::new().declare_inductive(block).unwrap();
}

#[test]
fn rejected_inductive_blocks_roll_back() {
    for late_failure in [false, true] {
        let mut env = Environment::new();
        env.axiom("A", expr("Type")).unwrap();
        env.axiom("a", expr("A")).unwrap();
        let mut block = switch();
        if late_failure {
            block.recursors[0].rules[0].rhs = expr("Type");
        } else {
            block.constructors[0].num_fields = 1;
        }
        let error = env.declare_inductive(block).unwrap_err();
        assert!(
            error.0.contains(if late_failure {
                "type mismatch"
            } else {
                "incorrect constructor field count"
            }),
            "{error}"
        );
        for name in ["Switch", "left", "right"] {
            assert!(env.infer(&Expr::constant(name)).is_err());
        }
        assert!(
            env.infer(&Expr::Const("Switch.rec".into(), vec![Level::Nat(1)]))
                .is_err()
        );
        env.check(&expr("a"), &expr("A")).unwrap();
        env.declare_inductive(switch()).unwrap();
        env.check(&expr("left"), &expr("Switch")).unwrap();
        env.check(&expr("right"), &expr("Switch")).unwrap();
        let term = Expr::Const("Switch.rec".into(), vec![Level::Nat(1)])
            .app(expr("fun (s : Switch) => A"))
            .app(expr("a"))
            .app(expr("a"))
            .app(expr("left"));
        assert!(env.def_eq(&term, &expr("a")).unwrap());
    }
}
