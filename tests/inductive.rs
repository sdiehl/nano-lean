#![allow(clippy::unwrap_used, clippy::panic)]

use nano_lean::{
    Environment, Expr, Level,
    kernel::{Constructor, InductiveBlock, InductiveType, Recursor, RecursorRule},
    parser::parse_expr,
};
use unbound::{Alpha, Shared};

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
    Environment::new().declare_inductive(&switch()).unwrap();
    for ty in [
        "(Switch -> Switch) -> Switch",
        "((Switch -> Switch) -> Switch) -> Switch",
    ] {
        let mut block = switch();
        block.constructors[0].ty = expr(ty);
        block.constructors[0].num_fields = 1;
        let error = Environment::new().declare_inductive(&block).unwrap_err();
        assert_eq!(error.to_string(), "negative inductive occurrence");
    }
}

#[test]
fn forged_recursor_rules_are_rejected() {
    Environment::new().declare_inductive(&switch()).unwrap();
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
    let error = Environment::new().declare_inductive(&block).unwrap_err();
    assert_eq!(error.to_string(), "incorrect recursor computation rule");

    let mut block = switch();
    block.recursors[0].rules.swap(0, 1);
    let error = Environment::new().declare_inductive(&block).unwrap_err();
    assert_eq!(error.to_string(), "incorrect recursor rule metadata");
}

#[test]
fn incorrect_constructor_metadata_is_rejected() {
    Environment::new().declare_inductive(&switch()).unwrap();
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
        let error = Environment::new().declare_inductive(&block).unwrap_err();
        assert_eq!(
            error.to_string(),
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
        .declare_inductive(&block.clone())
        .unwrap_err();
    assert_eq!(
        error.to_string(),
        "invalid large elimination from proposition"
    );

    let levels = [("u".into(), Level::Nat(0))].into_iter().collect();
    let recursor = &mut block.recursors[0];
    recursor.params.clear();
    recursor.ty = recursor.ty.substitute_levels(&levels).unwrap();
    for rule in &mut recursor.rules {
        rule.rhs = rule.rhs.substitute_levels(&levels).unwrap();
    }
    Environment::new().declare_inductive(&block).unwrap();
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
        let error = env.declare_inductive(&block).unwrap_err();
        assert!(
            error.to_string().contains(if late_failure {
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
        env.declare_inductive(&switch()).unwrap();
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

fn pack(prop: bool, proof_field: bool) -> Environment {
    let mut env = Environment::new();
    env.axiom("A", expr("Type")).unwrap();
    env.axiom(
        "B",
        expr(if proof_field {
            "A -> Prop"
        } else {
            "A -> Type"
        }),
    )
    .unwrap();
    env.axiom("a", expr("A")).unwrap();
    env.axiom("b", expr("B a")).unwrap();
    let rec_expr = |source: &str| {
        if prop {
            expr(&source.replace('U', "Prop"))
        } else {
            poly(source)
        }
    };
    env.declare_inductive(&InductiveBlock {
        types: vec![InductiveType {
            name: "Pack".into(),
            params: vec![],
            ty: expr(if prop { "Prop" } else { "Type" }),
            all: vec!["Pack".into()],
            constructors: vec!["mk".into()],
            num_params: 0,
            num_indices: 0,
            num_nested: 0,
            recursive: false,
            reflexive: false,
        }],
        constructors: vec![Constructor {
            name: "mk".into(),
            params: vec![],
            ty: expr("forall (a : A), B a -> Pack"),
            inductive: "Pack".into(),
            index: 0,
            num_params: 0,
            num_fields: 2,
        }],
        recursors: vec![Recursor {
            name: "Pack.rec".into(),
            params: if prop { vec![] } else { vec!["u".into()] },
            ty: rec_expr("forall (m : Pack -> U), (forall (a : A) (b : B a), m (mk a b)) -> forall (p : Pack), m p"),
            all: vec!["Pack".into()],
            num_params: 0,
            num_indices: 0,
            num_motives: 1,
            num_minors: 1,
            k: false,
            rules: vec![RecursorRule {
                constructor: "mk".into(),
                num_fields: 2,
                rhs: rec_expr("fun (m : Pack -> U) (f : forall (a : A) (b : B a), m (mk a b)) (a : A) (b : B a) => f a b"),
            }],
        }],
    }).unwrap();
    env.axiom("p", expr("Pack")).unwrap();
    env.axiom("q", expr("Pack")).unwrap();
    env
}

fn project(index: usize, value: Expr) -> Expr {
    Expr::Proj("Pack".into(), index, Shared::new(value))
}

#[test]
fn dependent_projection_type_inference() {
    let env = pack(false, false);
    let first = project(0, expr("p"));
    let second = project(1, expr("p"));
    assert!(env.infer(&first).unwrap().aeq(&expr("A")));
    let expected = expr("B").app(first);
    assert!(env.infer(&second).unwrap().aeq(&expected));
    env.check(&second, &expected).unwrap();
    assert!(env.check(&second, &expr("B a")).is_err());
    for (index, expected) in [(0, "a"), (1, "b")] {
        assert!(
            env.def_eq(&project(index, expr("mk a b")), &expr(expected))
                .unwrap()
        );
    }
    assert_eq!(
        env.infer(&project(2, expr("p"))).unwrap_err().to_string(),
        "projection field out of range"
    );
}

#[test]
fn data_projections_from_prop_are_rejected() {
    for proof_field in [false, true] {
        let env = pack(true, proof_field);
        for value in ["p", "mk a b"] {
            for index in [0, 1] {
                let error = env.infer(&project(index, expr(value))).unwrap_err();
                assert_eq!(
                    error.to_string(),
                    "projection eliminates proposition into data"
                );
            }
        }
    }
    let env = pack(false, true);
    env.infer(&project(1, expr("p"))).unwrap();
}

#[test]
fn structure_eta_on_neutral_terms() {
    let env = pack(false, false);
    let neutral = expr("p");
    let expanded = expr("mk")
        .app(project(0, neutral.clone()))
        .app(project(1, neutral.clone()));
    env.check(&expanded, &expr("Pack")).unwrap();
    assert!(env.def_eq(&neutral, &expanded).unwrap());
    assert!(env.def_eq(&expanded, &neutral).unwrap());
    assert!(!env.def_eq(&expr("q"), &expanded).unwrap());
    assert!(!env.def_eq(&neutral, &expr("mk a b")).unwrap());
}

fn indexed(prop: bool) -> Environment {
    let mut env = Environment::new();
    env.axiom("A", expr("Type")).unwrap();
    env.axiom("a", expr("A")).unwrap();
    env.axiom("b", expr("A")).unwrap();
    env.declare_inductive(&InductiveBlock {
        types: vec![InductiveType {
            name: "Indexed".into(),
            params: vec![],
            ty: expr(if prop { "A -> Prop" } else { "A -> Type" }),
            all: vec!["Indexed".into()],
            constructors: vec!["tag".into()],
            num_params: 0,
            num_indices: 1,
            num_nested: 0,
            recursive: false,
            reflexive: false,
        }],
        constructors: vec![Constructor {
            name: "tag".into(),
            params: vec![],
            ty: expr("Indexed a"),
            inductive: "Indexed".into(),
            index: 0,
            num_params: 0,
            num_fields: 0,
        }],
        recursors: vec![Recursor {
            name: "Indexed.rec".into(),
            params: vec!["u".into()],
            ty: poly("forall (m : forall (i : A), Indexed i -> U), m a tag -> forall (i : A) (h : Indexed i), m i h"),
            all: vec!["Indexed".into()],
            num_params: 0,
            num_indices: 1,
            num_motives: 1,
            num_minors: 1,
            k: prop,
            rules: vec![RecursorRule {
                constructor: "tag".into(),
                num_fields: 0,
                rhs: poly("fun (m : forall (i : A), Indexed i -> U) (base : m a tag) => base"),
            }],
        }],
    }).unwrap();
    env.axiom("p", expr("Indexed a")).unwrap();
    env.axiom("q", expr("Indexed b")).unwrap();
    env
}

fn indexed_call(index: &str, major: &str) -> Expr {
    Expr::Const("Indexed.rec".into(), vec![Level::Nat(1)])
        .app(expr("fun (i : A) (h : Indexed i) => A -> A"))
        .app(expr("fun (x : A) => x"))
        .app(expr(index))
        .app(expr(major))
        .app(expr("b"))
}

#[test]
fn indexed_recursor_computation() {
    let env = indexed(false);
    let term = indexed_call("a", "tag");
    env.check(&term, &expr("A")).unwrap();
    assert!(env.normalize(&term).unwrap().aeq(&expr("b")));
    assert!(env.infer(&indexed_call("b", "tag")).is_err());
    let neutral = indexed_call("a", "p");
    assert!(env.normalize(&neutral).unwrap().aeq(&neutral));
    assert!(!env.def_eq(&neutral, &expr("b")).unwrap());
}

#[test]
fn proof_recursor_k_reduction() {
    let mut env = indexed(true);
    for major in ["tag", "p"] {
        let term = indexed_call("a", major);
        env.check(&term, &expr("A")).unwrap();
        assert!(env.normalize(&term).unwrap().aeq(&expr("b")));
    }
    env.define("alias", expr("A"), expr("a")).unwrap();
    assert!(
        env.normalize(&indexed_call("alias", "p"))
            .unwrap()
            .aeq(&expr("b"))
    );
    let neutral = indexed_call("b", "q");
    assert!(env.normalize(&neutral).unwrap().aeq(&neutral));
    assert!(!env.def_eq(&neutral, &expr("b")).unwrap());
}

#[test]
fn higher_order_recursive_field_reduction() {
    let mut block = switch();
    block.types[0].name = "Tree".into();
    block.types[0].all = vec!["Tree".into()];
    block.types[0].constructors = vec!["leaf".into(), "branch".into()];
    block.types[0].recursive = true;
    block.types[0].reflexive = true;
    block.constructors[0].name = "leaf".into();
    block.constructors[0].inductive = "Tree".into();
    block.constructors[0].ty = expr("Tree");
    block.constructors[1].name = "branch".into();
    block.constructors[1].inductive = "Tree".into();
    block.constructors[1].ty = expr("(A -> Tree) -> Tree");
    block.constructors[1].num_fields = 1;
    let r = &mut block.recursors[0];
    r.name = "Tree.rec".into();
    r.all = vec!["Tree".into()];
    r.ty = poly(
        "forall (m : Tree -> U), m leaf -> (forall (f : A -> Tree), (forall (a : A), m (f a)) -> m (branch f)) -> forall (t : Tree), m t",
    );
    r.rules[0].constructor = "leaf".into();
    r.rules[0].rhs = poly(
        "fun (m : Tree -> U) (l : m leaf) (b : forall (f : A -> Tree), (forall (a : A), m (f a)) -> m (branch f)) => l",
    );
    r.rules[1].constructor = "branch".into();
    r.rules[1].num_fields = 1;
    let Expr::Lam(_, body) = poly(
        "fun (rec : Type) (m : Tree -> U) (l : m leaf) (b : forall (f : A -> Tree), (forall (a : A), m (f a)) -> m (branch f)) (f : A -> Tree) => b f (fun (a : A) => rec m l b (f a))",
    ) else {
        unreachable!()
    };
    r.rules[1].rhs = (*body.instantiate(&Expr::Const(
        "Tree.rec".into(),
        vec![Level::Param("u".into())],
    )))
    .clone();
    let mut env = Environment::new();
    env.axiom("A", expr("Type")).unwrap();
    env.axiom("a", expr("A")).unwrap();
    env.declare_inductive(&block).unwrap();
    let rec = Expr::Const("Tree.rec".into(), vec![Level::Nat(1)]);
    let prefix = rec
        .app(expr("fun (t : Tree) => A"))
        .app(expr("a"))
        .app(expr("fun (f : A -> Tree) (ih : A -> A) => ih a"));
    let tree = expr("branch (fun (x : A) => branch (fun (y : A) => leaf))");
    assert!(
        env.normalize(&prefix.clone().app(tree))
            .unwrap()
            .aeq(&expr("a"))
    );
    env.axiom("f", expr("A -> Tree")).unwrap();
    let reduced = env
        .normalize(&prefix.clone().app(expr("branch f")))
        .unwrap();
    assert!(env.def_eq(&reduced, &prefix.app(expr("f a"))).unwrap());
}
