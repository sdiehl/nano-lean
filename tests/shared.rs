use nano_lean::{Environment, Expr, Level};
use unbound::{Name, Shared, bind};

fn arrow(a: Expr, b: Expr) -> Expr {
    Expr::pi(Name::new("_"), a, b)
}

#[test]
fn exponentially_large_tree_checks_as_a_small_graph() {
    let mut env = Environment::new();
    let a = Expr::constant("A");
    env.axiom("A", Expr::Sort(Level::Nat(1))).unwrap();
    env.axiom("a", a.clone()).unwrap();
    env.axiom("f", arrow(a.clone(), arrow(a.clone(), a.clone())))
        .unwrap();
    let f = Shared::new(Expr::constant("f"));
    let mut term = Shared::new(Expr::constant("a"));
    for _ in 0..60 {
        term = Shared::new(Expr::App(
            Shared::new(Expr::App(f.clone(), term.clone())),
            term,
        ));
    }
    env.check(&term, &a).unwrap();
    let invalid = Expr::App(f, Shared::new(Expr::Sort(Level::Nat(0))));
    assert!(env.infer(&invalid).is_err());
}

#[test]
fn shared_closed_body_can_occur_in_different_local_contexts() {
    let mut env = Environment::new();
    let a = Expr::constant("A");
    let b = Expr::constant("B");
    env.axiom("A", Expr::Sort(Level::Nat(1))).unwrap();
    env.axiom("B", Expr::Sort(Level::Nat(1))).unwrap();
    env.axiom(
        "f",
        arrow(
            arrow(a.clone(), a.clone()),
            arrow(arrow(b.clone(), b.clone()), a.clone()),
        ),
    )
    .unwrap();
    let body = Shared::new(Expr::Var(Name::bound(0, 0)));
    let left = Expr::Lam(Shared::new(a.clone()), bind(Name::new("x"), body.clone()));
    let right = Expr::Lam(Shared::new(b), bind(Name::new("y"), body));
    env.check(&Expr::constant("f").app(left).app(right), &a)
        .unwrap();
}

#[test]
fn enormous_unbound_index_is_rejected_without_allocating_its_range() {
    let env = Environment::new();
    assert!(env.infer(&Expr::Var(Name::bound(usize::MAX, 0))).is_err());
}
