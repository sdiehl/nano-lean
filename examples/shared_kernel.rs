use nano_lean::{Environment, Expr, Level};
use std::time::Instant;
use unbound::{Name, Shared};

fn main() {
    let mut env = Environment::new();
    env.axiom("A", Expr::Sort(Level::Nat(1))).unwrap();
    env.axiom("a", Expr::constant("A")).unwrap();
    env.axiom(
        "f",
        Expr::pi(
            Name::new("x"),
            Expr::constant("A"),
            Expr::pi(Name::new("y"), Expr::constant("A"), Expr::constant("A")),
        ),
    )
    .unwrap();
    println!("depth,dag_nodes,status,milliseconds");
    for depth in [8, 12, 18, 30, 60] {
        let f = Shared::new(Expr::constant("f"));
        let mut term = Shared::new(Expr::constant("a"));
        for _ in 0..depth {
            term = Shared::new(Expr::App(
                Shared::new(Expr::App(f.clone(), term.clone())),
                term,
            ));
        }
        let start = Instant::now();
        let result = env.check(&term, &Expr::constant("A"));
        println!(
            "{depth},{},{},{:.3}",
            2 * depth + 2,
            if result.is_ok() { "checked" } else { "failed" },
            start.elapsed().as_secs_f64() * 1e3
        );
        if let Err(e) = result {
            eprintln!("{e}");
        }
    }
}
