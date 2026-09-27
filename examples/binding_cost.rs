use std::{
    collections::HashSet,
    hint::black_box,
    rc::Rc,
    sync::atomic::{AtomicUsize, Ordering},
    time::Instant,
};
use unbound::{Alpha, Bind, Name, Subst};

static CLONES: AtomicUsize = AtomicUsize::new(0);

#[derive(Debug, Alpha, Subst)]
enum Term {
    Var(Name<Term>),
    Global(String),
    App(Rc<Term>, Rc<Term>),
}

impl Clone for Term {
    fn clone(&self) -> Self {
        CLONES.fetch_add(1, Ordering::Relaxed);
        match self {
            Self::Var(n) => Self::Var(n.clone()),
            Self::Global(n) => Self::Global(n.clone()),
            Self::App(f, a) => Self::App(f.clone(), a.clone()),
        }
    }
}

fn dag(depth: u32) -> Rc<Term> {
    let f = Rc::new(Term::Global("f".into()));
    let mut t = Rc::new(Term::Global("a".into()));
    for _ in 0..depth {
        t = Rc::new(Term::App(Rc::new(Term::App(f.clone(), t.clone())), t));
    }
    t
}

fn nodes(root: &Rc<Term>) -> usize {
    let mut seen = HashSet::new();
    let mut pending = vec![root];
    while let Some(term) = pending.pop() {
        if seen.insert(Rc::as_ptr(term))
            && let Term::App(f, a) = term.as_ref()
        {
            pending.extend([f, a]);
        }
    }
    seen.len()
}

fn measure<T>(
    depth: u32,
    operation: &str,
    f: impl FnOnce() -> T,
    root: impl Fn(&T) -> &Rc<Term>,
) -> T {
    CLONES.store(0, Ordering::Relaxed);
    let start = Instant::now();
    let result = black_box(f());
    let elapsed = start.elapsed().as_secs_f64() * 1000.0;
    let clones = CLONES.load(Ordering::Relaxed);
    println!(
        "{depth},{},{operation},{clones},{},{elapsed:.3}",
        2 * depth + 2,
        nodes(root(&result))
    );
    result
}

fn main() {
    println!("depth,dag_nodes,operation,node_clones,result_nodes,milliseconds");
    for depth in [8, 12, 16, 18] {
        let body = dag(depth);
        assert_eq!(nodes(&body), (2 * depth + 2) as usize);
        let name = Name::new("unused");
        let binder = measure(
            depth,
            "bind",
            || Bind::new(name.clone(), body.clone()),
            |b| b.body(),
        );
        let opened = measure(depth, "unbind", || binder.unbind_ref(), |b| &b.1);
        let replaced = measure(
            depth,
            "subst_absent",
            || body.subst(&name, &Term::Global("b".into())),
            |b| b,
        );
        let instantiated = measure(
            depth,
            "instantiate",
            || binder.instantiate(&Term::Global("b".into())),
            |b| b,
        );
        assert!(body.aeq(&opened.1));
        assert!(body.aeq(&replaced));
        assert!(body.aeq(&instantiated));
    }
}
