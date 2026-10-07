use super::*;
#[test]
fn values_and_frames_share_only_identical_captures() {
    let env = Environment::new();
    let mut tc = Checker::new(&env);
    let mut ev = Evaluator::new(&mut tc);
    let a = ev.term(Expr::Sort(Level::Nat(0)), None);
    let b = ev.term(Expr::Sort(Level::Nat(1)), None);
    let fa = ev.frame(a.clone(), None);
    assert!(Rc::ptr_eq(&fa, &ev.frame(a.clone(), None)));
    let fb = ev.frame(b, None);
    let head = Expr::Lam(
        Shared::new(Expr::Sort(Level::Nat(1))),
        bind(Name::new("x"), Shared::new(Expr::Var(Name::bound(1, 0)))),
    );
    let va = ev.value(head.clone(), Some(fa.clone()), vec![]);
    let same = ev.value(head.clone(), Some(fa), vec![]);
    let different = ev.value(head, Some(fb), vec![]);
    assert!(Rc::ptr_eq(&va, &same));
    assert!(!Rc::ptr_eq(&va, &different));
    let proof = ev.value(Expr::Var(Name::new("h")), None, vec![]);
    let other = ev.value(Expr::Var(Name::new("h")), None, vec![]);
    assert!(!Rc::ptr_eq(&proof, &other));
    let weak = Rc::downgrade(&va);
    drop(va);
    drop(same);
    assert!(weak.upgrade().is_none());
}
#[test]
fn shared_normal_values_drop_on_a_small_stack() {
    std::thread::Builder::new()
        .stack_size(256 * 1024)
        .spawn(|| {
            let env = Environment::new();
            let mut tc = Checker::new(&env);
            let mut ev = Evaluator::new(&mut tc);
            let mut term = ev.term(Expr::Sort(Level::Nat(0)), None);
            let expr = term.expr.clone();
            for id in 1..30_000 {
                let value = ev.value(Expr::Sort(Level::Nat(0)), None, vec![term]);
                term = Rc::new(Term {
                    id,
                    expr: expr.clone(),
                    context: None,
                    normal: [OnceCell::new(), OnceCell::from(value)],
                    canonical: OnceCell::new(),
                });
            }
            assert!(ev.state.values.len() <= 16_384);
            drop(term);
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn reused_evaluation_does_not_export_local_proofs() {
    let mut env = Environment::new();
    crate::parser::run("axiom P : Prop; axiom p : P", &mut env).unwrap();
    let mut checker = Checker::new(&env);
    let p = Expr::constant("P");
    let x = Name::new("x");
    let identity = Expr::lam(x.clone(), p.clone(), Expr::Var(x));
    let closed = identity.clone().app(Expr::constant("p"));
    let h = Name::new("h");
    checker
        .local(h.clone(), p.clone(), |tc| {
            let first = identity.clone().app(Expr::Var(h.clone()));
            assert!(tc.whnf(&first)?.aeq(&Expr::Var(h)));
            assert!(tc.whnf(&closed)?.aeq(&Expr::constant("p")));
            Ok(())
        })
        .unwrap();
    let result = checker.whnf(&closed).unwrap();
    assert!(checker.infer(&result).unwrap().aeq(&p));
}

#[test]
fn reused_evaluation_preserves_unfolding_modes() {
    let mut env = Environment::new();
    crate::parser::run("axiom A : Type; axiom a : A; def d : A := a", &mut env).unwrap();
    let mut checker = Checker::new(&env);
    let d = Expr::constant("d");
    assert!(checker.whnf_mode(&d, false).unwrap().aeq(&d));
    assert!(checker.whnf(&d).unwrap().aeq(&Expr::constant("a")));
    assert!(checker.whnf_mode(&d, false).unwrap().aeq(&d));
}

#[test]
fn quote_reuses_a_forced_numeric_result() {
    let env = Environment::new();
    let mut checker = Checker::new(&env);
    let mut evaluator = Evaluator::new(&mut checker);
    let predecessor = evaluator.term(Expr::nat(604_799_999u64), None);
    let frame = evaluator.frame(predecessor, None);
    let suspended = evaluator.term(
        Expr::Const("Nat.succ".into(), vec![]).app(Expr::Var(Name::bound(0, 0))),
        Some(frame),
    );
    assert!(
        suspended.normal[1]
            .set(evaluator.value(Expr::nat(604_800_000u64), None, vec![]))
            .is_ok()
    );
    assert!(matches!(evaluator.quote(&suspended, 0),
        Expr::Nat(n) if n.0 == 604_800_000u64.into()));
}

#[test]
fn quote_deep_closure_chain_uses_bounded_stack() {
    std::thread::Builder::new()
        .stack_size(256 * 1024)
        .spawn(|| {
            let env = Environment::new();
            let mut checker = Checker::new(&env);
            let mut evaluator = Evaluator::new(&mut checker);
            let mut term = evaluator.term(Expr::Sort(Level::Nat(0)), None);
            let var = Shared::new(Expr::Var(Name::bound(0, 0)));
            for id in 1..100_000 {
                term = Rc::new(Term {
                    id,
                    expr: var.clone(),
                    context: Some(Rc::new(Frame {
                        id,
                        value: Some(term),
                        parent: None,
                    })),
                    normal: [OnceCell::new(), OnceCell::new()],
                    canonical: OnceCell::new(),
                });
            }
            assert!(matches!(
                evaluator.quote(&term, 0),
                Expr::Sort(Level::Nat(0))
            ));
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn deep_closure_graph_cleanup_uses_bounded_stack() {
    std::thread::Builder::new()
        .stack_size(256 * 1024)
        .spawn(|| {
            let expr = Shared::new(Expr::Sort(Level::Nat(0)));
            let mut context = None;
            for id in 0..100_000 {
                let term = Rc::new(Term {
                    id,
                    expr: expr.clone(),
                    context: context.clone(),
                    normal: [OnceCell::new(), OnceCell::new()],
                    canonical: OnceCell::new(),
                });
                context = Some(Rc::new(Frame {
                    id,
                    value: Some(term),
                    parent: context,
                }));
            }
            drop(context);
        })
        .unwrap()
        .join()
        .unwrap();
}
