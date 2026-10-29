use super::*;
use crate::checker::{self, Adapter};
use crate::import::import_bytes;
use crate::resource::Budget;
use crate::term::outcome::{Decline, Failure};
use std::fmt::Write;

macro_rules! fixtures {
    ($($f:literal),*) => { [$((concat!($f), include_bytes!(concat!("../../tests/fixtures/", $f)).as_slice())),*] };
}

#[test]
fn fixture_outcomes_match_the_term_checker() {
    let all = fixtures!(
        "frame-missing-binder-63.ndjson",
        "frame-missing-binder-64.ndjson",
        "frame-missing-binder-65.ndjson",
        "frame-missing-binder-70.ndjson",
        "frame-valid-63.ndjson",
        "frame-valid-64.ndjson",
        "frame-valid-65.ndjson",
        "frame-valid-70.ndjson",
        "frame-wrong-value-63.ndjson",
        "frame-wrong-value-64.ndjson",
        "frame-wrong-value-65.ndjson",
        "frame-wrong-value-70.ndjson",
        "foundations.ndjson",
        "inductive-boundaries.ndjson",
        "invalid-loose-bvar.ndjson",
        "invalid-loose-bvar-under-binder.ndjson",
        "invalid-nested-parameter.ndjson",
        "mutual.ndjson",
        "nested-minimal.ndjson",
        "nested.ndjson",
        "neutral.ndjson",
        "ordinary.ndjson",
        "primitives.ndjson",
        "projection-prop.ndjson",
        "reduction.ndjson",
        "session-universe-scope.ndjson",
        "session-universe-subset.ndjson",
        "smoke.ndjson",
        "theorem-reduction.ndjson",
        "valid-deep-sparse-scope.ndjson"
    );
    for (file, bytes) in all {
        let arena = Arena::new();
        let store = import_bytes(&arena, bytes).unwrap();
        let mut a = Adapter::new(&store);
        let mut b = Adapter::new(&store);
        let mut c = Adapter::new(&store);
        let mut session = Session::new(&store);
        for i in 0..store.declars.len() as u32 {
            let mut local = Arena::new();
            let old = checker::check_with_adapter(
                &store,
                &mut local,
                i,
                Limits::default(),
                Some(&mut a),
                true,
            );
            local.reset();
            let new = check(&store, &mut local, i, Limits::default(), Some(&mut b), true);
            let name = store.declars[i as usize].name();
            assert!(
                !matches!(new, Err(Failure::Internal(_))),
                "{file}: {name}: {}",
                new.as_ref().err().map_or("", |f| f.reason())
            );
            let kind = |r: &Result<bool, Failure>| {
                r.as_ref()
                    .map_err(super::super::term::outcome::Failure::status)
                    .copied()
            };
            assert_eq!(kind(&old), kind(&new), "{file}: {name}");
            let shared = session.check(i, Limits::default(), Some(&mut c), true);
            assert_eq!(kind(&old), kind(&shared), "{file}: {name} in a session");
        }
    }
}

#[test]
fn nat_let_value_is_not_folded_in_its_body() {
    let bytes = include_bytes!("../../tests/fixtures/let/nat-let-fold.ndjson");
    let arena = Arena::new();
    let store = import_bytes(&arena, bytes).unwrap();
    let mut a = Adapter::new(&store);
    let mut b = Adapter::new(&store);
    for i in 0..store.declars.len() as u32 {
        let mut local = Arena::new();
        let name = store.declars[i as usize].name();
        let term = checker::check_with_adapter(
            &store,
            &mut local,
            i,
            Limits::default(),
            Some(&mut a),
            true,
        );
        assert!(term.is_ok(), "term core: {name}");
        local.reset();
        let value = check(&store, &mut local, i, Limits::default(), Some(&mut b), true);
        assert!(value.is_ok(), "value core: {name}");
    }
}

#[test]
fn deep_term_declines_instead_of_overflowing() {
    const DEPTH: usize = 200_000;
    let mut s = String::from(concat!(
        "{\"meta\":{\"format\":{\"version\":\"3.1.0\"}}}\n",
        "{\"in\":1,\"str\":{\"pre\":0,\"str\":\"A\"}}\n",
        "{\"in\":2,\"str\":{\"pre\":0,\"str\":\"a\"}}\n",
        "{\"in\":3,\"str\":{\"pre\":0,\"str\":\"f\"}}\n",
        "{\"in\":4,\"str\":{\"pre\":0,\"str\":\"d\"}}\n",
        "{\"il\":1,\"succ\":0}\n",
        "{\"ie\":0,\"sort\":1}\n",
        "{\"axiom\":{\"name\":1,\"levelParams\":[],\"type\":0,\"isUnsafe\":false}}\n",
        "{\"const\":{\"name\":1,\"us\":[]},\"ie\":1}\n",
        "{\"axiom\":{\"name\":2,\"levelParams\":[],\"type\":1,\"isUnsafe\":false}}\n",
        "{\"forallE\":{\"binderInfo\":\"default\",\"body\":1,\"name\":2,\"type\":1},\"ie\":2}\n",
        "{\"axiom\":{\"name\":3,\"levelParams\":[],\"type\":2,\"isUnsafe\":false}}\n",
        "{\"const\":{\"name\":2,\"us\":[]},\"ie\":3}\n",
        "{\"const\":{\"name\":3,\"us\":[]},\"ie\":4}\n",
    ));
    for i in 0..DEPTH {
        writeln!(
            s,
            "{{\"app\":{{\"arg\":{},\"fn\":4}},\"ie\":{}}}",
            3 + i,
            5 + i
        )
        .unwrap();
    }
    writeln!(
        s,
        "{{\"def\":{{\"all\":[4],\"hints\":{{\"regular\":1}},\"levelParams\":[],\"name\":4,\"safety\":\"safe\",\"type\":1,\"value\":{}}}}}",
        4 + DEPTH
    )
    .unwrap();
    std::thread::Builder::new()
        .stack_size(4 << 20)
        .spawn(move || {
            let arena = Arena::new();
            let store = import_bytes(&arena, s.as_bytes()).unwrap();
            let mut local = Arena::new();
            let r = check(&store, &mut local, 3, Limits::default(), None, true);
            let reason = r.as_ref().err().map_or("accepted", Failure::reason);
            assert!(
                matches!(r, Err(Failure::Declined(Decline::Exhausted(Budget::Stack)))),
                "{reason}"
            );
        })
        .unwrap()
        .join()
        .unwrap();
}
