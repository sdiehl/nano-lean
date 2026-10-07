use super::*;
use crate::import::import_bytes;

macro_rules! fixtures {
    ($($f:literal),*) => { [$((concat!($f), include_bytes!(concat!("../../tests/fixtures/", $f)).as_slice())),*] };
}

/// Every declaration of every fixture gets the same verdict from both engines.
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
        "smoke.ndjson",
        "theorem-reduction.ndjson",
        "valid-deep-sparse-scope.ndjson"
    );
    outcome::install_hook();
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
                !matches!(new, Err(outcome::Failure::Internal(_))),
                "{file}: {name}: {}",
                new.as_ref().err().map_or("", |f| f.reason())
            );
            let kind =
                |r: &Result<bool, outcome::Failure>| r.as_ref().map_err(|f| f.status()).copied();
            assert_eq!(kind(&old), kind(&new), "{file}: {name}");
            let shared = session.check(i, Limits::default(), Some(&mut c), true);
            assert_eq!(kind(&old), kind(&shared), "{file}: {name} in a session");
        }
    }
}
