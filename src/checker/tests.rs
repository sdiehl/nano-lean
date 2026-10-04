use super::*;
use crate::import::import_bytes;
use crate::term::outcome;
use std::io::Cursor;

const FOUNDATIONS: &[u8] = include_bytes!("../../tests/fixtures/foundations.ndjson");

fn check_all(bytes: &[u8]) -> Result<usize, String> {
    let arena = Bump::new();
    let store = import_bytes(&arena, bytes).map_err(|e| e.to_string())?;
    for index in 0..store.declars.len() {
        let local = Bump::new();
        outcome::run(|| Tc::new(&store, &local).check(index as u32))
            .map_err(|e| format!("{}: {}", store.declars[index].name(), e.reason()))?;
    }
    Ok(store.stats.declarations)
}

#[test]
fn foundational_signatures_and_theorems_agree_with_existing_kernel() {
    let count = check_all(FOUNDATIONS).unwrap();
    let legacy = nano_lean::export::check_export(Cursor::new(FOUNDATIONS)).unwrap();
    assert_eq!(count, legacy.declarations);
    let arena = Bump::new();
    let store = import_bytes(&arena, FOUNDATIONS).unwrap();
    for name in [
        "Nat", "Or", "Eq", "List", "Array", "Subtype", "Eq.symm", "congrArg",
    ] {
        assert!(
            store.declars.iter().any(|d| d.name().to_string() == name),
            "missing {name}"
        );
    }
}

#[test]
fn adjacent_and_mutual_blocks_keep_exact_boundaries() {
    for input in [
        include_bytes!("../../tests/fixtures/inductive-boundaries.ndjson").as_slice(),
        include_bytes!("../../tests/fixtures/mutual.ndjson").as_slice(),
    ] {
        assert_eq!(
            check_all(input).unwrap(),
            nano_lean::export::check_export(Cursor::new(input))
                .unwrap()
                .declarations
        );
        let arena = Bump::new();
        let store = import_bytes(&arena, input).unwrap();
        for (index, d) in store.declars.iter().enumerate() {
            if let Some(block) = store.blocks.get(&d.name()) {
                assert!((block.start..block.end).contains(&(index as u32)));
                assert!(block.start < block.types_end);
                assert!(block.types_end <= block.ctors_end && block.ctors_end <= block.end);
            }
        }
    }
}

fn forward_reference(self_reference: bool) -> Vec<u8> {
    let mut lines = vec![
        serde_json::json!({"meta":{"format":{"version":"3.1.0"}}}),
        serde_json::json!({"in":1,"str":{"pre":0,"str":"A"}}),
        serde_json::json!({"in":2,"str":{"pre":0,"str":"a"}}),
        serde_json::json!({"in":3,"str":{"pre":0,"str":"f"}}),
        serde_json::json!({"in":4,"str":{"pre":0,"str":"g"}}),
        serde_json::json!({"il":1,"succ":0}),
        serde_json::json!({"ie":0,"sort":1}),
        serde_json::json!({"ie":1,"const":{"name":1,"us":[]}}),
        serde_json::json!({"ie":2,"const":{"name":2,"us":[]}}),
        serde_json::json!({"ie":3,"const":{"name":3,"us":[]}}),
        serde_json::json!({"ie":4,"const":{"name":4,"us":[]}}),
        serde_json::json!({"axiom":{"name":1,"levelParams":[],"type":0,"isUnsafe":false}}),
        serde_json::json!({"axiom":{"name":2,"levelParams":[],"type":1,"isUnsafe":false}}),
    ];
    lines.push(serde_json::json!({"def":{"name":3,"levelParams":[],"type":1,"value":if self_reference {3} else {4},"all":[3,4],"hints":{"regular":1},"safety":"safe"}}));
    lines.push(serde_json::json!({"def":{"name":4,"levelParams":[],"type":1,"value":2,"all":[3,4],"hints":{"regular":1},"safety":"safe"}}));
    lines
        .into_iter()
        .map(|x| format!("{x}\n"))
        .collect::<String>()
        .into_bytes()
}

#[test]
fn export_groups_never_authorize_self_or_forward_references() {
    for self_reference in [true, false] {
        let input = forward_reference(self_reference);
        assert!(check_all(&input).unwrap_err().contains("unknown constant"));
        assert!(nano_lean::export::check_export(Cursor::new(input)).is_err());
    }
}

#[test]
fn a_reused_checker_cannot_reuse_types_from_a_later_scope() {
    let input = forward_reference(false);
    let arena = Bump::new();
    let store = import_bytes(&arena, &input).unwrap();
    let local = Bump::new();
    let mut tc = Tc::new(&store, &local);
    tc.limit = store.declars.len() as u32;
    let levels = tc.empty_levels();
    let g = tc.ctx.konst(store.declars[3].name(), levels);
    tc.infer(g, false);
    let failure = outcome::run(|| tc.check(2))
        .err()
        .expect("forward reference accepted");
    assert!(failure.reason().contains("unknown constant"));
}

#[test]
fn proposition_detection_compares_universes_semantically() {
    let arena = Bump::new();
    let store = import_bytes(&arena, FOUNDATIONS).unwrap();
    let local = Bump::new();
    let mut tc = Tc::new(&store, &local);
    let name = tc.ctx.str1("u");
    let u = tc.ctx.param(name);
    tc.uparams = tc.ctx.levels(&[u]);
    let zero = tc.ctx.zero();
    let imax = tc.ctx.imax(u, zero);
    let sort = tc.ctx.sort(imax);
    let proposition = tc.fresh_local(sort);
    assert!(tc.is_prop(proposition));
    let sort = tc.ctx.sort(u);
    let unknown = tc.fresh_local(sort);
    assert!(!tc.is_prop(unknown));
    let one = tc.ctx.succ(zero);
    let sort = tc.ctx.sort(one);
    let data = tc.fresh_local(sort);
    assert!(!tc.is_prop(data));
}

#[test]
fn malformed_foundation_theorem_is_rejected_by_both_checkers() {
    let mut lines: Vec<serde_json::Value> = std::str::from_utf8(FOUNDATIONS)
        .unwrap()
        .lines()
        .map(|s| serde_json::from_str(s).unwrap())
        .collect();
    let sort_id = lines.iter().find(|v| v.get("sort").is_some()).unwrap()["ie"].clone();
    let theorem = lines.iter_mut().find(|v| v.get("thm").is_some()).unwrap();
    theorem["thm"]["type"] = sort_id;
    let input = lines.iter().map(|v| format!("{v}\n")).collect::<String>();
    assert!(check_all(input.as_bytes()).is_err());
    assert!(nano_lean::export::check_export(Cursor::new(input)).is_err());
}
