use super::*;
use crate::import::import_bytes;
use crate::term::outcome;
use std::io::Cursor;

const FOUNDATIONS: &[u8] = include_bytes!("../../tests/fixtures/foundations.ndjson");

fn check_all(bytes: &[u8]) -> Result<usize, String> {
    let arena = Arena::new();
    let store = import_bytes(&arena, bytes).map_err(|e| e.to_string())?;
    for index in 0..store.declars.len() {
        let mut local = Arena::new();
        check_declaration(&store, &mut local, index as u32, Limits::default())
            .map_err(|e| format!("{}: {}", store.declars[index].name(), e.reason()))?;
    }
    Ok(store.stats.declarations)
}

#[test]
fn foundational_signatures_and_theorems_agree_with_existing_kernel() {
    let count = check_all(FOUNDATIONS).unwrap();
    let legacy = nano_lean::export::check_export(Cursor::new(FOUNDATIONS)).unwrap();
    assert_eq!(count, legacy.declarations);
    let arena = Arena::new();
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
        let arena = Arena::new();
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
    let arena = Arena::new();
    let store = import_bytes(&arena, &input).unwrap();
    let local = Arena::new();
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
    let arena = Arena::new();
    let store = import_bytes(&arena, FOUNDATIONS).unwrap();
    let local = Arena::new();
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

const REDUCTION: &[u8] = include_bytes!("../../tests/fixtures/reduction.ndjson");

#[test]
fn failed_and_exhausted_congruence_probes_fall_back_to_unfolding() {
    assert_eq!(
        check_all(REDUCTION).unwrap(),
        nano_lean::export::check_export(Cursor::new(REDUCTION))
            .unwrap()
            .declarations
    );
    let arena = Arena::new();
    let store = import_bytes(&arena, REDUCTION).unwrap();
    let local = Arena::new();
    let mut tc = Tc::new(&store, &local);
    tc.limit = store.declars.len() as u32;
    let body = |name| {
        store
            .declars
            .iter()
            .find_map(|d| match *d {
                Declar::Def(info, value, _) if info.name.to_string() == name => Some(value),
                _ => None,
            })
            .unwrap()
    };
    assert!(tc.def_eq(body("PhaseTwo.erasedCostly"), body("PhaseTwo.erasedOne")));
    assert!(tc.probe_remaining.is_none());
    assert!(tc.probe_exhaustions > 0);
    let one = tc.ctx.nat_lit(1u32.into());
    let two = tc.ctx.nat_lit(2u32.into());
    assert!(!tc.def_eq(one, two));
    assert!(local.allocated_bytes() < 2 << 20);
}

#[test]
fn projections_expose_operations_before_expensive_natural_reduction() {
    let arena = Arena::new();
    let store = import_bytes(&arena, REDUCTION).unwrap();
    let local = Arena::new();
    let mut tc = Tc::new(&store, &local);
    tc.limit = store.declars.len() as u32;
    let body = |name| {
        store
            .declars
            .iter()
            .find_map(|d| match *d {
                Declar::Def(info, value, _) if info.name.to_string() == name => Some(value),
                _ => None,
            })
            .unwrap()
    };
    let direct = body("PhaseTwo.direct");
    let projected = body("PhaseTwo.projected");
    // Bound the regression itself: the old reduction order traversed billions
    // of successors. Exhaustion here must fail the test, not hang the suite.
    tc.probe_remaining = Some(10_000);
    outcome::run(|| assert!(tc.def_eq(direct, projected)))
        .unwrap_or_else(|e| panic!("{}", e.reason()));
    assert!(local.allocated_bytes() < 1 << 20);
}

#[test]
fn resource_exhaustion_is_unsupported_and_the_next_check_can_proceed() {
    let arena = Arena::new();
    let store = import_bytes(&arena, REDUCTION).unwrap();
    let mut local = Arena::new();
    let failure = outcome::run(|| {
        Tc::new(&store, &local)
            .with_limits(Limits {
                steps: 0,
                arena_bytes: 1 << 20,
            })
            .check(0);
    })
    .err()
    .expect("zero budget must not succeed");
    assert_eq!(failure.status(), "unsupported");
    assert_eq!(failure.exit_code(), 2);
    local.reset();
    outcome::run(|| Tc::new(&store, &local).check(0)).unwrap_or_else(|e| panic!("{}", e.reason()));
}

#[test]
fn projections_cannot_extract_data_from_transported_propositions() {
    let input = include_bytes!("../../tests/fixtures/projection-prop.ndjson");
    assert!(check_all(input).unwrap_err().contains("projection"));
}

#[test]
fn nested_and_primitive_fixtures_pass_complete_validation() {
    for input in [
        include_bytes!("../../tests/fixtures/nested.ndjson").as_slice(),
        include_bytes!("../../tests/fixtures/primitives.ndjson").as_slice(),
    ] {
        assert_eq!(
            check_all(input).unwrap(),
            nano_lean::export::check_export(Cursor::new(input))
                .unwrap()
                .declarations
        );
    }
    assert!(
        check_all(include_bytes!(
            "../../tests/fixtures/invalid-nested-parameter.ndjson"
        ))
        .is_err()
    );
}

#[test]
fn forged_inductive_metadata_and_computation_rules_are_rejected() {
    for mutation in 0..5 {
        let mut values: Vec<serde_json::Value> = FOUNDATIONS
            .split(|&b| b == b'\n')
            .filter(|s| !s.is_empty())
            .map(|s| serde_json::from_slice(s).unwrap())
            .collect();
        let block = values
            .iter_mut()
            .find_map(|v| v.get_mut("inductive"))
            .unwrap();
        match mutation {
            0 => {
                block["types"][0]["isRec"] =
                    serde_json::json!(!block["types"][0]["isRec"].as_bool().unwrap())
            }
            1 => block["types"][0]["numNested"] = serde_json::json!(10),
            2 => block["types"][0]["isReflexive"] = serde_json::json!(true),
            3 => block["ctors"][0]["numFields"] = serde_json::json!(100),
            _ => block["recs"][0]["rules"][0]["rhs"] = block["types"][0]["type"].clone(),
        }
        let bytes = values
            .into_iter()
            .map(|v| format!("{v}\n"))
            .collect::<String>();
        assert!(
            check_all(bytes.as_bytes()).is_err(),
            "accepted mutation {mutation}"
        );
        assert!(nano_lean::export::check_export(Cursor::new(bytes.as_bytes())).is_err());
    }
}

#[test]
fn quotient_kind_must_match_its_name() {
    let input = include_bytes!("../../tests/fixtures/primitives.ndjson");
    let mut values: Vec<serde_json::Value> = input
        .split(|&b| b == b'\n')
        .filter(|s| !s.is_empty())
        .map(|s| serde_json::from_slice(s).unwrap())
        .collect();
    let quotient = values.iter_mut().find_map(|v| v.get_mut("quot")).unwrap();
    quotient["kind"] = serde_json::json!("lift");
    let bytes = values
        .into_iter()
        .map(|v| format!("{v}\n"))
        .collect::<String>();
    assert!(
        check_all(bytes.as_bytes())
            .unwrap_err()
            .contains("quotient")
    );
}

#[test]
fn universe_equivalence_agrees_with_existing_kernel() {
    let arena = Arena::new();
    let store = import_bytes(&arena, FOUNDATIONS).unwrap();
    let local = Arena::new();
    let mut tc = Tc::new(&store, &local);
    let mut base = vec![(tc.ctx.zero(), nano_lean::Level::Nat(0))];
    for n in ["u", "v"] {
        let name = tc.ctx.str1(n);
        base.push((tc.ctx.param(name), nano_lean::Level::Param(n.into())));
    }
    let one = tc.ctx.succ(tc.ctx.zero());
    base.push((one, nano_lean::Level::Nat(1)));
    let mut levels = base.clone();
    for (a, old_a) in &base {
        for (b, old_b) in &base {
            levels.push((
                tc.ctx.max(*a, *b),
                nano_lean::Level::max(old_a.clone(), old_b.clone()),
            ));
            levels.push((
                tc.ctx.imax(*a, *b),
                nano_lean::Level::imax(old_a.clone(), old_b.clone()),
            ));
        }
    }
    for (a, old_a) in &levels {
        for (b, old_b) in &levels {
            assert_eq!(
                tc.ctx.level_eq(*a, *b),
                old_a.equivalent(old_b).unwrap(),
                "{old_a:?} == {old_b:?}"
            );
        }
    }
}

#[test]
fn fallback_cannot_accept_an_invalid_body_or_restore_an_exhausted_budget() {
    let input = forward_reference(false);
    let arena = Arena::new();
    let store = import_bytes(&arena, &input).unwrap();
    let local = Arena::new();
    let index = store
        .declars
        .iter()
        .position(|d| d.name().to_string() == "f")
        .unwrap() as u32;
    assert!(outcome::run(|| Tc::new(&store, &local).check_existing(index)).is_err());
    let arena = Arena::new();
    let store = import_bytes(&arena, REDUCTION).unwrap();
    let local = Arena::new();
    let failure = outcome::run(|| {
        Tc::new(&store, &local)
            .with_limits(Limits {
                steps: 0,
                arena_bytes: 1,
            })
            .check_existing(0)
    })
    .err()
    .unwrap();
    assert_eq!(failure.status(), "unsupported");
}

#[test]
fn arena_fallback_rechecks_the_target_body_and_reports_its_use() {
    for corrupt in [false, true] {
        let mut values: Vec<serde_json::Value> = REDUCTION
            .split(|&b| b == b'\n')
            .filter(|s| !s.is_empty())
            .map(|s| serde_json::from_slice(s).unwrap())
            .collect();
        if corrupt {
            let wrong = values.iter().find(|v| v.get("natVal").is_some()).unwrap()["ie"].clone();
            let theorem = values.iter_mut().find_map(|v| v.get_mut("thm")).unwrap();
            theorem["value"] = wrong;
        }
        let bytes = values
            .into_iter()
            .map(|v| format!("{v}\n"))
            .collect::<String>();
        let arena = Arena::new();
        let store = import_bytes(&arena, bytes.as_bytes()).unwrap();
        let index = store
            .declars
            .iter()
            .position(|d| matches!(d, Declar::Thm(..)))
            .unwrap() as u32;
        let mut local = Arena::new();
        local.alloc_slice_fill_copy(4096, 0u8);
        let result = check_declaration(
            &store,
            &mut local,
            index,
            Limits {
                steps: 1_000_000,
                arena_bytes: 1,
            },
        );
        if corrupt {
            assert_eq!(
                result.err().expect("invalid theorem accepted").status(),
                "rejected"
            );
        } else {
            assert!(result.unwrap_or_else(|e| panic!("{}", e.reason())));
        }
    }
}
