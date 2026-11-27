use super::*;
use crate::import::import_bytes;
use crate::mutate::render;
use crate::resource::on_stack;
use std::io::Cursor;

const FOUNDATIONS: &[u8] = include_bytes!("../../tests/fixtures/foundations.ndjson");

fn check_all(bytes: &[u8]) -> Result<usize, String> {
    let arena = Arena::new();
    let store = import_bytes(&arena, bytes).map_err(|e| e.to_string())?;
    let mut adapter = Adapter::new(&store);
    for index in 0..store.declars.len() {
        let mut local = Arena::new();
        check_with_adapter(
            &store,
            &mut local,
            index as u32,
            Limits::default(),
            Some(&mut adapter),
            false,
        )
        .map_err(|e| format!("{}: {}", store.declars[index].name(), e.reason()))?;
    }
    Ok(store.stats.declarations)
}

#[test]
fn foundational_signatures_and_theorems_agree_with_existing_kernel() {
    let count = check_all(FOUNDATIONS).unwrap();
    let legacy = crate::export::check_export(Cursor::new(FOUNDATIONS)).unwrap();
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
            crate::export::check_export(Cursor::new(input))
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
    render(&lines).into_bytes()
}

#[test]
fn export_groups_never_authorize_self_or_forward_references() {
    for self_reference in [true, false] {
        let input = forward_reference(self_reference);
        assert!(check_all(&input).unwrap_err().contains("unknown constant"));
        assert!(crate::export::check_export(Cursor::new(input)).is_err());
    }
}

#[test]
fn a_reused_checker_cannot_reuse_types_or_unfoldings_from_a_later_scope() {
    let input = forward_reference(false);
    let arena = Arena::new();
    let store = import_bytes(&arena, &input).unwrap();
    let local = Arena::new();
    let mut tc = Tc::new(&store, &local);
    tc.limit = store.declars.len() as u32;
    let levels = tc.empty_levels();
    let g = tc.ctx.konst(store.declars[3].name(), levels);
    tc.infer(g, false).unwrap();
    assert!(tc.unfold(g).is_some());
    let failure = tc.check(2).expect_err("forward reference accepted");
    assert!(failure.reason().contains("unknown constant"));
    assert!(tc.unfold(g).is_none());
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
    assert!(tc.is_prop(proposition).unwrap());
    let sort = tc.ctx.sort(u);
    let unknown = tc.fresh_local(sort);
    assert!(!tc.is_prop(unknown).unwrap());
    let one = tc.ctx.succ(zero);
    let sort = tc.ctx.sort(one);
    let data = tc.fresh_local(sort);
    assert!(!tc.is_prop(data).unwrap());
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
    let input = render(&lines);
    assert!(check_all(input.as_bytes()).is_err());
    assert!(crate::export::check_export(Cursor::new(input)).is_err());
}

const REDUCTION: &[u8] = include_bytes!("../../tests/fixtures/reduction.ndjson");

#[test]
fn failed_and_exhausted_congruence_probes_fall_back_to_unfolding() {
    assert_eq!(
        check_all(REDUCTION).unwrap(),
        crate::export::check_export(Cursor::new(REDUCTION))
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
    assert!(
        tc.def_eq(body("PhaseTwo.erasedCostly"), body("PhaseTwo.erasedOne"))
            .unwrap()
    );
    assert!(tc.probe_remaining.is_none());
    assert_eq!(
        tc.probe_exhaustions, 0,
        "unused arguments need no reduction"
    );
    let (_, arguments) = tc.ctx.unfold_apps(body("PhaseTwo.erasedCostly"));
    let succ = tc.konst0(tc.names.nat_succ).unwrap();
    let costly = tc.ctx.app(succ, arguments[0]);
    let one = tc.ctx.nat_lit(1u32.into());
    let cheap = tc.ctx.app(succ, one);
    assert!(!tc.probe_args(costly, cheap).unwrap());
    assert!(tc.probe_exhaustions > 0);
    assert!(tc.probe_remaining.is_none());
    let exhausted = tc.probe_exhaustions;
    let remaining = tc.steps_left;
    assert!(!tc.probe_args(costly, cheap).unwrap());
    assert!(!tc.probe_args(cheap, costly).unwrap());
    assert_eq!(tc.probe_exhaustions, exhausted);
    assert_eq!(tc.steps_left, remaining);
    let two = tc.ctx.nat_lit(2u32.into());
    tc.fail_cache.insert((cheap, two));
    assert!(tc.def_eq(cheap, two).unwrap());
    assert!(!tc.def_eq(one, two).unwrap());
    assert!(local.allocated_bytes() < 2 << 20);
}

#[test]
fn rigid_congruence_does_not_repeat_exhausted_speculation() {
    let arena = Arena::new();
    let store = import_bytes(&arena, REDUCTION).unwrap();
    let local = Arena::new();
    let mut tc = Tc::new(&store, &local);
    tc.limit = store.declars.len() as u32;
    let value = store
        .declars
        .iter()
        .find_map(|d| match *d {
            Declar::Def(info, value, _) if info.name.to_string() == "PhaseTwo.erasedCostly" => {
                Some(value)
            }
            _ => None,
        })
        .unwrap();
    let (_, arguments) = tc.ctx.unfold_apps(value);
    let (rec, mut arguments) = tc.ctx.unfold_apps(arguments[0]);
    *arguments.last_mut().unwrap() = tc.ctx.nat_lit(512u32.into());
    let computation = tc.ctx.apps(rec, &arguments);
    let succ = tc.konst0(tc.names.nat_succ).unwrap();
    let left = tc.ctx.app(succ, computation);
    let zero = tc.ctx.nat_lit(0u32.into());
    let right = tc.ctx.app(succ, zero);
    assert!(tc.def_eq(left, right).unwrap());
    assert_eq!(tc.probe_exhaustions, 0);
    assert!(tc.fail_cache.is_empty());
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
    // A wrong reduction order walks billions of successors, so this must fail, not hang.
    tc.probe_remaining = Some(10_000);
    assert!(tc.def_eq(direct, projected).unwrap());
    assert!(local.allocated_bytes() < 1 << 20);
}

#[test]
fn resource_exhaustion_is_unsupported_and_the_next_check_can_proceed() {
    let arena = Arena::new();
    let store = import_bytes(&arena, REDUCTION).unwrap();
    let mut local = Arena::new();
    let failure = Tc::new(&store, &local)
        .with_limits(Limits {
            steps: 0,
            arena_bytes: 1 << 20,
        })
        .check(0)
        .expect_err("zero budget must not succeed");
    assert_eq!(failure.status(), "unsupported");
    assert_eq!(failure.exit_code(), 2);
    local.reset();
    Tc::new(&store, &local)
        .check(0)
        .unwrap_or_else(|e| panic!("{}", e.reason()));
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
            crate::export::check_export(Cursor::new(input))
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
                    serde_json::json!(!block["types"][0]["isRec"].as_bool().unwrap());
            }
            1 => block["types"][0]["numNested"] = serde_json::json!(10),
            2 => block["types"][0]["isReflexive"] = serde_json::json!(true),
            3 => block["ctors"][0]["numFields"] = serde_json::json!(100),
            _ => block["recs"][0]["rules"][0]["rhs"] = block["types"][0]["type"].clone(),
        }
        let bytes = render(&values);
        assert!(
            check_all(bytes.as_bytes()).is_err(),
            "accepted mutation {mutation}"
        );
        assert!(crate::export::check_export(Cursor::new(bytes.as_bytes())).is_err());
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
    let bytes = render(&values);
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
    let mut base = vec![(tc.ctx.zero(), crate::kernel::Level::Nat(0))];
    for n in ["u", "v"] {
        let name = tc.ctx.str1(n);
        base.push((tc.ctx.param(name), crate::kernel::Level::Param(n.into())));
    }
    let one = tc.ctx.succ(tc.ctx.zero());
    base.push((one, crate::kernel::Level::Nat(1)));
    let mut levels = base.clone();
    for (a, old_a) in &base {
        for (b, old_b) in &base {
            levels.push((
                tc.ctx.max(*a, *b),
                crate::kernel::Level::max(old_a.clone(), old_b.clone()),
            ));
            levels.push((
                tc.ctx.imax(*a, *b),
                crate::kernel::Level::imax(old_a.clone(), old_b.clone()),
            ));
        }
    }
    for (a, old_a) in &levels {
        for (b, old_b) in &levels {
            assert_eq!(
                tc.ctx.try_level_eq(*a, *b).unwrap(),
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
    assert!(Tc::new(&store, &local).check_existing(index).is_err());
    let arena = Arena::new();
    let store = import_bytes(&arena, REDUCTION).unwrap();
    let local = Arena::new();
    let mut tc = Tc::new(&store, &local).with_limits(Limits {
        steps: 0,
        arena_bytes: 1,
    });
    assert!(tc.check_existing(0).is_err());
    let failure = tc.failure();
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
        let bytes = render(&values);
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
                result.expect_err("invalid theorem accepted").status(),
                "rejected"
            );
        } else {
            assert_eq!(
                result.unwrap_or_else(|e| panic!("{}", e.reason())),
                CheckPath::Fallback
            );
        }
    }
}

#[test]
fn contextual_inference_keeps_distinct_local_types_and_dependencies() {
    let arena = Arena::new();
    let store = import_bytes(&arena, FOUNDATIONS).unwrap();
    let local = Arena::new();
    let mut tc = Tc::new(&store, &local);
    tc.limit = store.declars.len() as u32;
    let prop = tc.ctx.sort(tc.ctx.zero());
    let one = tc.ctx.succ(tc.ctx.zero());
    let ty = tc.ctx.sort(one);
    let variable = tc.ctx.var(0);
    let prop_identity = tc.ctx.lam(prop, variable);
    let type_identity = tc.ctx.lam(ty, variable);
    let prop_expected = tc.ctx.pi(prop, prop);
    let type_expected = tc.ctx.pi(ty, ty);
    assert_eq!(tc.infer(prop_identity, false).unwrap(), prop_expected);
    assert_eq!(tc.infer(type_identity, false).unwrap(), type_expected);
    let outer = tc.ctx.var(1);
    let inner = tc.ctx.lam(prop, outer);
    let dependent = tc.ctx.lam(ty, inner);
    let result = tc.infer(dependent, false).unwrap();
    let inner_expected = tc.ctx.pi(prop, ty);
    let expected = tc.ctx.pi(ty, inner_expected);
    assert_eq!(result, expected);
}

#[test]
fn beta_and_let_ladders_do_not_copy_remaining_bodies() {
    std::thread::Builder::new()
        .stack_size(16 << 20)
        .spawn(|| {
            let arena = Arena::new();
            let store = import_bytes(&arena, FOUNDATIONS).unwrap();
            let local = Arena::new();
            let mut tc = Tc::new(&store, &local);
            tc.limit = store.declars.len() as u32;
            let nat = tc.konst0(tc.names.nat).unwrap();
            let zero = tc.ctx.nat_lit(0u32.into());
            let variable = tc.ctx.var(0);
            let mut beta = variable;
            for _ in 0..1024 {
                let lam = tc.ctx.lam(nat, beta);
                beta = tc.ctx.app(lam, variable);
            }
            let lam = tc.ctx.lam(nat, beta);
            let term = tc.ctx.app(lam, zero);
            assert_eq!(tc.infer(term, false).unwrap(), nat);
            assert_eq!(tc.whnf(term).unwrap(), zero);
            let mut lets = variable;
            for _ in 0..1024 {
                lets = tc.ctx.let_(nat, variable, lets, false);
            }
            let lets = tc.ctx.let_(nat, zero, lets, false);
            assert_eq!(tc.infer(lets, false).unwrap(), nat);
            assert_eq!(tc.whnf(lets).unwrap(), zero);
            assert!(local.allocated_bytes() < 2 << 20);
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn cached_inductives_can_be_rechecked_in_an_earlier_scope() {
    let arena = Arena::new();
    let store = import_bytes(&arena, FOUNDATIONS).unwrap();
    let mut adapter = Adapter::new(&store);
    for indices in [
        (0..store.declars.len()).collect::<Vec<_>>(),
        (0..store.declars.len()).rev().collect(),
    ] {
        for index in indices {
            let mut local = Arena::new();
            check_with_adapter(
                &store,
                &mut local,
                index as u32,
                Limits::default(),
                Some(&mut adapter),
                true,
            )
            .unwrap_or_else(|e| panic!("{}: {}", store.declars[index].name(), e.reason()));
        }
    }
}

#[test]
fn conversion_locals_share_work_without_aliasing_nested_binders() {
    let arena = Arena::new();
    let store = import_bytes(&arena, FOUNDATIONS).unwrap();
    let local = Arena::new();
    let mut tc = Tc::new(&store, &local);
    tc.limit = store.declars.len() as u32;
    let nat = tc.konst0(tc.names.nat).unwrap();
    let inner = tc.ctx.var(0);
    let outer = tc.ctx.var(1);
    let left = tc.ctx.lam(nat, outer);
    let left = tc.ctx.lam(nat, left);
    let right = tc.ctx.lam(nat, inner);
    let right = tc.ctx.lam(nat, right);
    for _ in 0..4 {
        assert!(!tc.def_eq(left, right).unwrap());
        assert_eq!(tc.conversion_depth.get(), 0);
    }
    let slots = tc.conversion_locals.len();
    assert!(slots >= 2);
    assert!(!tc.def_eq(left, right).unwrap());
    assert_eq!(tc.conversion_locals.len(), slots);
    tc.probe_remaining = Some(1);
    assert!(tc.def_eq(left, right).is_err());
    assert!(tc.fail.is_none());
    tc.probe_remaining = None;
    assert_eq!(tc.conversion_depth.get(), 0);
    assert!(!tc.def_eq(left, right).unwrap());
}

#[test]
fn repeated_conversion_does_not_copy_bodies_under_fresh_local_names() {
    let arena = Arena::new();
    let store = import_bytes(&arena, FOUNDATIONS).unwrap();
    let local = Arena::new();
    let mut tc = Tc::new(&store, &local);
    tc.limit = store.declars.len() as u32;
    let nat = tc.konst0(tc.names.nat).unwrap();
    let succ = tc.konst0(tc.names.nat_succ).unwrap();
    let var = tc.ctx.var(0);
    let lhs_body = tc.ctx.app(succ, var);
    let lhs = tc.ctx.lam(nat, lhs_body);
    let identity = tc.ctx.lam(nat, var);
    let rhs_body = tc.ctx.app(identity, lhs_body);
    let rhs = tc.ctx.lam(nat, rhs_body);
    assert!(tc.def_eq(lhs, rhs).unwrap());
    let nodes = tc.ctx.dag.exprs.len();
    for _ in 0..64 {
        tc.eq_cache.remove(&(lhs, rhs));
        tc.eq_cache.remove(&(rhs, lhs));
        assert!(tc.def_eq(lhs, rhs).unwrap());
    }
    assert!(
        tc.ctx.dag.exprs.len() <= nodes + 8,
        "conversion reopened shared bodies with fresh locals"
    );
}

#[test]
fn inference_through_a_rejected_self_projecting_type_declines_instead_of_overflowing() {
    // The theorem's type projects out of the theorem itself; it is rejected, but the
    // quotient's type still infers through it, so inference cycles until the stack guard.
    let input = br#"{"meta":{"format":{"version":"3.1.0"}}}
{"in":1,"num":{"i":2,"pre":0}}
{"const":{"name":0,"us":[0,0]},"ie":0}
{"ie":1,"proj":{"idx":32768,"struct":0,"typeName":0}}
{"ie":2,"proj":{"idx":15,"struct":1,"typeName":0}}
{"thm":{"all":[0],"levelParams":[0,1],"name":0,"type":2,"value":0}}
{"in":2,"str":{"pre":0,"str":"Quot"}}
{"quot":{"kind":"type","levelParams":[],"name":2,"type":1}}
"#;
    on_stack(TEST_STACK, || {
        let arena = Arena::new();
        let store = import_bytes(&arena, input).unwrap();
        let local = Arena::new();
        let failure = Tc::new(&store, &local)
            .check(1)
            .expect_err("a cyclic type must not check");
        assert_eq!(failure.status(), "unsupported");
        assert!(failure.reason().contains("stack"), "{}", failure.reason());
    });
}

/// A fixed stack, so the tests below do not depend on the test harness's thread size.
const TEST_STACK: usize = 16 << 20;

/// Checks every declaration through the value core, as `nl-fast` checks an export, and
/// expects one of them to decline at the stack floor instead of overflowing.
fn value_core_declines_at_the_stack_floor(input: &[u8]) {
    on_stack(TEST_STACK, || {
        let arena = Arena::new();
        let store = import_bytes(&arena, input).unwrap();
        let mut session = crate::value_checker::Session::new(&store);
        let mut adapter = Adapter::new(&store);
        let mut reasons = Vec::new();
        for idx in 0..store.declars.len() as u32 {
            let result = Core::Value.check(
                &store,
                &mut session,
                idx,
                Limits::default(),
                &mut adapter,
                false,
            );
            if let Err(failure) = result {
                reasons.push(format!("{}: {}", failure.status(), failure.reason()));
            }
            session.reset();
        }
        assert!(
            reasons
                .iter()
                .any(|r| r.starts_with("unsupported") && r.contains("stack budget")),
            "{reasons:?}"
        );
    });
}

#[test]
fn value_inference_through_a_self_projecting_axiom_type_declines_instead_of_overflowing() {
    // The axiom's type projects out of the axiom itself.
    value_core_declines_at_the_stack_floor(
        br#"{"meta":{"format":{"version":"3.1.0"}}}
{"in":1,"num":{"i":1,"pre":0}}
{"const":{"name":0,"us":[]},"ie":0}
{"ie":1,"proj":{"idx":1,"struct":0,"typeName":1}}
{"axiom":{"isUnsafe":false,"levelParams":[],"name":0,"type":1}}
{"axiom":{"isUnsafe":false,"levelParams":[],"name":1,"type":1}}
{"in":2,"str":{"pre":0,"str":"Quot"}}
{"quot":{"kind":"type","levelParams":[],"name":2,"type":0}}
"#,
    );
}

#[test]
fn value_nat_reduction_through_a_self_referential_operand_declines_instead_of_overflowing() {
    // The theorem's value is `Nat.log2` of the theorem itself.
    value_core_declines_at_the_stack_floor(
        br#"{"meta":{"format":{"version":"3.1.0"}}}
{"in":1,"str":{"pre":0,"str":"Nat"}}
{"in":2,"str":{"pre":1,"str":"log2"}}
{"const":{"name":2,"us":[]},"ie":0}
{"const":{"name":0,"us":[]},"ie":1}
{"app":{"arg":1,"fn":0},"ie":2}
{"thm":{"all":[0],"levelParams":[],"name":0,"type":2,"value":2}}
{"in":3,"num":{"i":1,"pre":0}}
{"thm":{"all":[3],"levelParams":[],"name":3,"type":1,"value":2}}
"#,
    );
}

#[test]
fn value_conversion_through_a_self_referential_bool_abbrev_declines_instead_of_overflowing() {
    // `Bool.true` abbreviates the anonymous theorem, whose value reduces through `Nat.ble`.
    value_core_declines_at_the_stack_floor(
        br#"{"meta":{"format":{"version":"3.1.0"}}}
{"ie":0,"sort":0}
{"in":1,"str":{"pre":0,"str":"Nat"}}
{"in":2,"str":{"pre":1,"str":"ble"}}
{"const":{"name":2,"us":[0]},"ie":1}
{"ie":2,"natVal":"0"}
{"app":{"arg":2,"fn":1},"ie":3}
{"ie":4,"mdata":{"expr":3}}
{"ie":5,"natVal":"5"}
{"app":{"arg":5,"fn":4},"ie":6}
{"ie":7,"mdata":{"expr":6}}
{"thm":{"all":[0],"levelParams":[],"name":0,"type":0,"value":7}}
{"in":3,"str":{"pre":0,"str":"Bool"}}
{"in":4,"str":{"pre":3,"str":"true"}}
{"const":{"name":3,"us":[]},"ie":8}
{"const":{"name":0,"us":[]},"ie":9}
{"def":{"all":[4],"hints":"abbrev","levelParams":[],"name":4,"safety":"safe","type":8,"value":9}}
{"in":5,"num":{"i":281474976710657,"pre":0}}
{"in":6,"str":{"pre":0,"str":"e"}}
{"in":7,"num":{"i":2,"pre":6}}
{"thm":{"all":[5],"levelParams":[7],"name":5,"type":9,"value":9}}
"#,
    );
}

#[test]
fn term_reduction_through_a_rejected_theorem_declines_instead_of_overflowing() {
    // The theorem's value applies a projection out of itself; Quot.ind's type reduces through it.
    value_core_declines_at_the_stack_floor(
        br#"{"meta":{"format":{"version":"3.1.0"}}}
{"in":1,"str":{"pre":0,"str":"qrrqblm"}}
{"const":{"name":1,"us":[0]},"ie":0}
{"bvar":4095,"ie":1}
{"bvar":256,"ie":2}
{"app":{"arg":2,"fn":1},"ie":3}
{"app":{"arg":3,"fn":0},"ie":4}
{"ie":5,"proj":{"idx":1,"struct":0,"typeName":1}}
{"app":{"arg":2,"fn":5},"ie":6}
{"thm":{"all":[1],"levelParams":[1],"name":1,"type":4,"value":6}}
{"in":2,"str":{"pre":0,"str":"Quot"}}
{"in":3,"str":{"pre":2,"str":"ind"}}
{"in":4,"num":{"i":15,"pre":0}}
{"in":5,"num":{"i":15,"pre":4}}
{"quot":{"kind":"ind","levelParams":[5],"name":3,"type":0}}
"#,
    );
}

#[test]
fn positivity_through_a_self_unfolding_field_type_declines_instead_of_overflowing() {
    // `T` unfolds to `Prop -> (fun _ => T) I`, so the positivity check of `I.mk : T -> I`
    // meets the same Pi again after every binder, each time through a cached whnf.
    value_core_declines_at_the_stack_floor(br#"{"meta":{"format":{"version":"3.1.0"}}}
{"in":1,"str":{"pre":0,"str":"T"}}
{"in":2,"str":{"pre":0,"str":"I"}}
{"in":3,"str":{"pre":2,"str":"mk"}}
{"in":4,"str":{"pre":0,"str":"x"}}
{"ie":0,"sort":0}
{"const":{"name":2,"us":[]},"ie":1}
{"const":{"name":1,"us":[]},"ie":2}
{"ie":3,"lam":{"binderInfo":"default","body":2,"name":4,"type":0}}
{"app":{"arg":1,"fn":3},"ie":4}
{"forallE":{"binderInfo":"default","body":4,"name":4,"type":0},"ie":5}
{"thm":{"all":[1],"levelParams":[],"name":1,"type":0,"value":5}}
{"forallE":{"binderInfo":"default","body":1,"name":4,"type":2},"ie":6}
{"il":1,"succ":0}
{"ie":7,"sort":1}
{"inductive":{"ctors":[{"cidx":0,"induct":2,"isUnsafe":false,"levelParams":[],"name":3,"numFields":1,"numParams":0,"type":6}],"recs":[],"types":[{"all":[2],"ctors":[3],"isRec":true,"isReflexive":false,"isUnsafe":false,"levelParams":[],"name":2,"numIndices":0,"numNested":0,"numParams":0,"type":7}]}}
"#);
}

#[test]
fn kernel_positivity_through_a_self_unfolding_field_type_declines_instead_of_overflowing() {
    // The nested block goes to the reference kernel, whose positivity check meets the
    // same cycle through the theorem `yng`.
    value_core_declines_at_the_stack_floor(br#"{"meta":{"format":{"version":"3.1.0"}}}
{"in":1,"str":{"pre":0,"str":"yng"}}
{"ie":0,"sort":0}
{"in":2,"num":{"i":31,"pre":0}}
{"bvar":0,"ie":1}
{"in":3,"str":{"pre":0,"str":"h"}}
{"const":{"name":0,"us":[]},"ie":2}
{"const":{"name":1,"us":[]},"ie":3}
{"ie":4,"lam":{"binderInfo":"strictImplicit","body":3,"name":3,"type":2}}
{"app":{"arg":2,"fn":4},"ie":5}
{"forallE":{"binderInfo":"implicit","body":5,"name":2,"type":1},"ie":6}
{"thm":{"all":[1],"levelParams":[],"name":1,"type":0,"value":6}}
{"in":4,"str":{"pre":0,"str":"gzotfy"}}
{"il":1,"param":4}
{"il":2,"imax":[1,0]}
{"ie":7,"sort":2}
{"forallE":{"binderInfo":"default","body":0,"name":3,"type":3},"ie":8}
{"in":5,"str":{"pre":0,"str":"rec"}}
{"inductive":{"ctors":[{"cidx":0,"induct":0,"isUnsafe":false,"levelParams":[],"name":2,"numFields":1,"numParams":0,"type":8}],"recs":[{"all":[0],"isUnsafe":false,"k":false,"levelParams":[],"name":5,"numIndices":0,"numMinors":1,"numMotives":1,"numParams":9,"rules":[],"type":2}],"types":[{"all":[0],"ctors":[2],"isRec":false,"isReflexive":false,"isUnsafe":false,"levelParams":[],"name":0,"numIndices":0,"numNested":1,"numParams":0,"type":7}]}}
"#);
}
