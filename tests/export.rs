use nano_lean::export::{ExportError, check_export, check_export_file};
use std::{
    io::Cursor,
    sync::atomic::{AtomicUsize, Ordering},
};

static NEXT_FILE: AtomicUsize = AtomicUsize::new(0);

#[test]
fn reducibility_hints_do_not_skip_definition_validation() {
    use serde_json::{Value, json};
    let original: Vec<Value> = include_str!("fixtures/smoke.ndjson")
        .lines()
        .map(|s| serde_json::from_str(s).unwrap())
        .collect();
    let source = |items: &[Value]| {
        items
            .iter()
            .map(Value::to_string)
            .collect::<Vec<_>>()
            .join("\n")
    };
    for hint in [
        json!("opaque"),
        json!("abbrev"),
        json!({"regular": 0}),
        json!({"regular": u32::MAX}),
    ] {
        let mut items = original.clone();
        for item in &mut items {
            if let Some(d) = item.get_mut("def") {
                d["hints"] = hint.clone();
            }
        }
        assert_eq!(check(&source(&items)).unwrap().declarations, 6);
        let d = items.iter_mut().find_map(|i| i.get_mut("def")).unwrap();
        d["value"] = d["type"].clone();
        assert!(matches!(
            check(&source(&items)),
            Err(ExportError::Invalid(_))
        ));
    }
}

fn check(s: &str) -> Result<nano_lean::export::ExportReport, ExportError> {
    let path = std::env::temp_dir().join(format!(
        "nano-lean-export-{}-{}.ndjson",
        std::process::id(),
        NEXT_FILE.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::write(&path, s).unwrap();
    let file = check_export_file(&path);
    std::fs::remove_file(path).unwrap();
    let stream = check_export(Cursor::new(s));
    match (&stream, &file) {
        (Ok(a), Ok(b)) => assert_eq!(a.json(), b.json()),
        (Err(a), Err(b)) => assert_eq!(std::mem::discriminant(a), std::mem::discriminant(b)),
        _ => panic!("stream/file mismatch: {stream:?} versus {file:?}"),
    }
    stream
}

#[test]
fn official_exporter_smoke() {
    let report = check(include_str!("fixtures/smoke.ndjson")).unwrap();
    assert_eq!(report.declarations, 6);
}

#[test]
fn neutral_recursor_does_not_repeat_major_normalization() {
    let report = check(include_str!("fixtures/neutral.ndjson")).unwrap();
    assert_eq!(report.declarations, 53);
}

#[test]
fn theorem_bodies_reduce_but_opaque_bodies_do_not() {
    use serde_json::{Value, json};
    let source = include_str!("fixtures/theorem-reduction.ndjson");
    assert_eq!(check(source).unwrap().declarations, 36);
    let mut items: Vec<Value> = source
        .lines()
        .map(|line| serde_json::from_str(line).unwrap())
        .collect();
    let name = items
        .iter()
        .find(|item| item["str"]["str"] == "conjunction")
        .unwrap()["in"]
        .clone();
    let item = items
        .iter_mut()
        .find(|item| item["thm"]["name"] == name)
        .unwrap();
    let mut declaration = item.as_object_mut().unwrap().remove("thm").unwrap();
    declaration["isUnsafe"] = json!(false);
    *item = json!({"opaque": declaration});
    let source = items
        .iter()
        .map(Value::to_string)
        .collect::<Vec<_>>()
        .join("\n");
    let error = check(&source).unwrap_err();
    assert!(matches!(error, ExportError::Invalid(ref s) if s.contains("type mismatch")));
}

#[test]
fn official_ordinary_inductive_export() {
    let report = check(include_str!("fixtures/ordinary.ndjson")).unwrap();
    assert_eq!(report.declarations, 4);
}

#[test]
fn official_mutual_inductive_export() {
    let report = check(include_str!("fixtures/mutual.ndjson")).unwrap();
    assert_eq!(report.declarations, 7);
}

#[test]
fn official_primitive_export() {
    let report = check(include_str!("fixtures/primitives.ndjson")).unwrap();
    assert_eq!(report.declarations, 35);
    let forged = include_str!("fixtures/primitives.ndjson").replace(
        "680564733841876926926749214863536422914",
        "680564733841876926926749214863536422915",
    );
    assert!(matches!(check(&forged), Err(ExportError::Invalid(_))));
}

#[test]
fn malformed_quotient_signatures_and_metadata_are_rejected() {
    use serde_json::{Value, json};
    let original: Vec<Value> = include_str!("fixtures/primitives.ndjson")
        .lines()
        .map(|line| serde_json::from_str(line).unwrap())
        .collect();
    for (i, item) in original
        .iter()
        .enumerate()
        .filter(|(_, item)| item.get("quot").is_some())
    {
        for (field, value) in [
            ("type", json!(0)),
            ("name", json!(0)),
            ("kind", json!("bogus")),
            ("levelParams", json!([])),
            (
                "kind",
                json!(if item["quot"]["kind"] == "type" {
                    "ctor"
                } else {
                    "type"
                }),
            ),
        ] {
            let mut entries = original.clone();
            entries[i]["quot"][field] = value;
            let input = entries
                .iter()
                .map(Value::to_string)
                .collect::<Vec<_>>()
                .join("\n");
            assert!(
                matches!(check(&input), Err(ExportError::Invalid(_))),
                "quotient {} field {field}",
                item["quot"]["kind"]
            );
        }
        let mut entries = original.clone();
        entries.insert(i + 1, item.clone());
        let input = entries
            .iter()
            .map(Value::to_string)
            .collect::<Vec<_>>()
            .join("\n");
        assert!(matches!(check(&input), Err(ExportError::Invalid(_))));
    }
    assert!(matches!(
        check("{\"meta\":{\"format\":{\"version\":\"3.1.0\"}}}\n{\"quot\":{}}\n"),
        Err(ExportError::Invalid(_))
    ));
}

#[test]
fn malformed_literals_and_safety_annotations_are_rejected() {
    use serde_json::json;
    let meta = "{\"meta\":{\"format\":{\"version\":\"3.1.0\"}}}\n";
    for value in [
        json!(""),
        json!("-1"),
        json!("+1"),
        json!("1.0"),
        json!("1e3"),
        json!(" 1"),
        json!("١"),
        json!(1),
        json!(null),
    ] {
        let input = format!("{meta}{}\n", json!({"ie":0,"natVal":value}));
        assert!(matches!(check(&input), Err(ExportError::Invalid(_))));
    }
    for entry in [json!({"ie":0,"strVal":42}), json!({"ie":0,"strVal":null})] {
        assert!(matches!(
            check(&format!("{meta}{entry}\n")),
            Err(ExportError::Invalid(_))
        ));
    }
    let fixture = include_str!("fixtures/primitives.ndjson");
    for safety in ["unsafe", "partial", "unknown"] {
        let input = fixture.replace("\"safety\":\"safe\"", &format!("\"safety\":\"{safety}\""));
        assert!(matches!(check(&input), Err(ExportError::Invalid(_))));
    }
    let input = fixture.replace("\"isUnsafe\":false", "\"isUnsafe\":true");
    assert!(matches!(check(&input), Err(ExportError::Invalid(_))));
}

#[test]
fn malformed_entries_and_bad_terms_are_rejected() {
    let meta = "{\"meta\":{\"format\":{\"version\":\"3.1.0\"}}}\n";
    for body in [
        "{\"inductive\":{}}\n",
        "{\"ie\":0,\"sort\":23}\n",
        "{\"ie\":0,\"sort\":0}\n{\"ie\":0,\"sort\":0}\n",
        "{\"in\":0,\"str\":{\"pre\":0,\"str\":\"x\"}}\n",
        "{\"ie\":0,\"bvar\":0}\n{\"in\":1,\"str\":{\"pre\":0,\"str\":\"bad\"}}\n{\"axiom\":{\"name\":1,\"type\":0,\"levelParams\":[],\"isUnsafe\":false}}\n",
    ] {
        assert!(matches!(
            check(&format!("{meta}{body}")),
            Err(ExportError::Invalid(_))
        ));
    }
    assert!(check("").is_err());
    assert!(check("{}\n").is_err());
}

#[test]
fn unsupported_is_not_reported_as_checked() {
    let input = "{\"meta\":{\"format\":{\"version\":\"3.1.0\"}}}\n{\"futureDeclaration\":{}}\n";
    assert!(matches!(check(input), Err(ExportError::Unsupported(_))));
}

#[test]
fn sparse_and_out_of_order_indices_are_accepted() {
    let input = "{\"meta\":{\"format\":{\"version\":\"3.1.0\"}}}\n{\"il\":900,\"succ\":0}\n{\"il\":1,\"succ\":900}\n{\"in\":400,\"str\":{\"pre\":0,\"str\":\"x\"}}\n{\"ie\":23,\"sort\":1}\n{\"axiom\":{\"name\":400,\"type\":23,\"levelParams\":[],\"isUnsafe\":false}}\n";
    assert_eq!(check(input).unwrap().declarations, 1);
}

#[test]
fn reclamation_across_inductive_boundaries() {
    let fixture = include_str!("fixtures/inductive-boundaries.ndjson");
    let input = format!(
        "{fixture}{}\n{}\n",
        r#"{"in":22,"str":{"pre":0,"str":"SubtypeAgain"}}"#,
        r#"{"axiom":{"name":22,"type":6,"levelParams":[2],"isUnsafe":false}}"#,
    );
    let report = check(&input).unwrap();
    assert_eq!(report.declarations, 7);
    assert_eq!(report.expressions, 67);
}

#[test]
fn invalid_inductive_expression_references_are_rejected() {
    let fixture = include_str!("fixtures/inductive-boundaries.ndjson");
    for reference in [r#""type":6"#, r#""type":17"#, r#""type":36"#, r#""rhs":45"#] {
        let key = reference.split(':').next().unwrap();
        let input = fixture.replace(reference, &format!("{key}:9999"));
        assert!(matches!(check(&input), Err(ExportError::Invalid(_))));
    }
}

#[test]
fn imported_unicode_is_preserved_through_escaped_json_and_equality() {
    use serde_json::{Value, json};
    let mut entries: Vec<Value> = include_str!("fixtures/primitives.ndjson")
        .lines()
        .map(|line| serde_json::from_str(line).unwrap())
        .collect();
    let next = |key: &str| {
        entries
            .iter()
            .filter_map(|v| v[key].as_u64())
            .max()
            .unwrap()
            + 1
    };
    let name = next("in");
    let level = next("il");
    let mut expression = next("ie");
    let eq = entries
        .iter()
        .find(|v| v["str"]["pre"] == 0 && v["str"]["str"] == "Eq")
        .unwrap()["in"]
        .as_u64()
        .unwrap();
    let refl = entries
        .iter()
        .find(|v| v["str"]["pre"] == eq && v["str"]["str"] == "refl")
        .unwrap()["in"]
        .as_u64()
        .unwrap();
    entries.push(json!({"in":name,"str":{"pre":0,"str":"String"}}));
    entries.push(json!({"in":name+1,"str":{"pre":0,"str":"unicodeEquality"}}));
    entries.push(json!({"il":level,"succ":0}));
    fn add(entries: &mut Vec<Value>, next: &mut u64, mut entry: Value) -> u64 {
        let id = *next;
        *next += 1;
        entry["ie"] = json!(id);
        entries.push(entry);
        id
    }
    let sort = add(&mut entries, &mut expression, json!({"sort":level}));
    entries.push(json!({"axiom":{"name":name,"type":sort,"levelParams":[],"isUnsafe":false}}));
    let string = add(
        &mut entries,
        &mut expression,
        json!({"const":{"name":name,"us":[]}}),
    );
    let left = add(&mut entries, &mut expression, json!({"strVal":"Aé水🦀\0"}));
    let right = add(&mut entries, &mut expression, json!({"strVal":"Aé水🦀\0"}));
    let mut ty = add(
        &mut entries,
        &mut expression,
        json!({"const":{"name":eq,"us":[level]}}),
    );
    for arg in [string, left, right] {
        ty = add(
            &mut entries,
            &mut expression,
            json!({"app":{"fn":ty,"arg":arg}}),
        );
    }
    let mut value = add(
        &mut entries,
        &mut expression,
        json!({"const":{"name":refl,"us":[level]}}),
    );
    for arg in [string, left] {
        value = add(
            &mut entries,
            &mut expression,
            json!({"app":{"fn":value,"arg":arg}}),
        );
    }
    entries.push(
        json!({"thm":{"name":name+1,"levelParams":[],"type":ty,"value":value,"all":[name+1]}}),
    );
    let input = entries
        .iter()
        .map(Value::to_string)
        .collect::<Vec<_>>()
        .join("\n");
    let raw = serde_json::to_string("Aé水🦀\0").unwrap();
    let escaped = input.replacen(&raw, r#""\u0041\u00e9\u6c34\ud83e\udd80\u0000""#, 1);
    assert_eq!(check(&escaped).unwrap().declarations, 37);
    let corrupted = escaped.replacen(&raw, &serde_json::to_string("Ae水🦀\0").unwrap(), 1);
    assert!(matches!(check(&corrupted), Err(ExportError::Invalid(_))));
}

#[test]
fn official_nested_inductive_exports() {
    let minimal = check(include_str!("fixtures/nested-minimal.ndjson")).unwrap();
    assert_eq!(minimal.declarations, 8);
    let expanded = check(include_str!("fixtures/nested.ndjson")).unwrap();
    assert_eq!(expanded.declarations, 91);
    let reordered: Vec<_> = include_str!("fixtures/nested.ndjson")
        .lines()
        .map(|line| {
            let mut value: serde_json::Value = serde_json::from_str(line).unwrap();
            if let Some(block) = value.get_mut("inductive") {
                block["ctors"].as_array_mut().unwrap().reverse();
                block["recs"].as_array_mut().unwrap().reverse();
            }
            value.to_string()
        })
        .collect();
    assert_eq!(check(&reordered.join("\n")).unwrap().declarations, 91);
}

#[test]
fn nested_unused_parameter_does_not_hide_an_ill_typed_argument() {
    let error = check(include_str!("fixtures/invalid-nested-parameter.ndjson")).unwrap_err();
    assert!(matches!(error, ExportError::Invalid(_)), "{error}");
    assert!(
        error.to_string().contains("projection type name mismatch"),
        "{error}"
    );
}

#[test]
fn forged_nested_metadata_signatures_and_rules_are_rejected() {
    use serde_json::{Value, json};
    let original: Vec<Value> = include_str!("fixtures/nested-minimal.ndjson")
        .lines()
        .map(|s| serde_json::from_str(s).unwrap())
        .collect();
    let index = original
        .iter()
        .position(|v| v["inductive"]["types"][0]["numNested"] == 1)
        .unwrap();
    let serialize = |values: &[Value]| {
        values
            .iter()
            .map(Value::to_string)
            .collect::<Vec<_>>()
            .join("\n")
    };
    for count in [0, 2] {
        let mut values = original.clone();
        values[index]["inductive"]["types"][0]["numNested"] = json!(count);
        assert!(matches!(
            check(&serialize(&values)),
            Err(ExportError::Invalid(_))
        ));
    }
    for rec in 0..2 {
        for (field, value) in [
            ("type", json!(0)),
            ("numParams", json!(1)),
            ("numMotives", json!(1)),
            ("k", json!(true)),
            ("levelParams", json!([])),
            ("all", json!([])),
        ] {
            let mut values = original.clone();
            values[index]["inductive"]["recs"][rec][field] = value;
            assert!(
                matches!(check(&serialize(&values)), Err(ExportError::Invalid(_))),
                "rec {rec} {field}"
            );
        }
        for field in ["rhs", "nfields", "ctor"] {
            let mut values = original.clone();
            values[index]["inductive"]["recs"][rec]["rules"][0][field] = json!(999);
            assert!(matches!(
                check(&serialize(&values)),
                Err(ExportError::Invalid(_))
            ));
        }
    }
}

#[test]
fn nested_parameters_reject_negative_occurrences_and_constructor_locals() {
    use serde_json::{Value, json};
    let original: Vec<Value> = include_str!("fixtures/nested-minimal.ndjson")
        .lines()
        .map(|s| serde_json::from_str(s).unwrap())
        .collect();
    let block_index = original
        .iter()
        .position(|v| v["inductive"]["types"][0]["numNested"] == 1)
        .unwrap();
    let ctor_type = original[block_index]["inductive"]["ctors"][0]["type"]
        .as_u64()
        .unwrap();
    let expression = |id: u64| original.iter().find(|v| v["ie"] == id).unwrap();
    let list_tree_id = expression(ctor_type)["forallE"]["type"].as_u64().unwrap();
    let list_tree = expression(list_tree_id);
    let tree = list_tree["app"]["arg"].as_u64().unwrap();
    let list = list_tree["app"]["fn"].as_u64().unwrap();
    for local in [false, true] {
        let mut values = original[..block_index].to_vec();
        let mut next = values
            .iter()
            .filter_map(|v| v["ie"].as_u64())
            .max()
            .unwrap()
            + 1;
        let mut add = |mut v: Value| {
            let id = next;
            next += 1;
            v["ie"] = json!(id);
            values.push(v);
            id
        };
        let pi = |domain, body| json!({"forallE":{"name":0,"binderInfo":"default","type":domain,"body":body}});
        let argument = if local {
            let x = add(json!({"bvar":0}));
            let lambda =
                add(json!({"lam":{"name":0,"binderInfo":"default","type":tree,"body":tree}}));
            add(json!({"app":{"fn":lambda,"arg":x}}))
        } else {
            add(pi(tree, tree))
        };
        let domain = add(json!({"app":{"fn":list,"arg":argument}}));
        let mut ty = add(pi(domain, tree));
        if local {
            ty = add(pi(tree, ty));
        }
        let mut block = original[block_index].clone();
        block["inductive"]["ctors"][0]["type"] = json!(ty);
        if local {
            block["inductive"]["ctors"][0]["numFields"] = json!(2);
        }
        values.push(block);
        let input = values
            .iter()
            .map(Value::to_string)
            .collect::<Vec<_>>()
            .join("\n");
        let error = check(&input).unwrap_err();
        let expected = if local {
            "constructor-local"
        } else {
            "negative inductive occurrence"
        };
        assert!(
            matches!(error, ExportError::Invalid(_)) && error.to_string().contains(expected),
            "{error}"
        );
    }
}

#[test]
fn source_groups_do_not_enable_forward_or_cyclic_references() {
    let original = include_str!("fixtures/smoke.ndjson");
    let mut records: Vec<serde_json::Value> = original
        .lines()
        .map(|s| serde_json::from_str(s).unwrap())
        .collect();
    let grouped: Vec<_> = records
        .iter()
        .filter_map(|r| {
            r.get("def")
                .or_else(|| r.get("thm"))
                .map(|d| d["name"].clone())
        })
        .collect();
    assert!(grouped.len() > 1);
    for r in &mut records {
        for k in ["def", "thm"] {
            if let Some(d) = r.get_mut(k) {
                d["all"] = serde_json::json!(grouped);
            }
        }
    }
    let encode = |rs: &[serde_json::Value]| {
        rs.iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>()
            .join("\n")
    };
    records.sort_by_key(|r| {
        if r.get("meta").is_some() {
            0
        } else if r.get("in").is_some() {
            1
        } else {
            2
        }
    });
    check(&encode(&records)).unwrap();
    let declaration = records.iter().position(|r| r.get("def").is_some()).unwrap();
    let next = records
        .iter()
        .filter_map(|r| r.get("ie").and_then(|v| v.as_u64()))
        .max()
        .unwrap()
        + 1;
    for target in [&grouped[0], grouped.last().unwrap()] {
        let mut forged = records.clone();
        forged[declaration]["def"]["value"] = serde_json::json!(next);
        forged.insert(
            declaration,
            serde_json::json!({"ie": next, "const": {"name": target, "us": []}}),
        );
        let error = check(&encode(&forged)).unwrap_err();
        assert!(error.to_string().contains("unknown constant"), "{error}");
    }
}
