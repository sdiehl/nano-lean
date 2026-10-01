use nano_lean::export::{ExportError, check_export, check_export_file};
use std::{
    io::Cursor,
    sync::atomic::{AtomicUsize, Ordering},
};

static NEXT_FILE: AtomicUsize = AtomicUsize::new(0);

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
