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
    let input = "{\"meta\":{\"format\":{\"version\":\"3.1.0\"}}}\n{\"quot\":{}}\n";
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
