#![allow(clippy::unwrap_used, clippy::panic)]

use clap::ValueEnum;
use nano_lean::{
    checker::Limits,
    mutate::{self, Operator, Rng},
};
use std::{fs, path::Path};

fn fixture(name: &str) -> Vec<serde_json::Value> {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures")
        .join(name);
    mutate::parse(&fs::read_to_string(path).unwrap()).unwrap()
}

#[test]
fn seeded_sweep_finds_nothing() {
    let mut rng = Rng::new(1);
    let mut findings = Vec::new();
    for name in ["ordinary.ndjson", "mutual.ndjson", "primitives.ndjson"] {
        let lines = fixture(name);
        let baseline = mutate::check(&lines, Limits::default());
        for &op in Operator::value_variants() {
            let mut candidates = mutate::mutants(&lines, op);
            while candidates.len() > 8 {
                candidates.swap_remove(rng.below(candidates.len()));
            }
            for m in candidates {
                let v = mutate::check(&m.apply(&lines), Limits::default());
                if let Some(why) = mutate::finding(m.expect, &baseline, &v) {
                    findings.push(format!("{name} {op} {}: {why}\n{v}", m.site()));
                }
            }
        }
    }
    assert!(findings.is_empty(), "{}", findings.join("\n"));
}

#[test]
fn compaction_preserves_verdicts() {
    for name in [
        "nested.ndjson",
        "projection-prop.ndjson",
        "foundations.ndjson",
    ] {
        let lines = fixture(name);
        let (compact, _) = mutate::compact(&lines, &[]);
        assert_eq!(
            mutate::check(&compact, Limits::default()).to_string(),
            mutate::check(&lines, Limits::default()).to_string(),
            "{name}"
        );
    }
}

fn last_name(lines: &[serde_json::Value]) -> String {
    let decl = lines.iter().rfind(|l| mutate::is_declaration(l)).unwrap();
    let (_, body) = decl.as_object().unwrap().iter().next().unwrap();
    let mut id = body["name"].as_u64().unwrap();
    let mut parts = Vec::new();
    while id != 0 {
        let entry = lines.iter().find(|l| l["in"] == id).unwrap();
        let (pre, part) = match (&entry.get("str"), &entry.get("num")) {
            (Some(s), _) => (&s["pre"], s["str"].as_str().unwrap().to_owned()),
            (_, Some(n)) => (&n["pre"], n["i"].to_string()),
            _ => unreachable!(),
        };
        parts.push(part);
        id = pre.as_u64().unwrap();
    }
    parts.reverse();
    parts.join(".")
}

#[test]
fn shrinking_keeps_the_edit_and_a_valid_base() {
    let lines = fixture("primitives.ndjson");
    let pin = lines.iter().rposition(mutate::is_declaration).unwrap();
    let m = mutate::mutants(&lines, Operator::DuplicateDecl)
        .into_iter()
        .find(|m| m.pins() == [pin])
        .unwrap();
    let wanted = mutate::signature(&mutate::check(&m.apply(&lines), Limits::default()));
    assert_eq!(wanted, "RRR");
    let (base, pins) = mutate::shrink(lines.clone(), m.pins(), |c, pins| {
        mutate::signature(&mutate::check(c, Limits::default())) == "AAA"
            && mutate::signature(&mutate::check(&m.at(pins).apply(c), Limits::default())) == wanted
    });
    assert!(base.len() < lines.len());
    assert_eq!(last_name(&base), last_name(&lines));
    assert_eq!(
        mutate::signature(&mutate::check(&base, Limits::default())),
        "AAA"
    );
    let witness = m.at(&pins).apply(&base);
    assert_eq!(
        mutate::signature(&mutate::check(&witness, Limits::default())),
        wanted
    );
}
