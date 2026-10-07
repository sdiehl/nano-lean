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
        for op in Operator::ALL {
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
        let (compact, _) = mutate::compact(&lines, None);
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
fn shrinking_keeps_the_pinned_declaration_and_its_cone() {
    let lines = fixture("primitives.ndjson");
    let pin = lines.iter().rposition(mutate::is_declaration).unwrap();
    let small = mutate::shrink(lines.clone(), Some(pin), |c| {
        mutate::check(c, Limits::default()).reference.accepted()
    });
    assert!(small.len() < lines.len());
    assert_eq!(last_name(&small), last_name(&lines));
    assert!(mutate::check(&small, Limits::default()).agree());
}
