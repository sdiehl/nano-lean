#[path = "support/graph.rs"]
mod graph;

use graph::Term;
use serde_json::{Value, json};
use std::{
    fs::File,
    io::{BufRead, BufReader},
    time::Instant,
};
use unbound::prelude::*;

type Result<T> = std::result::Result<T, Box<dyn std::error::Error>>;

fn references(item: &Value) -> Result<Vec<usize>> {
    let mut out = Vec::new();
    let mut add = |v: &Value| -> Result<()> {
        out.push(usize::try_from(
            v.as_u64().ok_or("invalid expression reference")?,
        )?);
        Ok(())
    };
    if item.get("ie").is_some() {
        if let Some(n) = item.get("app") {
            add(&n["fn"])?;
            add(&n["arg"])?;
        } else if let Some(n) = item.get("lam").or_else(|| item.get("forallE")) {
            add(&n["type"])?;
            add(&n["body"])?;
        } else if let Some(n) = item.get("letE") {
            add(&n["type"])?;
            add(&n["value"])?;
            add(&n["body"])?;
        } else if let Some(n) = item.get("proj") {
            add(&n["struct"])?;
        } else if let Some(n) = item.get("mdata") {
            add(&n["expr"])?;
        }
    } else {
        fn visit(item: &Value, out: &mut Vec<usize>) -> Result<()> {
            match item {
                Value::Object(obj) => {
                    for (key, v) in obj {
                        if matches!(key.as_str(), "type" | "value" | "rhs") && v.is_number() {
                            out.push(usize::try_from(
                                v.as_u64().ok_or("invalid expression reference")?,
                            )?);
                        } else {
                            visit(v, out)?;
                        }
                    }
                }
                Value::Array(items) => {
                    for v in items {
                        visit(v, out)?;
                    }
                }
                _ => {}
            }
            Ok(())
        }
        visit(item, &mut out)?;
    }
    Ok(out)
}

fn main() -> Result<()> {
    let path = std::env::args().nth(1).ok_or("expected export file")?;
    let sample_every = std::env::args()
        .nth(2)
        .map(|s| s.parse::<usize>())
        .transpose()?
        .unwrap_or(0);
    let start = Instant::now();
    let mut uses = Vec::<u32>::new();
    for line in BufReader::new(File::open(&path)?).lines() {
        let item: Value = serde_json::from_str(&line?)?;
        for id in references(&item)? {
            let count = uses.get_mut(id).ok_or("forward reference")?;
            *count = count.checked_add(1).ok_or("reference count overflow")?;
        }
        if let Some(id) = item.get("ie") {
            if id.as_u64() != Some(uses.len() as u64) {
                return Err("expected dense expression IDs".into());
            }
            uses.push(0);
        }
    }
    let scanned = start.elapsed().as_secs_f64();
    eprintln!(
        "{}",
        json!({"phase":"references_counted","expressions":uses.len(),"seconds":scanned})
    );
    let mut terms = Vec::<Option<Shared<Term>>>::with_capacity(uses.len());
    let mut retained = Vec::<Shared<Term>>::new();
    let unused = Name::<Term>::new("unused");
    let mut declarations = 0usize;
    let mut roundtrips = 0usize;
    for line in BufReader::new(File::open(path)?).lines() {
        let item: Value = serde_json::from_str(&line?)?;
        let get = |v: &Value| -> Result<Shared<Term>> {
            Ok(terms
                .get(v.as_u64().ok_or("invalid reference")? as usize)
                .and_then(Option::as_ref)
                .ok_or("released reference")?
                .clone())
        };
        let refs = references(&item)?;
        if item.get("ie").is_none() && !refs.is_empty() {
            declarations += 1;
            if sample_every != 0 && declarations.is_multiple_of(sample_every) {
                for id in &refs {
                    let root = terms[*id].as_ref().ok_or("released root")?;
                    if let Term::Binder(_, body) = &**root {
                        let (name, opened) = body.unbind_ref();
                        assert!(bind(name.clone(), opened.clone()).aeq(body));
                        assert!(body.instantiate(&Term::Var(name)).aeq(&opened));
                        roundtrips += 1;
                    }
                }
            }
        }
        if item.get("ie").is_some() {
            let term = graph::decode(&item, get)?;
            let closed = bind(unused.clone(), term.clone());
            assert!(closed.body().ptr_eq(&term));
            terms.push(if uses[terms.len()] == 0 {
                None
            } else {
                Some(term)
            });
            if terms.len().is_multiple_of(1_000_000) {
                eprintln!(
                    "{}",
                    json!({"expressions_loaded":terms.len(),"seconds":start.elapsed().as_secs_f64()})
                );
            }
        } else if let Some(d) = item.get("thm").or_else(|| item.get("opaque")) {
            retained.push(get(&d["type"])?);
        } else {
            for id in &refs {
                retained.push(get(&json!(id))?);
            }
        }
        for id in refs {
            uses[id] = uses[id].checked_sub(1).ok_or("reference count underflow")?;
            if uses[id] == 0 {
                terms[id] = None;
            }
        }
    }
    assert!(uses.iter().all(|&n| n == 0));
    assert!(terms.iter().all(Option::is_none));
    println!(
        "{}",
        json!({"status":"profiled_not_checked","expressions":terms.len(),"retained_roots":retained.len(),"sample_every":sample_every,"binding_roundtrips":roundtrips,"reference_scan_seconds":scanned,"total_seconds":start.elapsed().as_secs_f64(),"note":"binding graph only; releases export table slots at last serialized use; retains declaration types, definition bodies and recursor rules, but not theorem or opaque bodies; no type checking or payload/name/universe storage"})
    );
    Ok(())
}
