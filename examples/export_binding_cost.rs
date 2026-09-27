use serde_json::{Value, json};
use std::{
    collections::BTreeMap,
    fs::File,
    io::{BufRead, BufReader},
    time::Instant,
};
use unbound::prelude::*;

#[path = "support/graph.rs"]
mod graph;
use graph::Term;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let path = std::env::args().nth(1).ok_or("expected export file")?;
    let limit = std::env::args()
        .nth(2)
        .map(|n| n.parse::<usize>())
        .transpose()?
        .unwrap_or(usize::MAX);
    let mut terms = Vec::<Shared<Term>>::new();
    let mut kinds = BTreeMap::<String, usize>::new();
    let mut declarations = BTreeMap::<String, usize>::new();
    let mut total = 0;
    let start = Instant::now();
    for line in BufReader::new(File::open(path)?).lines() {
        let item: Value = serde_json::from_str(&line?)?;
        let Some(id) = item.get("ie") else {
            for kind in ["axiom", "def", "thm", "opaque", "quot"] {
                if item.get(kind).is_some() {
                    *declarations.entry(kind.into()).or_default() += 1;
                }
            }
            if let Some(block) = item.get("inductive") {
                for kind in ["types", "ctors", "recs"] {
                    *declarations.entry(format!("inductive.{kind}")).or_default() += block[kind]
                        .as_array()
                        .ok_or("invalid inductive array")?
                        .len();
                }
            }
            continue;
        };
        if id.as_u64() != Some(total as u64) {
            return Err("this profiler requires dense expression IDs".into());
        }
        let get = |v: &Value| -> Result<Shared<Term>, Box<dyn std::error::Error>> {
            Ok(terms
                .get(v.as_u64().ok_or("invalid reference")? as usize)
                .ok_or("unknown reference")?
                .clone())
        };
        let kind = item
            .as_object()
            .ok_or("expected object")?
            .keys()
            .find(|k| *k != "ie")
            .ok_or("missing node kind")?;
        *kinds.entry(kind.clone()).or_default() += 1;
        total += 1;
        if terms.len() >= limit {
            continue;
        }
        terms.push(graph::decode(&item, get)?);
        if terms.len().is_multiple_of(1_000_000) {
            eprintln!(
                "{}",
                json!({"expressions_loaded":terms.len(),"seconds":start.elapsed().as_secs_f64()})
            );
        }
    }
    let loaded = start.elapsed().as_secs_f64();
    let unused = Name::<Term>::new("unused");
    for term in &terms {
        let b = bind(unused.clone(), term.clone());
        assert!(b.body().ptr_eq(term));
    }
    println!(
        "{}",
        json!({
            "status":"profiled_not_checked", "expressions":terms.len(), "kinds":kinds,
            "export_expressions":total,"limited":terms.len()!=total,"declarations":declarations,
            "load_seconds":loaded,"total_seconds":start.elapsed().as_secs_f64(),
            "term_bytes":std::mem::size_of::<Term>(),
            "kernel_expr_bytes":std::mem::size_of::<nano_lean::Expr>(),
            "support_bytes":std::mem::size_of::<unbound::Support>(),
            "note":"binding graph only; constants, sorts and literals replaced by atoms; declaration, name and universe tables excluded"
        })
    );
    Ok(())
}
