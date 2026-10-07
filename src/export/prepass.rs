use super::json::{array, index, invalid, io, unsupported};
use super::{EXPRESSION, Kind, Result, current_format};
use serde_json::{Map, Value};
use std::io::BufRead;

const EXPRESSION_KINDS: [&str; 11] = [
    "bvar", "sort", "const", "app", "lam", "forallE", "letE", "mdata", "proj", "natVal", "strVal",
];
const TABLE_KEYS: [&str; 3] = ["meta", "in", "il"];

pub(super) fn references(item: &Value) -> Result<Vec<usize>> {
    let mut refs = Vec::new();
    let mut add = |v: &Value| -> Result<()> {
        refs.push(index(v)?);
        Ok(())
    };
    if item.get(EXPRESSION).is_some() {
        if let Some(a) = item.get("app") {
            add(&a["fn"])?;
            add(&a["arg"])?;
        } else if let Some(b) = item.get("lam").or_else(|| item.get("forallE")) {
            add(&b["type"])?;
            add(&b["body"])?;
        } else if let Some(b) = item.get("letE") {
            add(&b["type"])?;
            add(&b["value"])?;
            add(&b["body"])?;
        } else if let Some(m) = item.get("mdata") {
            add(&m["expr"])?;
        } else if let Some(p) = item.get("proj") {
            add(&p["struct"])?;
        }
        return Ok(refs);
    }
    for kind in Kind::ALL {
        let Some(d) = item.get(kind.key()) else {
            continue;
        };
        if kind == Kind::Inductive {
            for section in ["types", "ctors", "recs"] {
                for declaration in array(&d[section])? {
                    add(&declaration["type"])?;
                    if section == "recs" {
                        for rule in array(&declaration["rules"])? {
                            add(&rule["rhs"])?;
                        }
                    }
                }
            }
        } else {
            add(&d["type"])?;
            if kind.has_value() {
                add(&d["value"])?;
            }
        }
    }
    Ok(refs)
}

fn known(item: &Value, object: &Map<String, Value>, expressions: usize) -> Result<bool> {
    Ok(if item.get(EXPRESSION).is_some() {
        index(&item[EXPRESSION])? == expressions
            && EXPRESSION_KINDS.iter().any(|k| object.contains_key(*k))
    } else {
        TABLE_KEYS.iter().any(|k| object.contains_key(*k))
            || Kind::ALL.iter().any(|k| object.contains_key(k.key()))
    })
}

pub(super) fn count_uses(reader: impl BufRead) -> Result<Option<Vec<u32>>> {
    #[cfg(feature = "profile")]
    let _prepass = crate::profile::span("prepass");
    let mut counts = Vec::<u32>::new();
    for (line, text) in reader.lines().enumerate() {
        let text = text.map_err(io)?;
        let item: Value =
            serde_json::from_str(&text).map_err(|e| invalid(e.to_string()).at_line(line))?;
        let Some(obj) = item.as_object() else {
            return Ok(None);
        };
        if line == 0 && !current_format(&item) {
            return Ok(None);
        }
        if !known(&item, obj, counts.len())? {
            return Ok(None);
        }
        for id in references(&item)? {
            let n = counts
                .get_mut(id)
                .ok_or_else(|| invalid("unknown or forward expression reference"))?;
            *n = n
                .checked_add(1)
                .ok_or_else(|| unsupported("reference count overflow"))?;
        }
        if item.get(EXPRESSION).is_some() {
            counts.push(0);
        }
    }
    Ok(Some(counts))
}
