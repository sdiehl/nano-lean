use super::json::{array, index, invalid, unsupported};
use super::{EXPRESSION, ExportError, Kind, Result, current_format};
use crate::schema::{ExprKind, META, Ref};
use serde_json::{Map, Value};
use std::io::BufRead;

pub(super) fn references(item: &Value) -> Result<Vec<usize>> {
    let mut refs = Vec::new();
    let mut add = |v: &Value| -> Result<()> {
        refs.push(index(v)?);
        Ok(())
    };
    if item.get(EXPRESSION).is_some() {
        if let Some(a) = item.get(ExprKind::App.key()) {
            add(&a["fn"])?;
            add(&a["arg"])?;
        } else if let Some(b) = item
            .get(ExprKind::Lam.key())
            .or_else(|| item.get(ExprKind::ForallE.key()))
        {
            add(&b["type"])?;
            add(&b["body"])?;
        } else if let Some(b) = item.get(ExprKind::LetE.key()) {
            add(&b["type"])?;
            add(&b["value"])?;
            add(&b["body"])?;
        } else if let Some(m) = item.get(ExprKind::MData.key()) {
            add(&m["expr"])?;
        } else if let Some(p) = item.get(ExprKind::Proj.key()) {
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
            && ExprKind::ALL.iter().any(|k| object.contains_key(k.key()))
    } else {
        object.contains_key(META)
            || [Ref::Name, Ref::Level]
                .iter()
                .any(|k| object.contains_key(k.key()))
            || Kind::ALL.iter().any(|k| object.contains_key(k.key()))
    })
}

pub(super) fn count_uses(reader: impl BufRead) -> Result<Option<Vec<u32>>> {
    #[cfg(feature = "profile")]
    let _prepass = crate::profile::span("prepass");
    let mut counts = Vec::<u32>::new();
    for (line, text) in reader.lines().enumerate() {
        let text = text?;
        let item: Value =
            serde_json::from_str(&text).map_err(|e| ExportError::from(e).at("line", line))?;
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
