pub use crate::schema::Ref;
use crate::schema::{ExprKind, META};
use serde_json::{Value, json};
use std::collections::{BTreeMap, BTreeSet};

pub fn defines(entry: &Value) -> Option<(Ref, u64)> {
    Ref::ALL
        .into_iter()
        .find_map(|r| Some((r, entry.get(r.key())?.as_u64()?)))
}

pub fn is_declaration(entry: &Value) -> bool {
    defines(entry).is_none() && entry.get(META).is_none()
}

pub fn id_at(line: &Value, ptr: &str) -> u64 {
    line.pointer(ptr)
        .and_then(Value::as_u64)
        .expect("refs point at ids")
}

pub fn refs(entry: &Value) -> Vec<(Ref, String)> {
    use Ref::{Expr, Level, Name};
    let mut out = Vec::new();
    let mut at = |kind: Ref, ptr: String| match entry.pointer(&ptr) {
        Some(Value::Array(items)) => {
            out.extend((0..items.len()).map(|i| (kind, format!("{ptr}/{i}"))));
        }
        Some(Value::Number(_)) => out.push((kind, ptr)),
        _ => {}
    };
    match defines(entry) {
        Some((Name, _)) => {
            at(Name, "/str/pre".into());
            at(Name, "/num/pre".into());
        }
        Some((Level, _)) => {
            for k in ["succ", "max", "imax"] {
                at(Level, format!("/{k}"));
            }
            at(Name, "/param".into());
        }
        Some((Expr, _)) => {
            at(Level, "/sort".into());
            at(Name, "/const/name".into());
            at(Level, "/const/us".into());
            at(Expr, "/app/fn".into());
            at(Expr, "/app/arg".into());
            for b in [
                ExprKind::Lam.key(),
                ExprKind::ForallE.key(),
                ExprKind::LetE.key(),
            ] {
                at(Name, format!("/{b}/name"));
                for k in ["type", "value", "body"] {
                    at(Expr, format!("/{b}/{k}"));
                }
            }
            at(Name, "/proj/typeName".into());
            at(Expr, "/proj/struct".into());
            at(Expr, "/mdata/expr".into());
        }
        None => {
            let Some((kind, body)) = entry.as_object().and_then(|o| o.iter().next()) else {
                return out;
            };
            let mut decl = |prefix: String, body: &Value| {
                for k in ["name", "levelParams", "all", "ctors", "induct"] {
                    at(Name, format!("{prefix}/{k}"));
                }
                at(Expr, format!("{prefix}/type"));
                at(Expr, format!("{prefix}/value"));
                for i in 0..body["rules"].as_array().map_or(0, Vec::len) {
                    at(Name, format!("{prefix}/rules/{i}/ctor"));
                    at(Expr, format!("{prefix}/rules/{i}/rhs"));
                }
            };
            if kind == "inductive" {
                for section in ["types", "ctors", "recs"] {
                    for (i, item) in body[section].as_array().into_iter().flatten().enumerate() {
                        decl(format!("/inductive/{section}/{i}"), item);
                    }
                }
            } else if kind != META {
                decl(format!("/{kind}"), body);
            }
        }
    }
    out
}

pub fn compact(lines: &[Value], pin: Option<usize>) -> (Vec<Value>, Option<usize>) {
    let mut live: BTreeSet<(Ref, u64)> = BTreeSet::new();
    for (i, line) in lines.iter().enumerate().rev() {
        let keep = match defines(line) {
            Some(d) => pin == Some(i) || live.contains(&d),
            None => true,
        };
        if keep {
            for (kind, ptr) in refs(line) {
                live.insert((kind, id_at(line, &ptr)));
            }
        }
    }
    let mut map: BTreeMap<(Ref, u64), u64> = [((Ref::Name, 0), 0), ((Ref::Level, 0), 0)].into();
    let mut next = BTreeMap::from([(Ref::Name, 1), (Ref::Level, 1), (Ref::Expr, 0)]);
    let (mut out, mut moved) = (Vec::new(), None);
    for (i, line) in lines.iter().enumerate() {
        let mut line = line.clone();
        if let Some((kind, id)) = defines(&line) {
            let pinned = pin == Some(i);
            if !pinned && (!live.contains(&(kind, id)) || map.contains_key(&(kind, id))) {
                continue;
            }
            let counter = next.entry(kind).or_default();
            let fresh = *counter;
            *counter += 1;
            map.entry((kind, id)).or_insert(fresh);
            line[kind.key()] = json!(fresh);
        }
        for (kind, ptr) in refs(&line) {
            let slot = line.pointer_mut(&ptr).expect("refs point at ids");
            if let Some(&n) = map.get(&(kind, slot.as_u64().expect("refs point at ids"))) {
                *slot = json!(n);
            }
        }
        if pin == Some(i) {
            moved = Some(out.len());
        }
        out.push(line);
    }
    (out, moved)
}
