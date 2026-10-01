use crate::kernel::{Constructor, InductiveBlock, InductiveType, Recursor, RecursorRule};
use crate::{Environment, Error, Expr, Level};
use serde_json::{Value, json};
use std::{
    collections::HashMap,
    fs::File,
    io::{BufRead, BufReader, Seek},
    path::Path,
};
use unbound::{Name, Shared, bind};

#[derive(Debug)]
pub enum ExportError {
    Invalid(String),
    Unsupported(String),
}
impl std::fmt::Display for ExportError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Invalid(s) => write!(f, "invalid export: {s}"),
            Self::Unsupported(s) => write!(f, "unsupported: {s}"),
        }
    }
}
impl std::error::Error for ExportError {}
impl From<Error> for ExportError {
    fn from(e: Error) -> Self {
        if e.0.contains("budget exhausted") || e.0.starts_with("unsupported:") {
            Self::Unsupported(e.0)
        } else {
            Self::Invalid(e.0)
        }
    }
}
type Result<T> = std::result::Result<T, ExportError>;
fn invalid(s: impl Into<String>) -> ExportError {
    ExportError::Invalid(s.into())
}
fn index(v: &Value) -> Result<usize> {
    v.as_u64()
        .and_then(|n| usize::try_from(n).ok())
        .ok_or_else(|| invalid("expected nonnegative index"))
}
fn array(v: &Value) -> Result<&[Value]> {
    v.as_array()
        .map(Vec::as_slice)
        .ok_or_else(|| invalid("expected array"))
}
fn string(v: &Value) -> Result<&str> {
    v.as_str().ok_or_else(|| invalid("expected string"))
}
fn boolean(v: &Value) -> Result<bool> {
    v.as_bool().ok_or_else(|| invalid("expected boolean"))
}
fn get<T: Clone>(items: &HashMap<usize, T>, v: &Value) -> Result<T> {
    items
        .get(&index(v)?)
        .cloned()
        .ok_or_else(|| invalid("unknown or forward reference"))
}
fn append<T>(items: &mut HashMap<usize, T>, id: &Value, value: T) -> Result<()> {
    let id = index(id)?;
    if items.contains_key(&id) {
        return Err(invalid("duplicate index"));
    }
    items.insert(id, value);
    Ok(())
}

#[derive(Debug)]
pub struct ExportReport {
    pub declarations: usize,
    pub expressions: usize,
    pub names: usize,
    pub levels: usize,
}
impl ExportReport {
    pub fn json(&self) -> Value {
        json!({"status":"checked", "declarations":self.declarations,"expressions":self.expressions,"names":self.names,"levels":self.levels})
    }
}

pub fn check_export(reader: impl BufRead) -> Result<ExportReport> {
    check_with_counts(reader, None)
}

pub fn check_export_file(path: impl AsRef<Path>) -> Result<ExportReport> {
    let file = File::open(path).map_err(|e| invalid(e.to_string()))?;
    let mut reader = BufReader::new(file);
    let counts = count_uses(&mut reader)?;
    reader.rewind().map_err(|e| invalid(e.to_string()))?;
    check_with_counts(reader, counts)
}

fn references(item: &Value) -> Result<Vec<usize>> {
    let mut refs = Vec::new();
    let mut add = |v: &Value| -> Result<()> {
        refs.push(index(v)?);
        Ok(())
    };
    if item.get("ie").is_some() {
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
    } else {
        for kind in ["axiom", "def", "thm", "opaque", "quot"] {
            if let Some(d) = item.get(kind) {
                add(&d["type"])?;
                if kind != "axiom" && kind != "quot" {
                    add(&d["value"])?;
                }
            }
        }
        if let Some(d) = item.get("inductive") {
            for kind in ["types", "ctors", "recs"] {
                for declaration in array(&d[kind])? {
                    add(&declaration["type"])?;
                    if kind == "recs" {
                        for rule in array(&declaration["rules"])? {
                            add(&rule["rhs"])?;
                        }
                    }
                }
            }
        }
    }
    Ok(refs)
}

fn count_uses(reader: impl BufRead) -> Result<Option<Vec<u32>>> {
    let mut counts = Vec::<u32>::new();
    for (line, text) in reader.lines().enumerate() {
        let text = text.map_err(|e| invalid(e.to_string()))?;
        let item: Value =
            serde_json::from_str(&text).map_err(|e| invalid(format!("line {}: {e}", line + 1)))?;
        let Some(obj) = item.as_object() else {
            return Ok(None);
        };
        if line == 0 && item["meta"]["format"]["version"] != "3.1.0" {
            return Ok(None);
        }
        if item.get("ie").is_some() {
            if index(&item["ie"])? != counts.len()
                || ![
                    "bvar", "sort", "const", "app", "lam", "forallE", "letE", "mdata", "proj",
                    "natVal", "strVal",
                ]
                .iter()
                .any(|k| obj.contains_key(*k))
            {
                return Ok(None);
            }
        } else if ![
            "meta",
            "in",
            "il",
            "axiom",
            "def",
            "thm",
            "opaque",
            "inductive",
            "quot",
        ]
        .iter()
        .any(|k| obj.contains_key(*k))
        {
            return Ok(None);
        }
        for id in references(&item)? {
            let n = counts
                .get_mut(id)
                .ok_or_else(|| invalid("unknown or forward expression reference"))?;
            *n = n
                .checked_add(1)
                .ok_or_else(|| ExportError::Unsupported("reference count overflow".into()))?;
        }
        if item.get("ie").is_some() {
            counts.push(0);
        }
    }
    Ok(Some(counts))
}

fn check_with_counts(reader: impl BufRead, mut counts: Option<Vec<u32>>) -> Result<ExportReport> {
    let mut names = HashMap::from([(0, Vec::<Value>::new())]);
    let mut levels = HashMap::from([(0, Level::Nat(0))]);
    let mut expressions = HashMap::<usize, Shared<Expr>>::new();
    let mut env = Environment::new();
    let mut count = 0;
    let mut expression_count = 0;
    let mut metadata = false;
    for (line, text) in reader.lines().enumerate() {
        let text = text.map_err(|e| invalid(e.to_string()))?;
        let item: Value =
            serde_json::from_str(&text).map_err(|e| invalid(format!("line {}: {e}", line + 1)))?;
        let result = (|| -> Result<()> {
            let object = item.as_object().ok_or_else(|| invalid("expected object"))?;
            if !metadata {
                if line != 0 || object.len() != 1 || item.get("meta").is_none() {
                    return Err(invalid("missing export metadata"));
                }
                if item["meta"]["format"]["version"] != "3.1.0" {
                    return Err(ExportError::Unsupported("export format version".into()));
                }
                metadata = true;
                return Ok(());
            }
            let name = |v: &Value| -> Result<String> {
                Ok(serde_json::to_string(&get(&names, v)?).unwrap())
            };
            if let Some(id) = item.get("in") {
                if object.len() != 2 {
                    return Err(invalid("malformed name entry"));
                }
                let mut segments;
                if let Some(n) = item.get("str") {
                    segments = get(&names, &n["pre"])?;
                    segments.push(Value::String(string(&n["str"])?.to_owned()));
                } else if let Some(n) = item.get("num") {
                    segments = get(&names, &n["pre"])?;
                    n["i"]
                        .as_u64()
                        .ok_or_else(|| invalid("invalid numeric name"))?;
                    segments.push(n["i"].clone());
                } else {
                    return Err(invalid("unknown name entry"));
                }
                return append(&mut names, id, segments);
            }
            if let Some(id) = item.get("il") {
                if object.len() != 2 {
                    return Err(invalid("malformed level entry"));
                }
                let level = if let Some(p) = item.get("param") {
                    Level::Param(name(p)?)
                } else if let Some(s) = item.get("succ") {
                    get(&levels, s)?.succ()?
                } else {
                    let (args, imax) = if let Some(a) = item.get("max") {
                        (a, false)
                    } else if let Some(a) = item.get("imax") {
                        (a, true)
                    } else {
                        return Err(invalid("unknown level entry"));
                    };
                    let [a, b] = array(args)? else {
                        return Err(invalid("level operator arity"));
                    };
                    if imax {
                        Level::imax(get(&levels, a)?, get(&levels, b)?)
                    } else {
                        Level::max(get(&levels, a)?, get(&levels, b)?)
                    }
                };
                return append(&mut levels, id, level);
            }
            if let Some(id) = item.get("ie") {
                if counts.is_some() && index(id)? != expression_count {
                    return Err(invalid("expression indices changed between passes"));
                }
                if object.len() != 2 {
                    return Err(invalid("malformed expression entry"));
                }
                let e = |v| get(&expressions, v);
                let expr = if let Some(v) = item.get("bvar") {
                    Expr::Var(Name::bound(index(v)?, 0))
                } else if let Some(v) = item.get("natVal") {
                    let digits = string(v)?;
                    if digits.is_empty() || !digits.bytes().all(|c| c.is_ascii_digit()) {
                        return Err(invalid("invalid natural literal"));
                    }
                    Expr::nat(
                        num_bigint::BigUint::parse_bytes(digits.as_bytes(), 10)
                            .ok_or_else(|| invalid("invalid natural literal"))?,
                    )
                } else if let Some(v) = item.get("strVal") {
                    Expr::Str(string(v)?.to_owned())
                } else if let Some(u) = item.get("sort") {
                    Expr::Sort(get(&levels, u)?)
                } else if let Some(c) = item.get("const") {
                    Expr::Const(
                        name(&c["name"])?,
                        array(&c["us"])?
                            .iter()
                            .map(|u| get(&levels, u))
                            .collect::<Result<_>>()?,
                    )
                } else if let Some(a) = item.get("app") {
                    Expr::App(e(&a["fn"])?, e(&a["arg"])?)
                } else if let Some(p) = item.get("proj") {
                    Expr::Proj(name(&p["typeName"])?, index(&p["idx"])?, e(&p["struct"])?)
                } else if let Some(b) = item.get("lam").or_else(|| item.get("forallE")) {
                    let ty = e(&b["type"])?;
                    let body = bind(Name::new(name(&b["name"])?), e(&b["body"])?);
                    if item.get("lam").is_some() {
                        Expr::Lam(ty, body)
                    } else {
                        Expr::Pi(ty, body)
                    }
                } else if let Some(b) = item.get("letE") {
                    Expr::Let(
                        e(&b["type"])?,
                        e(&b["value"])?,
                        bind(Name::new(name(&b["name"])?), e(&b["body"])?),
                    )
                } else if let Some(m) = item.get("mdata") {
                    let value = e(&m["expr"])?;
                    return append(&mut expressions, id, value);
                } else {
                    return Err(ExportError::Unsupported(format!(
                        "expression {}",
                        object.keys().find(|k| *k != "ie").unwrap()
                    )));
                };
                return append(&mut expressions, id, Shared::new(expr));
            }
            if object.len() != 1 {
                return Err(invalid("malformed declaration entry"));
            }
            let (kind, d) = object.iter().next().unwrap();
            if kind == "quot" {
                let params = array(&d["levelParams"])?
                    .iter()
                    .map(name)
                    .collect::<Result<_>>()?;
                let ty = (*get(&expressions, &d["type"])?).clone();
                env.declare_quotient(name(&d["name"])?, params, ty, string(&d["kind"])?)?;
                count += 1;
                return Ok(());
            }
            if kind == "inductive" {
                let names_of =
                    |v: &Value| -> Result<Vec<String>> { array(v)?.iter().map(name).collect() };
                let expr = |v: &Value| -> Result<Expr> { Ok((*get(&expressions, v)?).clone()) };
                let safe = |v: &Value| -> Result<()> {
                    if boolean(&v["isUnsafe"])? {
                        return Err(invalid(
                            "unsafe inductive declaration is not permitted in a safe proof export",
                        ));
                    }
                    Ok(())
                };
                let types = array(&d["types"])?
                    .iter()
                    .map(|t| -> Result<_> {
                        safe(t)?;
                        Ok(InductiveType {
                            name: name(&t["name"])?,
                            params: names_of(&t["levelParams"])?,
                            ty: expr(&t["type"])?,
                            all: names_of(&t["all"])?,
                            constructors: names_of(&t["ctors"])?,
                            num_params: index(&t["numParams"])?,
                            num_indices: index(&t["numIndices"])?,
                            num_nested: index(&t["numNested"])?,
                            recursive: boolean(&t["isRec"])?,
                            reflexive: boolean(&t["isReflexive"])?,
                        })
                    })
                    .collect::<Result<Vec<_>>>()?;
                let constructors = array(&d["ctors"])?
                    .iter()
                    .map(|c| -> Result<_> {
                        safe(c)?;
                        Ok(Constructor {
                            name: name(&c["name"])?,
                            params: names_of(&c["levelParams"])?,
                            ty: expr(&c["type"])?,
                            inductive: name(&c["induct"])?,
                            index: index(&c["cidx"])?,
                            num_params: index(&c["numParams"])?,
                            num_fields: index(&c["numFields"])?,
                        })
                    })
                    .collect::<Result<Vec<_>>>()?;
                let recursors = array(&d["recs"])?
                    .iter()
                    .map(|r| -> Result<_> {
                        safe(r)?;
                        Ok(Recursor {
                            name: name(&r["name"])?,
                            params: names_of(&r["levelParams"])?,
                            ty: expr(&r["type"])?,
                            all: names_of(&r["all"])?,
                            num_params: index(&r["numParams"])?,
                            num_indices: index(&r["numIndices"])?,
                            num_motives: index(&r["numMotives"])?,
                            num_minors: index(&r["numMinors"])?,
                            k: boolean(&r["k"])?,
                            rules: array(&r["rules"])?
                                .iter()
                                .map(|rule| -> Result<_> {
                                    Ok(RecursorRule {
                                        constructor: name(&rule["ctor"])?,
                                        num_fields: index(&rule["nfields"])?,
                                        rhs: expr(&rule["rhs"])?,
                                    })
                                })
                                .collect::<Result<_>>()?,
                        })
                    })
                    .collect::<Result<Vec<_>>>()?;
                let declarations = types.len() + constructors.len() + recursors.len();
                env.declare_inductive(InductiveBlock {
                    types,
                    constructors,
                    recursors,
                })?;
                count += declarations;
                return Ok(());
            }
            if !matches!(kind.as_str(), "axiom" | "def" | "thm" | "opaque") {
                return Err(ExportError::Unsupported(format!("declaration kind {kind}")));
            }
            if kind == "def" {
                match string(&d["safety"])? {
                    "safe" => {}
                    "unsafe" | "partial" => {
                        return Err(invalid(
                            "unsafe or partial definition is not permitted in a safe proof export",
                        ));
                    }
                    _ => return Err(invalid("invalid definition safety")),
                }
            } else if kind != "thm" && boolean(&d["isUnsafe"])? {
                return Err(invalid(
                    "unsafe declaration is not permitted in a safe proof export",
                ));
            }
            if let Some(all) = d.get("all") {
                let all = array(all)?;
                if all.len() != 1 || all[0] != d["name"] {
                    return Err(ExportError::Unsupported("mutual declaration block".into()));
                }
            }
            let n = name(&d["name"])?;
            let params = array(&d["levelParams"])?
                .iter()
                .map(name)
                .collect::<Result<_>>()?;
            let ty = (*get(&expressions, &d["type"])?).clone();
            let value = if kind == "axiom" {
                None
            } else {
                Some((*get(&expressions, &d["value"])?).clone())
            };
            if kind == "thm" {
                env.declare_theorem(n, params, ty, value.unwrap())?;
            } else {
                env.declare(n, params, ty, value, kind == "def")?;
            }
            count += 1;
            Ok(())
        })();
        result.map_err(|e| match e {
            ExportError::Invalid(s) => invalid(format!("line {}: {s}", line + 1)),
            ExportError::Unsupported(s) => {
                ExportError::Unsupported(format!("line {}: {s}", line + 1))
            }
        })?;
        if item.get("ie").is_some() {
            expression_count += 1;
        }
        if let Some(counts) = &mut counts {
            for id in references(&item)? {
                let n = counts
                    .get_mut(id)
                    .ok_or_else(|| invalid("expression references changed between passes"))?;
                *n = n
                    .checked_sub(1)
                    .ok_or_else(|| invalid("expression references changed between passes"))?;
                if *n == 0 {
                    expressions.remove(&id);
                }
            }
            if let Some(id) = item.get("ie") {
                let id = index(id)?;
                let n = counts
                    .get(id)
                    .ok_or_else(|| invalid("expression indices changed between passes"))?;
                if *n == 0 {
                    expressions.remove(&id);
                }
            }
        }
    }
    if !metadata {
        return Err(invalid("empty export"));
    }
    if let Some(counts) = counts
        && (counts.len() != expression_count || counts.iter().any(|&n| n != 0))
    {
        return Err(invalid("expression references changed between passes"));
    }
    Ok(ExportReport {
        declarations: count,
        expressions: expression_count,
        names: names.len(),
        levels: levels.len(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Cursor;

    #[test]
    fn projection_prepass_counts_only_the_structure_expression() {
        let input = concat!(
            "{\"meta\":{\"format\":{\"version\":\"3.1.0\"}}}\n",
            "{\"in\":100,\"str\":{\"pre\":0,\"str\":\"S\"}}\n",
            "{\"ie\":0,\"bvar\":0}\n",
            "{\"ie\":1,\"proj\":{\"typeName\":100,\"idx\":2,\"struct\":0}}\n",
            "{\"ie\":2,\"proj\":{\"typeName\":100,\"idx\":3,\"struct\":0}}\n",
        );
        let counts = count_uses(Cursor::new(input)).unwrap().unwrap();
        assert_eq!(counts, [2, 0, 0]);
        let reclaimed = check_with_counts(Cursor::new(input), Some(counts)).unwrap();
        let stream = check_export(Cursor::new(input)).unwrap();
        assert_eq!(reclaimed.json(), stream.json());
    }

    #[test]
    fn inductive_prepass_keeps_declaration_roots_alive() {
        let input = include_str!("../tests/fixtures/inductive-boundaries.ndjson");
        let counts = count_uses(Cursor::new(input)).unwrap().unwrap();
        assert_eq!(counts.len(), 67);
        for root in [6, 17, 36, 45, 46, 50, 62, 66] {
            assert_eq!(counts[root], 1, "declaration root {root}");
        }
        let reclaimed = check_with_counts(Cursor::new(input), Some(counts)).unwrap();
        assert_eq!(reclaimed.declarations, 6);
        assert_eq!(
            reclaimed.json(),
            check_export(Cursor::new(input)).unwrap().json()
        );
    }

    #[test]
    fn primitive_prepass_handles_literals_and_quotient_signature_roots() {
        let input = include_str!("../tests/fixtures/primitives.ndjson");
        let input = format!("{input}{{\"ie\":460,\"strVal\":\"水🦀\"}}\n");
        let counts = count_uses(Cursor::new(&input)).unwrap().unwrap();
        assert_eq!(counts.len(), 461);
        let reclaimed = check_with_counts(Cursor::new(&input), Some(counts)).unwrap();
        assert_eq!(reclaimed.declarations, 35);
        assert_eq!(
            reclaimed.json(),
            check_export(Cursor::new(input)).unwrap().json()
        );
    }
}
