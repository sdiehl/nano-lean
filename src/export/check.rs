use super::json::{append, array, boolean, index, invalid, lookup, string, unsupported};
use super::prepass::references;
use super::{
    CheckPlan, EXPRESSION, ExportError, ExportReport, Kind, Result, TRACE_VAR, Trace,
    current_format,
};
use crate::Environment;
use crate::kernel::{Constructor, InductiveBlock, InductiveType, Recursor, RecursorRule};
use crate::kernel::{Expr, Level};
use crate::schema::{ExprKind, META, Ref};
use num_bigint::BigUint;
use serde_json::{Map, Value};
use sha2::Digest;
use std::collections::{BTreeSet, HashMap};
use std::io::BufRead;
use unbound::{Name, Shared, bind};

#[derive(Debug, Clone, Copy, thiserror::Error)]
enum Drift {
    #[error("expression indices changed between passes")]
    Indices,
    #[error("expression references changed between passes")]
    References,
}

impl From<Drift> for ExportError {
    fn from(d: Drift) -> Self {
        invalid(d.to_string())
    }
}

struct Tables {
    names: HashMap<usize, Vec<Value>>,
    levels: HashMap<usize, Level>,
    expressions: HashMap<usize, Shared<Expr>>,
}

impl Tables {
    fn new() -> Self {
        Self {
            names: HashMap::from([(0, Vec::new())]),
            levels: HashMap::from([(0, Level::Nat(0))]),
            expressions: HashMap::new(),
        }
    }

    fn name(&self, v: &Value) -> Result<String> {
        Ok(
            serde_json::to_string(lookup(&self.names, v)?)
                .expect("serializing strings cannot fail"),
        )
    }

    fn names(&self, v: &Value) -> Result<Vec<String>> {
        array(v)?.iter().map(|n| self.name(n)).collect()
    }

    fn level(&self, v: &Value) -> Result<Level> {
        lookup(&self.levels, v).cloned()
    }

    fn expr(&self, v: &Value) -> Result<Shared<Expr>> {
        lookup(&self.expressions, v).cloned()
    }

    fn owned(&self, v: &Value) -> Result<Expr> {
        Ok((**lookup(&self.expressions, v)?).clone())
    }

    fn add_name(&mut self, id: &Value, item: &Value) -> Result<()> {
        let prefix = |n: &Value| lookup(&self.names, &n["pre"]).cloned();
        let segments = if let Some(n) = item.get("str") {
            let mut segments = prefix(n)?;
            segments.push(Value::String(string(&n["str"])?.to_owned()));
            segments
        } else if let Some(n) = item.get("num") {
            let mut segments = prefix(n)?;
            n["i"]
                .as_u64()
                .ok_or_else(|| invalid("invalid numeric name"))?;
            segments.push(n["i"].clone());
            segments
        } else {
            return Err(invalid("unknown name entry"));
        };
        append(&mut self.names, id, segments)
    }

    fn add_level(&mut self, id: &Value, item: &Value) -> Result<()> {
        let level = if let Some(p) = item.get("param") {
            Level::Param(self.name(p)?)
        } else if let Some(s) = item.get("succ") {
            self.level(s)?.succ()?
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
                Level::imax(self.level(a)?, self.level(b)?)
            } else {
                Level::max(self.level(a)?, self.level(b)?)
            }
        };
        append(&mut self.levels, id, level)
    }

    fn expression(&self, item: &Value, object: &Map<String, Value>) -> Result<Shared<Expr>> {
        let e = |v| self.expr(v);
        let expr = if let Some(v) = item.get(ExprKind::BVar.key()) {
            Expr::Var(Name::bound(index(v)?, 0))
        } else if let Some(v) = item.get(ExprKind::NatVal.key()) {
            let digits = string(v)?;
            if digits.is_empty() || !digits.bytes().all(|c| c.is_ascii_digit()) {
                return Err(invalid("invalid natural literal"));
            }
            Expr::nat(
                BigUint::parse_bytes(digits.as_bytes(), 10)
                    .ok_or_else(|| invalid("invalid natural literal"))?,
            )
        } else if let Some(v) = item.get(ExprKind::StrVal.key()) {
            Expr::Str(string(v)?.to_owned())
        } else if let Some(u) = item.get(ExprKind::Sort.key()) {
            Expr::Sort(self.level(u)?)
        } else if let Some(c) = item.get(ExprKind::Const.key()) {
            Expr::Const(
                self.name(&c["name"])?,
                array(&c["us"])?
                    .iter()
                    .map(|u| self.level(u))
                    .collect::<Result<_>>()?,
            )
        } else if let Some(a) = item.get(ExprKind::App.key()) {
            Expr::App(e(&a["fn"])?, e(&a["arg"])?)
        } else if let Some(p) = item.get(ExprKind::Proj.key()) {
            Expr::Proj(
                self.name(&p["typeName"])?,
                index(&p["idx"])?,
                e(&p["struct"])?,
            )
        } else if let Some(b) = item
            .get(ExprKind::Lam.key())
            .or_else(|| item.get(ExprKind::ForallE.key()))
        {
            let ty = e(&b["type"])?;
            let body = bind(Name::new(self.name(&b["name"])?), e(&b["body"])?);
            if item.get(ExprKind::Lam.key()).is_some() {
                Expr::Lam(ty, body)
            } else {
                Expr::Pi(ty, body)
            }
        } else if let Some(b) = item.get(ExprKind::LetE.key()) {
            Expr::Let(
                e(&b["type"])?,
                e(&b["value"])?,
                bind(Name::new(self.name(&b["name"])?), e(&b["body"])?),
            )
        } else if let Some(m) = item.get(ExprKind::MData.key()) {
            return e(&m["expr"]);
        } else {
            return Err(unsupported(format!(
                "expression {}",
                object
                    .keys()
                    .find(|k| *k != EXPRESSION)
                    .map_or("<empty>", String::as_str)
            )));
        };
        Ok(Shared::new(expr))
    }
}

fn header(item: &Value) -> Result<()> {
    let object = item.as_object().ok_or_else(|| invalid("expected object"))?;
    if object.len() != 1 || item.get(META).is_none() {
        return Err(invalid("missing export metadata"));
    }
    if !current_format(item) {
        return Err(unsupported("export format version"));
    }
    Ok(())
}

fn safe(v: &Value) -> Result<()> {
    if boolean(&v["isUnsafe"])? {
        return Err(invalid(
            "unsafe inductive declaration is not permitted in a safe proof export",
        ));
    }
    Ok(())
}

struct Loader<'p> {
    tables: Tables,
    env: Environment,
    plan: &'p mut CheckPlan,
    counts: Option<Vec<u32>>,
    declarations: usize,
    expressions: usize,
    tracing: bool,
}

impl Loader<'_> {
    fn entry(&mut self, item: &Value, line: usize) -> Result<()> {
        let object = item.as_object().ok_or_else(|| invalid("expected object"))?;
        if let Some(id) = item.get(Ref::Name.key()) {
            if object.len() != 2 {
                return Err(invalid("malformed name entry"));
            }
            return self.tables.add_name(id, item);
        }
        if let Some(id) = item.get(Ref::Level.key()) {
            if object.len() != 2 {
                return Err(invalid("malformed level entry"));
            }
            return self.tables.add_level(id, item);
        }
        if let Some(id) = item.get(EXPRESSION) {
            if self.counts.is_some() && index(id)? != self.expressions {
                return Err(Drift::Indices.into());
            }
            if object.len() != 2 {
                return Err(invalid("malformed expression entry"));
            }
            let expr = self.tables.expression(item, object)?;
            return append(&mut self.tables.expressions, id, expr);
        }
        if object.len() != 1 {
            return Err(invalid("malformed declaration entry"));
        }
        let (key, d) = object.iter().next().expect("length checked above");
        #[cfg(feature = "profile")]
        let _declaration = crate::profile::span("declarations");
        if self.tracing {
            self.trace(line, key, d);
        }
        match Kind::of(key) {
            Some(Kind::Quot) => self.quotient(d),
            Some(Kind::Inductive) => self.inductive(d),
            Some(kind) => self.definition(kind, d),
            None => Err(unsupported(format!("declaration kind {key}"))),
        }
    }

    fn trace(&self, line: usize, key: &str, d: &Value) {
        let n = if key == Kind::Inductive.key() {
            &d["types"][0]["name"]
        } else {
            &d["name"]
        };
        let trace = Trace {
            line: line + 1,
            checked: self.plan.shard.is_none().then_some(self.declarations),
            imported: self.declarations,
            shard: self.plan.shard.map(|(i, _)| i),
            assigned_checked: self.plan.assigned,
            kind: key.to_owned(),
            name: self.tables.name(n).ok(),
        };
        eprintln!(
            "{}",
            serde_json::to_string(&trace).expect("serializing a trace cannot fail")
        );
    }

    fn quotient(&mut self, d: &Value) -> Result<()> {
        let t = &self.tables;
        let params = t.names(&d["levelParams"])?;
        let ty = t.owned(&d["type"])?;
        self.env
            .declare_quotient(t.name(&d["name"])?, params, ty, string(&d["kind"])?)?;
        self.declarations += 1;
        Ok(())
    }

    fn inductive(&mut self, d: &Value) -> Result<()> {
        let t = &self.tables;
        let types = array(&d["types"])?
            .iter()
            .map(|v| -> Result<_> {
                safe(v)?;
                Ok(InductiveType {
                    name: t.name(&v["name"])?,
                    params: t.names(&v["levelParams"])?,
                    ty: t.owned(&v["type"])?,
                    all: t.names(&v["all"])?,
                    constructors: t.names(&v["ctors"])?,
                    num_params: index(&v["numParams"])?,
                    num_indices: index(&v["numIndices"])?,
                    num_nested: index(&v["numNested"])?,
                    recursive: boolean(&v["isRec"])?,
                    reflexive: boolean(&v["isReflexive"])?,
                })
            })
            .collect::<Result<Vec<_>>>()?;
        let constructors = array(&d["ctors"])?
            .iter()
            .map(|c| -> Result<_> {
                safe(c)?;
                Ok(Constructor {
                    name: t.name(&c["name"])?,
                    params: t.names(&c["levelParams"])?,
                    ty: t.owned(&c["type"])?,
                    inductive: t.name(&c["induct"])?,
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
                    name: t.name(&r["name"])?,
                    params: t.names(&r["levelParams"])?,
                    ty: t.owned(&r["type"])?,
                    all: t.names(&r["all"])?,
                    num_params: index(&r["numParams"])?,
                    num_indices: index(&r["numIndices"])?,
                    num_motives: index(&r["numMotives"])?,
                    num_minors: index(&r["numMinors"])?,
                    k: boolean(&r["k"])?,
                    rules: array(&r["rules"])?
                        .iter()
                        .map(|rule| -> Result<_> {
                            Ok(RecursorRule {
                                constructor: t.name(&rule["ctor"])?,
                                num_fields: index(&rule["nfields"])?,
                                rhs: t.owned(&rule["rhs"])?,
                            })
                        })
                        .collect::<Result<_>>()?,
                })
            })
            .collect::<Result<Vec<_>>>()?;
        let declarations = types.len() + constructors.len() + recursors.len();
        self.env.declare_inductive(&InductiveBlock {
            types,
            constructors,
            recursors,
        })?;
        self.declarations += declarations;
        Ok(())
    }

    fn definition(&mut self, kind: Kind, d: &Value) -> Result<()> {
        match kind {
            Kind::Def => match string(&d["safety"])? {
                "safe" => {}
                "unsafe" | "partial" => {
                    return Err(invalid(
                        "unsafe or partial definition is not permitted in a safe proof export",
                    ));
                }
                _ => return Err(invalid("invalid definition safety")),
            },
            Kind::Thm => {}
            _ if boolean(&d["isUnsafe"])? => {
                return Err(invalid(
                    "unsafe declaration is not permitted in a safe proof export",
                ));
            }
            _ => {}
        }
        let t = &self.tables;
        if let Some(all) = d.get("all") {
            // Group metadata never permits forward references, so order is still enforced.
            let members = array(all)?
                .iter()
                .map(|n| t.name(n))
                .collect::<Result<Vec<_>>>()?;
            let own = t.name(&d["name"])?;
            if !members.contains(&own)
                || members.iter().collect::<BTreeSet<_>>().len() != members.len()
            {
                return Err(invalid("invalid declaration group metadata"));
            }
        }
        let n = t.name(&d["name"])?;
        let params = t.names(&d["levelParams"])?;
        let ty = t.owned(&d["type"])?;
        let value = if kind == Kind::Axiom {
            None
        } else {
            Some(t.owned(&d["value"])?)
        };
        let plan = &mut *self.plan;
        let assigned = plan.shard.is_none_or(|(i, n)| plan.ordinary % n == i);
        plan.ordinary += 1;
        if !assigned {
            self.env.assume_export_declaration(
                n,
                params,
                ty,
                value,
                matches!(kind, Kind::Def | Kind::Thm),
            )?;
        } else if kind == Kind::Thm {
            self.env
                .declare_theorem(n, params, ty, value.expect("theorems carry a value"))?;
        } else {
            self.env.declare(n, params, ty, value, kind == Kind::Def)?;
        }
        if assigned {
            plan.assigned += 1;
        }
        self.declarations += 1;
        Ok(())
    }

    fn release(&mut self, item: &Value) -> Result<()> {
        if item.get(EXPRESSION).is_some() {
            self.expressions += 1;
        }
        let Some(counts) = &mut self.counts else {
            return Ok(());
        };
        for id in references(item)? {
            let n = counts.get_mut(id).ok_or(Drift::References)?;
            *n = n.checked_sub(1).ok_or(Drift::References)?;
            if *n == 0 {
                self.tables.expressions.remove(&id);
            }
        }
        if let Some(id) = item.get(EXPRESSION) {
            let id = index(id)?;
            let n = counts.get(id).ok_or(Drift::Indices)?;
            if *n == 0 {
                self.tables.expressions.remove(&id);
            }
        }
        Ok(())
    }

    fn finish(self) -> Result<ExportReport> {
        if let Some(counts) = self.counts
            && (counts.len() != self.expressions || counts.iter().any(|&n| n != 0))
        {
            return Err(Drift::References.into());
        }
        Ok(ExportReport {
            declarations: self.declarations,
            expressions: self.expressions,
            names: self.tables.names.len(),
            levels: self.tables.levels.len(),
        })
    }
}

pub(super) fn run(
    mut reader: impl BufRead,
    counts: Option<Vec<u32>>,
    plan: &mut CheckPlan,
) -> Result<ExportReport> {
    let mut loader = Loader {
        tables: Tables::new(),
        env: Environment::new(),
        plan,
        counts,
        declarations: 0,
        expressions: 0,
        tracing: std::env::var_os(TRACE_VAR).is_some(),
    };
    let mut metadata = false;
    let mut text = String::new();
    for line in 0.. {
        text.clear();
        if reader.read_line(&mut text)? == 0 {
            break;
        }
        if loader.plan.shard.is_some() {
            loader.plan.digest.update(text.as_bytes());
        }
        let item: Value =
            serde_json::from_str(&text).map_err(|e| ExportError::from(e).at("line", line))?;
        let result = if metadata {
            loader.entry(&item, line)
        } else {
            header(&item)
        };
        result.map_err(|e| e.at("line", line))?;
        metadata = true;
        loader.release(&item)?;
    }
    if !metadata {
        return Err(invalid("empty export"));
    }
    loader.finish()
}
