use super::table::{Ref, defines, is_declaration, refs};
use super::{Edit, Expect, Mutant};
use num_bigint::BigUint;
use serde_json::{Value, json};
use std::collections::BTreeMap;
use std::fmt;
use std::str::FromStr;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Operator {
    LooseBvar,
    DanglingRef,
    DuplicateDecl,
    InductiveCount,
    InductiveFlag,
    Unsafe,
    Reorder,
    DropDecl,
    SwapDecls,
    RetargetExpr,
    Unfold,
    LevelOp,
    NatLiteral,
    Hints,
    ThmToDef,
}

impl Operator {
    pub const ALL: [Self; 15] = [
        Self::LooseBvar,
        Self::DanglingRef,
        Self::DuplicateDecl,
        Self::InductiveCount,
        Self::InductiveFlag,
        Self::Unsafe,
        Self::Reorder,
        Self::DropDecl,
        Self::SwapDecls,
        Self::RetargetExpr,
        Self::Unfold,
        Self::LevelOp,
        Self::NatLiteral,
        Self::Hints,
        Self::ThmToDef,
    ];

    pub fn name(self) -> &'static str {
        match self {
            Self::LooseBvar => "loose-bvar",
            Self::DanglingRef => "dangling-ref",
            Self::DuplicateDecl => "duplicate-decl",
            Self::InductiveCount => "inductive-count",
            Self::InductiveFlag => "inductive-flag",
            Self::Unsafe => "unsafe",
            Self::Reorder => "reorder",
            Self::DropDecl => "drop-decl",
            Self::SwapDecls => "swap-decls",
            Self::RetargetExpr => "retarget-expr",
            Self::Unfold => "unfold",
            Self::LevelOp => "level-op",
            Self::NatLiteral => "nat-literal",
            Self::Hints => "hints",
            Self::ThmToDef => "thm-to-def",
        }
    }
}

impl fmt::Display for Operator {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.name())
    }
}

impl FromStr for Operator {
    type Err = String;

    fn from_str(name: &str) -> Result<Self, String> {
        Self::ALL
            .into_iter()
            .find(|op| op.name() == name)
            .ok_or_else(|| format!("unknown operator {name}"))
    }
}

const COUNTS: &[&str] = &[
    "numParams",
    "numIndices",
    "numNested",
    "numFields",
    "numMotives",
    "numMinors",
    "nfields",
    "cidx",
];
const FLAGS: &[&str] = &["k", "isRec", "isReflexive"];

fn walk(v: &Value, ptr: &mut String, f: &mut impl FnMut(&str, &str, &Value)) {
    match v {
        Value::Object(o) => {
            for (k, child) in o {
                let len = ptr.len();
                ptr.push('/');
                ptr.push_str(k);
                f(ptr, k, child);
                walk(child, ptr, f);
                ptr.truncate(len);
            }
        }
        Value::Array(a) => {
            for (i, child) in a.iter().enumerate() {
                let len = ptr.len();
                ptr.push_str(&format!("/{i}"));
                walk(child, ptr, f);
                ptr.truncate(len);
            }
        }
        _ => {}
    }
}

fn same_type(lines: &[Value]) -> BTreeMap<u64, Vec<u64>> {
    let exprs = expressions(lines);
    let former = |mut ty: u64| loop {
        match exprs.get(&ty) {
            Some(e) if e.get("sort").is_some() => return true,
            Some(e) if e.get("forallE").is_some() => ty = e["forallE"]["body"].as_u64().unwrap(),
            _ => return false,
        }
    };
    let mut declared = BTreeMap::new();
    let mut note = |d: &Value| {
        if let (Some(name), Some(ty)) = (d["name"].as_u64(), d["type"].as_u64())
            && !former(ty)
        {
            declared.insert(name, format!("{ty}{}", d["levelParams"]));
        }
    };
    for line in lines.iter().filter(|l| is_declaration(l)) {
        let Some((kind, body)) = line.as_object().and_then(|o| o.iter().next()) else {
            continue;
        };
        if kind == "inductive" {
            ["types", "ctors", "recs"]
                .iter()
                .flat_map(|s| body[s].as_array().into_iter().flatten())
                .for_each(&mut note);
        } else {
            note(body);
        }
    }
    let mut classes: BTreeMap<String, Vec<u64>> = BTreeMap::new();
    for line in lines {
        let Some((Ref::Expr, id)) = defines(line) else {
            continue;
        };
        let class = if let Some(c) = line.get("const") {
            c["name"]
                .as_u64()
                .and_then(|n| declared.get(&n))
                .map(|ty| format!("{ty}{}", c["us"]))
        } else {
            ["natVal", "strVal"]
                .into_iter()
                .find(|k| line.get(k).is_some())
                .map(str::to_owned)
        };
        if let Some(class) = class {
            classes.entry(class).or_default().push(id);
        }
    }
    let mut out = BTreeMap::new();
    for ids in classes.into_values().filter(|ids| ids.len() > 1) {
        for &id in &ids {
            out.insert(id, ids.clone());
        }
    }
    out
}

fn expressions(lines: &[Value]) -> BTreeMap<u64, &Value> {
    lines
        .iter()
        .filter_map(|l| match defines(l) {
            Some((Ref::Expr, id)) => Some((id, l)),
            _ => None,
        })
        .collect()
}

/// `Nat` and `String` stay folded because kernels accelerate them by name.
fn bodies(lines: &[Value]) -> BTreeMap<u64, u64> {
    let mut root = BTreeMap::from([(0, String::new())]);
    for line in lines {
        let Some((Ref::Name, id)) = defines(line) else {
            continue;
        };
        let (pre, part) = match (line.get("str"), line.get("num")) {
            (Some(s), _) => (&s["pre"], s["str"].as_str().unwrap_or("").to_owned()),
            (_, Some(n)) => (&n["pre"], n["i"].to_string()),
            _ => continue,
        };
        let first = match pre.as_u64().and_then(|p| root.get(&p)) {
            Some(r) if !r.is_empty() => r.clone(),
            _ => part,
        };
        root.insert(id, first);
    }
    let mut out = BTreeMap::new();
    for line in lines {
        let d = match (line.get("def"), line.get("thm")) {
            (Some(d), _) if d["safety"] == "safe" && d["hints"] != "opaque" => d,
            (_, Some(t)) => t,
            _ => continue,
        };
        let name = d["name"].as_u64().unwrap();
        let accelerated = matches!(root.get(&name).map(String::as_str), Some("Nat" | "String"));
        if d["levelParams"].as_array().is_some_and(Vec::is_empty) && !accelerated {
            out.insert(name, d["value"].as_u64().unwrap());
        }
    }
    out
}

pub fn mutants(lines: &[Value], op: Operator) -> Vec<Mutant> {
    use Expect::*;
    let mut out = Vec::new();
    let mut push = |expect, edit| out.push(Mutant { op, expect, edit });
    let max = |kind| {
        lines
            .iter()
            .filter_map(defines)
            .filter(|(k, _)| *k == kind)
            .map(|(_, id)| id)
            .max()
            .unwrap_or(0)
    };
    let peers = if op == Operator::RetargetExpr {
        same_type(lines)
    } else {
        BTreeMap::new()
    };
    let (exprs, bodies) = if op == Operator::Unfold {
        (expressions(lines), bodies(lines))
    } else {
        Default::default()
    };
    let decls: Vec<usize> = (0..lines.len())
        .filter(|&i| is_declaration(&lines[i]))
        .collect();
    for (i, line) in lines.iter().enumerate() {
        let decl = is_declaration(line);
        match op {
            Operator::LooseBvar if line.get("bvar").is_some() => {
                push(Reject, Edit::Set(i, "/bvar".into(), json!(60_000)))
            }
            Operator::DanglingRef => {
                for (kind, ptr) in refs(line) {
                    let target = match defines(line) {
                        Some((k, id)) if k == kind => id,
                        _ => max(kind) + 1,
                    };
                    push(Reject, Edit::Set(i, ptr, json!(target)));
                }
            }
            Operator::DuplicateDecl if decl => push(Reject, Edit::Duplicate(i)),
            Operator::DropDecl if decl => push(Agree, Edit::Remove(i)),
            Operator::InductiveCount | Operator::InductiveFlag
                if line.get("inductive").is_some() =>
            {
                walk(line, &mut String::new(), &mut |ptr, key, v| {
                    if op == Operator::InductiveCount && COUNTS.contains(&key) {
                        let n = v.as_u64().unwrap();
                        push(Reject, Edit::Set(i, ptr.into(), json!(n + 1)));
                        if n > 0 {
                            push(Reject, Edit::Set(i, ptr.into(), json!(n - 1)));
                        }
                    } else if op == Operator::InductiveFlag && FLAGS.contains(&key) {
                        push(
                            Reject,
                            Edit::Set(i, ptr.into(), json!(!v.as_bool().unwrap())),
                        );
                    }
                });
            }
            Operator::Unsafe if decl => walk(line, &mut String::new(), &mut |ptr, key, v| {
                if key == "isUnsafe" && v == &json!(false) {
                    push(Reject, Edit::Set(i, ptr.into(), json!(true)));
                } else if key == "safety" {
                    push(Reject, Edit::Set(i, ptr.into(), json!("unsafe")));
                }
            }),
            Operator::Reorder if line.get("inductive").is_some() => {
                walk(line, &mut String::new(), &mut |ptr, key, v| {
                    if let Some(items) = v.as_array().filter(|a| a.len() > 1)
                        && matches!(key, "rules" | "ctors")
                        && !ptr.starts_with("/inductive/ctors")
                    {
                        let mut swapped = items.clone();
                        swapped.swap(0, 1);
                        push(Reject, Edit::Set(i, ptr.into(), Value::Array(swapped)));
                    }
                });
            }
            Operator::SwapDecls if decl => {
                if let Some(&next) = decls.iter().find(|&&j| j > i) {
                    push(Agree, Edit::Swap(i, next));
                }
            }
            Operator::RetargetExpr => {
                let bound = match defines(line) {
                    Some((Ref::Expr, id)) => id,
                    _ => u64::MAX,
                };
                for (kind, ptr) in refs(line) {
                    let old = line.pointer(&ptr).unwrap().as_u64().unwrap();
                    if kind != Ref::Expr {
                        continue;
                    }
                    for &new in peers.get(&old).into_iter().flatten() {
                        if new != old && new < bound {
                            push(Agree, Edit::Set(i, ptr.clone(), json!(new)));
                        }
                    }
                }
            }
            Operator::Unfold if line.get("const").is_some() => {
                let id = line["ie"].as_u64().unwrap();
                let body = line["const"]["name"].as_u64().and_then(|n| bodies.get(&n));
                if let Some(body) = body.and_then(|b| exprs.get(b)) {
                    let mut copy = (*body).clone();
                    copy["ie"] = json!(id);
                    if refs(&copy).iter().all(|(kind, ptr)| {
                        *kind != Ref::Expr || copy.pointer(ptr).unwrap().as_u64().unwrap() < id
                    }) {
                        push(Same, Edit::Replace(i, copy));
                    }
                }
            }
            Operator::LevelOp => {
                for (from, to) in [("max", "imax"), ("imax", "max")] {
                    if let Some(args) = line.get(from) {
                        push(
                            Agree,
                            Edit::Replace(i, json!({ "il": line["il"], to: args.clone() })),
                        );
                    }
                }
                if line.get("param").is_some() {
                    push(
                        Agree,
                        Edit::Replace(i, json!({ "il": line["il"], "succ": 0 })),
                    );
                }
            }
            Operator::NatLiteral => {
                if let Some(digits) = line.get("natVal").and_then(Value::as_str) {
                    let n = BigUint::parse_bytes(digits.as_bytes(), 10).unwrap();
                    push(
                        Agree,
                        Edit::Set(i, "/natVal".into(), json!((n + 1u32).to_string())),
                    );
                }
            }
            Operator::Hints if line.get("def").is_some() => {
                let current = &line["def"]["hints"];
                for hint in [json!("abbrev"), json!("opaque"), json!({"regular": 1})] {
                    if &hint != current {
                        push(Same, Edit::Set(i, "/def/hints".into(), hint));
                    }
                }
            }
            Operator::ThmToDef if line.get("thm").is_some() => {
                let mut def = line["thm"].clone();
                def["hints"] = json!("opaque");
                def["safety"] = json!("safe");
                push(Same, Edit::Replace(i, json!({ "def": def })));
            }
            _ => {}
        }
    }
    out
}
