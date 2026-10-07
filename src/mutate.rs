//! Targeted single edits to a valid export, checked against every checker,
//! plus a shrinker that cuts a finding down to the declarations it needs.

use crate::checker::Limits;
use crate::verdict::{self, Verdict, Verdicts};
use serde_json::{Value, json};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Ref {
    Name,
    Level,
    Expr,
}

/// What a correct checker must say about a mutant.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Expect {
    /// The edit breaks an invariant: every checker rejects.
    Reject,
    /// The edit may or may not be valid: checkers must agree.
    Agree,
    /// The edit only affects performance: verdicts match the original.
    Same,
}

#[derive(Clone, Debug)]
pub enum Edit {
    Set(usize, String, Value),
    Replace(usize, Value),
    Remove(usize),
    Duplicate(usize),
    Swap(usize, usize),
}

#[derive(Clone, Debug)]
pub struct Mutant {
    pub op: &'static str,
    pub expect: Expect,
    pub edit: Edit,
}

impl Mutant {
    pub fn apply(&self, lines: &[Value]) -> Vec<Value> {
        let mut out = lines.to_vec();
        match &self.edit {
            Edit::Set(i, ptr, v) => *out[*i].pointer_mut(ptr).unwrap() = v.clone(),
            Edit::Replace(i, v) => out[*i] = v.clone(),
            Edit::Remove(i) => {
                out.remove(*i);
            }
            Edit::Duplicate(i) => out.insert(*i + 1, lines[*i].clone()),
            Edit::Swap(a, b) => out.swap(*a, *b),
        }
        out
    }
    /// The line in the mutant that carries the edit, if it is a single line.
    pub fn pin(&self) -> Option<usize> {
        match self.edit {
            Edit::Set(i, ..) | Edit::Replace(i, _) => Some(i),
            Edit::Duplicate(i) => Some(i + 1),
            Edit::Remove(_) | Edit::Swap(..) => None,
        }
    }
    pub fn site(&self) -> String {
        match &self.edit {
            Edit::Set(i, ptr, v) => format!("line {} {ptr} = {v}", i + 1),
            Edit::Replace(i, _) => format!("line {} replaced", i + 1),
            Edit::Remove(i) => format!("line {} removed", i + 1),
            Edit::Duplicate(i) => format!("line {} duplicated", i + 1),
            Edit::Swap(a, b) => format!("lines {} and {} swapped", a + 1, b + 1),
        }
    }
}

pub fn parse(source: &str) -> Result<Vec<Value>, serde_json::Error> {
    source
        .lines()
        .filter(|l| !l.trim().is_empty())
        .map(serde_json::from_str)
        .collect()
}

pub fn render(lines: &[Value]) -> String {
    lines.iter().map(|l| format!("{l}\n")).collect()
}

/// The table entry a line defines, if it is a name, level or expression.
pub fn defines(entry: &Value) -> Option<(Ref, u64)> {
    [("in", Ref::Name), ("il", Ref::Level), ("ie", Ref::Expr)]
        .into_iter()
        .find_map(|(k, r)| Some((r, entry.get(k)?.as_u64()?)))
}

pub fn is_declaration(entry: &Value) -> bool {
    defines(entry).is_none() && entry.get("meta").is_none()
}

/// JSON pointers to every table reference an entry makes.
pub fn refs(entry: &Value) -> Vec<(Ref, String)> {
    use Ref::*;
    let mut out = Vec::new();
    let mut at = |kind: Ref, ptr: String| match entry.pointer(&ptr) {
        Some(Value::Array(items)) => {
            out.extend((0..items.len()).map(|i| (kind, format!("{ptr}/{i}"))))
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
            for b in ["lam", "forallE", "letE"] {
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
            } else if kind != "meta" {
                decl(format!("/{kind}"), body);
            }
        }
    }
    out
}

/// Drop unreachable table entries and renumber the rest densely, keeping
/// the pinned line and reporting where it moved.
pub fn compact(lines: &[Value], pin: Option<usize>) -> (Vec<Value>, Option<usize>) {
    let mut live: BTreeSet<(Ref, u64)> = BTreeSet::new();
    for (i, line) in lines.iter().enumerate().rev() {
        let keep = match defines(line) {
            Some(d) => pin == Some(i) || live.contains(&d),
            None => true,
        };
        if keep {
            for (kind, ptr) in refs(line) {
                live.insert((kind, line.pointer(&ptr).unwrap().as_u64().unwrap()));
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
            let fresh = next[&kind];
            *next.get_mut(&kind).unwrap() += 1;
            map.entry((kind, id)).or_insert(fresh);
            let key = match kind {
                Ref::Name => "in",
                Ref::Level => "il",
                Ref::Expr => "ie",
            };
            line[key] = json!(fresh);
        }
        for (kind, ptr) in refs(&line) {
            let slot = line.pointer_mut(&ptr).unwrap();
            if let Some(&n) = map.get(&(kind, slot.as_u64().unwrap())) {
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

/// A small deterministic generator, so a seed reproduces a run.
pub struct Rng(u64);

impl Rng {
    pub fn new(seed: u64) -> Self {
        Self(seed ^ 0x9e37_79b9_7f4a_7c15)
    }
    pub fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }
    pub fn below(&mut self, n: usize) -> usize {
        (self.next_u64() % n as u64) as usize
    }
}

pub const OPERATORS: &[&str] = &[
    "loose-bvar",
    "dangling-ref",
    "duplicate-decl",
    "inductive-count",
    "inductive-flag",
    "unsafe",
    "reorder",
    "drop-decl",
    "swap-decls",
    "retarget-expr",
    "level-op",
    "nat-literal",
    "hints",
    "thm-to-def",
];

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

/// Every mutant of one operator, in file order.
pub fn mutants(lines: &[Value], op: &'static str, rng: &mut Rng) -> Vec<Mutant> {
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
    let decls: Vec<usize> = (0..lines.len())
        .filter(|&i| is_declaration(&lines[i]))
        .collect();
    for (i, line) in lines.iter().enumerate() {
        let decl = is_declaration(line);
        match op {
            "loose-bvar" if line.get("bvar").is_some() => {
                push(Reject, Edit::Set(i, "/bvar".into(), json!(60_000)))
            }
            "dangling-ref" => {
                for (kind, ptr) in refs(line) {
                    let target = match defines(line) {
                        Some((k, id)) if k == kind => id,
                        _ => max(kind) + 1,
                    };
                    push(Reject, Edit::Set(i, ptr, json!(target)));
                }
            }
            "duplicate-decl" if decl => push(Reject, Edit::Duplicate(i)),
            "drop-decl" if decl => push(Agree, Edit::Remove(i)),
            "inductive-count" | "inductive-flag" if line.get("inductive").is_some() => {
                walk(line, &mut String::new(), &mut |ptr, key, v| {
                    if op == "inductive-count" && COUNTS.contains(&key) {
                        let n = v.as_u64().unwrap();
                        push(Reject, Edit::Set(i, ptr.into(), json!(n + 1)));
                        if n > 0 {
                            push(Reject, Edit::Set(i, ptr.into(), json!(n - 1)));
                        }
                    } else if op == "inductive-flag" && FLAGS.contains(&key) {
                        push(
                            Reject,
                            Edit::Set(i, ptr.into(), json!(!v.as_bool().unwrap())),
                        );
                    }
                });
            }
            "unsafe" if decl => walk(line, &mut String::new(), &mut |ptr, key, v| {
                if key == "isUnsafe" && v == &json!(false) {
                    push(Reject, Edit::Set(i, ptr.into(), json!(true)));
                } else if key == "safety" {
                    push(Reject, Edit::Set(i, ptr.into(), json!("unsafe")));
                }
            }),
            "reorder" if line.get("inductive").is_some() => {
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
            "swap-decls" if decl => {
                if let Some(&next) = decls.iter().find(|&&j| j > i) {
                    push(Agree, Edit::Swap(i, next));
                }
            }
            "retarget-expr" => {
                let bound = match defines(line) {
                    Some((Ref::Expr, id)) => id,
                    _ => max(Ref::Expr) + 1,
                };
                for (kind, ptr) in refs(line) {
                    if kind == Ref::Expr && bound > 1 {
                        let old = line.pointer(&ptr).unwrap().as_u64().unwrap();
                        let new = rng.below(bound as usize) as u64;
                        if new != old {
                            push(Agree, Edit::Set(i, ptr, json!(new)));
                        }
                    }
                }
            }
            "level-op" => {
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
            "nat-literal" => {
                if let Some(digits) = line.get("natVal").and_then(Value::as_str) {
                    let n = num_bigint::BigUint::parse_bytes(digits.as_bytes(), 10).unwrap();
                    push(
                        Agree,
                        Edit::Set(i, "/natVal".into(), json!((n + 1u32).to_string())),
                    );
                }
            }
            "hints" if line.get("def").is_some() => {
                let current = &line["def"]["hints"];
                for hint in [json!("abbrev"), json!("opaque"), json!({"regular": 1})] {
                    if &hint != current {
                        push(Same, Edit::Set(i, "/def/hints".into(), hint));
                    }
                }
            }
            "thm-to-def" if line.get("thm").is_some() => {
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

fn category(v: &Verdict) -> char {
    match v {
        Verdict::Accepted => 'A',
        Verdict::Rejected(_) => 'R',
        Verdict::Unsupported(_) => 'U',
        Verdict::Internal(_) => 'I',
    }
}

/// One letter per checker: Accepted, Rejected, Unsupported or Internal.
pub fn signature(v: &Verdicts) -> String {
    v.all().iter().map(|(_, v)| category(v)).collect()
}

/// Why a mutant's verdicts are wrong, if they are.
pub fn finding(expect: Expect, baseline: &Verdicts, v: &Verdicts) -> Option<&'static str> {
    if !v.agree() {
        return Some(
            if v.all()
                .iter()
                .any(|(_, v)| matches!(v, Verdict::Internal(_)))
            {
                "internal error"
            } else {
                "checkers disagree"
            },
        );
    }
    match expect {
        Expect::Reject if v.all().iter().any(|(_, v)| v.accepted()) => {
            Some("accepted an invalid export")
        }
        Expect::Same if signature(v) != signature(baseline) => Some("verdict changed"),
        _ => None,
    }
}

/// Greedily drop declarations other than the pinned line, then unused
/// table entries, while `keep` holds.
pub fn shrink(
    mut lines: Vec<Value>,
    mut pin: Option<usize>,
    keep: impl Fn(&[Value]) -> bool,
) -> Vec<Value> {
    loop {
        let before = lines.len();
        let mut i = lines.len();
        while i > 0 {
            i -= 1;
            if is_declaration(&lines[i]) && pin != Some(i) {
                let mut candidate = lines.clone();
                candidate.remove(i);
                if keep(&candidate) {
                    lines = candidate;
                    pin = pin.map(|p| if p > i { p - 1 } else { p });
                }
            }
        }
        let (compacted, moved) = compact(&lines, pin);
        if compacted.len() < lines.len() && keep(&compacted) {
            lines = compacted;
            pin = moved;
        }
        if lines.len() == before {
            return lines;
        }
    }
}

pub fn check(lines: &[Value], limits: Limits) -> Verdicts {
    verdict::check(&render(lines), limits)
}
