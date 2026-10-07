use crate::export::FORMAT_VERSION;
use crate::kernel::{InductiveBlock, quotient_primitives};
use crate::parser::Declaration;
use crate::{Error, Expr, Level};
use serde_json::{Value, json};
use std::collections::HashMap;
use unbound::{Name, Shared};

const EXPORTER: &str = "nano-lean";
const ANONYMOUS_BINDER: &str = "x";

#[derive(Default)]
struct Writer {
    out: Vec<Value>,
    names: HashMap<String, u64>,
    levels: HashMap<Level, u64>,
    exprs: HashMap<String, u64>,
    shared: HashMap<usize, u64>,
    heights: HashMap<String, u64>,
}

impl Writer {
    fn name(&mut self, name: &str) -> u64 {
        if name.is_empty() {
            return 0;
        }
        if let Some(&id) = self.names.get(name) {
            return id;
        }
        let (pre, last) = name.rsplit_once('.').unwrap_or(("", name));
        let pre = self.name(pre);
        let id = self.names.len() as u64 + 1;
        self.out.push(match last.parse::<u64>() {
            Ok(i) => json!({"in": id, "num": {"pre": pre, "i": i}}),
            Err(_) => json!({"in": id, "str": {"pre": pre, "str": last}}),
        });
        self.names.insert(name.into(), id);
        id
    }

    fn names(&mut self, names: &[String]) -> Vec<u64> {
        names.iter().map(|n| self.name(n)).collect()
    }

    fn binder(&mut self, name: &Name<Expr>) -> u64 {
        self.name(name.string().unwrap_or(ANONYMOUS_BINDER))
    }

    fn level(&mut self, u: &Level) -> u64 {
        if let Some(&id) = self.levels.get(u) {
            return id;
        }
        let mut node = match u {
            Level::Nat(0) => return 0,
            Level::Nat(n) => json!({"succ": self.level(&Level::Nat(n - 1))}),
            Level::Succ(a) => json!({"succ": self.level(a)}),
            Level::Max(a, b) => json!({"max": [self.level(a), self.level(b)]}),
            Level::IMax(a, b) => json!({"imax": [self.level(a), self.level(b)]}),
            Level::Param(p) => json!({"param": self.name(p)}),
        };
        let id = self.levels.len() as u64 + 1;
        node["il"] = json!(id);
        self.out.push(node);
        self.levels.insert(u.clone(), id);
        id
    }

    fn shared(&mut self, e: &Shared<Expr>) -> Result<u64, Error> {
        let key = e.as_ptr() as usize;
        if let Some(&id) = self.shared.get(&key) {
            return Ok(id);
        }
        let id = self.expr(e)?;
        self.shared.insert(key, id);
        Ok(id)
    }

    fn expr(&mut self, e: &Expr) -> Result<u64, Error> {
        let mut node = match e {
            Expr::Var(n) => match n.coordinates() {
                Some((index, _)) => json!({"bvar": index}),
                None => return Err(Error(format!("open term: free variable {n}"))),
            },
            Expr::Sort(u) => json!({"sort": self.level(u)}),
            Expr::Const(n, us) => {
                let us: Vec<_> = us.iter().map(|u| self.level(u)).collect();
                json!({"const": {"name": self.name(n), "us": us}})
            }
            Expr::App(f, a) => json!({"app": {"fn": self.shared(f)?, "arg": self.shared(a)?}}),
            Expr::Pi(t, b) | Expr::Lam(t, b) => {
                let tag = if matches!(e, Expr::Pi(..)) {
                    "forallE"
                } else {
                    "lam"
                };
                json!({tag: {
                    "binderInfo": "default",
                    "body": self.shared(b.body())?,
                    "name": self.binder(b.pattern()),
                    "type": self.shared(t)?,
                }})
            }
            Expr::Let(t, v, b) => json!({"letE": {
                "body": self.shared(b.body())?,
                "name": self.binder(b.pattern()),
                "nondep": false,
                "type": self.shared(t)?,
                "value": self.shared(v)?,
            }}),
            Expr::Proj(n, i, s) => json!({"proj": {
                "idx": i,
                "struct": self.shared(s)?,
                "typeName": self.name(n),
            }}),
            Expr::Nat(n) => json!({"natVal": n.0.to_string()}),
            Expr::Str(s) => json!({"strVal": s}),
        };
        let key = node.to_string();
        if let Some(&id) = self.exprs.get(&key) {
            return Ok(id);
        }
        let id = self.exprs.len() as u64;
        node["ie"] = json!(id);
        self.out.push(node);
        self.exprs.insert(key, id);
        Ok(id)
    }

    fn height(&self, e: &Expr) -> u64 {
        fn go(e: &Expr, w: &Writer, seen: &mut HashMap<usize, u64>) -> u64 {
            let mut shared = |e: &Shared<Expr>| {
                let key = e.as_ptr() as usize;
                if let Some(&h) = seen.get(&key) {
                    return h;
                }
                let h = go(e, w, seen);
                seen.insert(key, h);
                h
            };
            match e {
                Expr::Const(n, _) => w.heights.get(n).copied().unwrap_or(0),
                Expr::App(f, a) => shared(f).max(shared(a)),
                Expr::Proj(_, _, e) => shared(e),
                Expr::Pi(t, b) | Expr::Lam(t, b) => shared(t).max(shared(b.body())),
                Expr::Let(t, v, b) => shared(t).max(shared(v)).max(shared(b.body())),
                _ => 0,
            }
        }
        1 + go(e, self, &mut HashMap::new())
    }

    fn inductive(&mut self, block: &InductiveBlock) -> Result<Value, Error> {
        let types = block
            .types
            .iter()
            .map(|t| -> Result<_, Error> {
                Ok(json!({
                    "all": self.names(&t.all),
                    "ctors": self.names(&t.constructors),
                    "isRec": t.recursive,
                    "isReflexive": t.reflexive,
                    "isUnsafe": false,
                    "levelParams": self.names(&t.params),
                    "name": self.name(&t.name),
                    "numIndices": t.num_indices,
                    "numNested": t.num_nested,
                    "numParams": t.num_params,
                    "type": self.expr(&t.ty)?,
                }))
            })
            .collect::<Result<Vec<_>, _>>()?;
        let ctors = block
            .constructors
            .iter()
            .map(|c| -> Result<_, Error> {
                Ok(json!({
                    "cidx": c.index,
                    "induct": self.name(&c.inductive),
                    "isUnsafe": false,
                    "levelParams": self.names(&c.params),
                    "name": self.name(&c.name),
                    "numFields": c.num_fields,
                    "numParams": c.num_params,
                    "type": self.expr(&c.ty)?,
                }))
            })
            .collect::<Result<Vec<_>, _>>()?;
        let recs = block
            .recursors
            .iter()
            .map(|r| -> Result<_, Error> {
                let rules = r
                    .rules
                    .iter()
                    .map(|rule| -> Result<_, Error> {
                        Ok(json!({
                            "ctor": self.name(&rule.constructor),
                            "nfields": rule.num_fields,
                            "rhs": self.expr(&rule.rhs)?,
                        }))
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(json!({
                    "all": self.names(&r.all),
                    "isUnsafe": false,
                    "k": r.k,
                    "levelParams": self.names(&r.params),
                    "name": self.name(&r.name),
                    "numIndices": r.num_indices,
                    "numMinors": r.num_minors,
                    "numMotives": r.num_motives,
                    "numParams": r.num_params,
                    "rules": rules,
                    "type": self.expr(&r.ty)?,
                }))
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok(json!({"inductive": {"ctors": ctors, "recs": recs, "types": types}}))
    }

    fn quotient(&mut self) -> Result<(), Error> {
        for (name, kind, params, ty) in quotient_primitives() {
            let record = json!({"quot": {
                "kind": kind,
                "levelParams": self.names(&params),
                "name": self.name(name),
                "type": self.expr(&ty)?,
            }});
            self.out.push(record);
            // `ty` is dropped here, so its addresses may be reused.
            self.shared.clear();
        }
        Ok(())
    }

    fn declaration(&mut self, d: &Declaration) -> Result<(), Error> {
        let record = match d {
            Declaration::Axiom(n, ps, ty) => json!({"axiom": {
                "isUnsafe": false,
                "levelParams": self.names(ps),
                "name": self.name(n),
                "type": self.expr(ty)?,
            }}),
            Declaration::Definition(n, ps, ty, value) => {
                let height = self.height(value);
                self.heights.insert(n.clone(), height);
                json!({"def": {
                    "all": [self.name(n)],
                    "hints": {"regular": height},
                    "levelParams": self.names(ps),
                    "name": self.name(n),
                    "safety": "safe",
                    "type": self.expr(ty)?,
                    "value": self.expr(value)?,
                }})
            }
            Declaration::Theorem(n, ps, ty, value) => json!({"thm": {
                "all": [self.name(n)],
                "levelParams": self.names(ps),
                "name": self.name(n),
                "type": self.expr(ty)?,
                "value": self.expr(value)?,
            }}),
            Declaration::Inductive(block) => self.inductive(block)?,
            Declaration::Quotient => return self.quotient(),
        };
        self.out.push(record);
        Ok(())
    }
}

pub fn ndjson(declarations: &[Declaration]) -> Result<String, Error> {
    let mut w = Writer::default();
    w.out.push(json!({"meta": {
        "exporter": {"name": EXPORTER, "version": env!("CARGO_PKG_VERSION")},
        "format": {"version": FORMAT_VERSION},
    }}));
    for d in declarations {
        w.declaration(d)?;
    }
    Ok(w.out.iter().map(|v| format!("{v}\n")).collect())
}
