//! Single-pass importer for lean4export NDJSON (format 3.1.0). Hot line shapes are
//! scanned by hand straight out of an mmap; everything else goes through serde_json.

pub mod blean;
mod scan;

use crate::hash64;
use crate::term::FxHashMap;
use crate::term::arena::Arena;
use crate::term::decl::{Constructor, Declar, Hint, Inductive, Info, RecRule, Recursor};
use crate::term::expr::{Expr, LetData, mk};
use crate::term::intern::{Block, Dag, Names, Stats, Store};
use crate::term::level::{IMAX_HASH, Level, MAX_HASH, PARAM_HASH, SUCC_HASH};
use crate::term::name::{NUM_HASH, Name, STR_HASH};
use crate::term::ptr::{ExprPtr, LevelPtr, LevelsPtr, NamePtr};
use num_bigint::BigUint;
use scan::Line;
use serde_json::Value;
use std::path::Path;

#[derive(Debug)]
pub enum ImportError {
    Invalid(String),
    Unsupported(String),
}

impl std::fmt::Display for ImportError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Invalid(s) => write!(f, "invalid export: {s}"),
            Self::Unsupported(s) => write!(f, "unsupported: {s}"),
        }
    }
}

impl std::error::Error for ImportError {}

type Result<T> = std::result::Result<T, ImportError>;

fn invalid<T>(s: impl Into<String>) -> Result<T> {
    Err(ImportError::Invalid(s.into()))
}

fn unsupported<T>(s: impl Into<String>) -> Result<T> {
    Err(ImportError::Unsupported(s.into()))
}

struct Importer<'a> {
    arena: &'a Arena,
    dag: Dag<'a>,
    anon: NamePtr<'a>,
    zero: LevelPtr<'a>,
    names: Vec<Option<NamePtr<'a>>>,
    levels: Vec<Option<LevelPtr<'a>>>,
    exprs: Vec<Option<ExprPtr<'a>>>,
    declars: Vec<Declar<'a>>,
    blocks: FxHashMap<NamePtr<'a>, Block>,
    stats: Stats,
    scratch: Vec<u32>,
    /// Indices of metadata records, which reuse their child's node.
    aliases: Vec<u32>,
}

fn slot<T: Copy>(v: &[Option<T>], i: u32) -> Result<T> {
    match v.get(i as usize) {
        Some(Some(x)) => Ok(*x),
        _ => invalid("unknown or forward reference"),
    }
}

fn put<T>(v: &mut Vec<Option<T>>, i: u32, x: T) -> Result<()> {
    let i = i as usize;
    if v.len() <= i {
        v.resize_with(i + 1, || None);
    }
    if v[i].is_some() {
        return invalid("duplicate index");
    }
    v[i] = Some(x);
    Ok(())
}

impl<'a> Importer<'a> {
    fn new(arena: &'a Arena, bytes: usize) -> Self {
        let lines = bytes / 56;
        let mut dag = Dag::with_capacity(lines);
        let anon = dag.add_name(arena, Name::Anon);
        let zero = dag.add_level(arena, Level::Zero);
        Self {
            arena,
            dag,
            anon,
            zero,
            names: vec![Some(anon)],
            levels: vec![Some(zero)],
            exprs: Vec::with_capacity(lines),
            declars: Vec::new(),
            blocks: FxHashMap::default(),
            stats: Stats {
                names: 1,
                levels: 1,
                ..Stats::default()
            },
            scratch: Vec::new(),
            aliases: Vec::new(),
        }
    }

    /// Feed every non-empty line of `bytes`, numbering them from `n`.
    fn lines(&mut self, bytes: &[u8], n: &mut usize) -> Result<()> {
        let mut start = 0;
        for end in memchr::memchr_iter(b'\n', bytes).chain([bytes.len()]) {
            let line = &bytes[start..end];
            start = end + 1;
            if !line.is_empty() {
                self.line(line, *n == 0).map_err(|e| at(e, *n))?;
                *n += 1;
            }
        }
        Ok(())
    }

    fn finish_lines(self, n: usize) -> Result<Store<'a>> {
        if n == 0 {
            return invalid("empty export");
        }
        Ok(self.finish())
    }

    fn name(&self, i: u32) -> Result<NamePtr<'a>> {
        slot(&self.names, i)
    }

    fn level(&self, i: u32) -> Result<LevelPtr<'a>> {
        slot(&self.levels, i)
    }

    fn expr(&self, i: u32) -> Result<ExprPtr<'a>> {
        slot(&self.exprs, i)
    }

    fn add_name(&mut self, i: u32, n: Name<'a>) -> Result<()> {
        let p = match self.dag.find_name(&n) {
            Some(p) => p,
            None => self.dag.add_name(self.arena, n),
        };
        self.stats.names += 1;
        put(&mut self.names, i, p)
    }

    fn do_str(&mut self, i: u32, pre: u32, s: &str) -> Result<()> {
        let pre = self.name(pre)?;
        let s = match self.dag.find_str(s) {
            Some(p) => p,
            None => self.dag.add_str(self.arena, s),
        };
        self.add_name(i, Name::Str(pre, s, hash64!(STR_HASH, pre, s)))
    }

    fn do_num(&mut self, i: u32, pre: u32, n: u64) -> Result<()> {
        let pre = self.name(pre)?;
        self.add_name(i, Name::Num(pre, n, hash64!(NUM_HASH, pre, n)))
    }

    fn add_level(&mut self, i: u32, l: Level<'a>) -> Result<()> {
        let p = match self.dag.find_level(&l) {
            Some(p) => p,
            None => self.dag.add_level(self.arena, l),
        };
        self.stats.levels += 1;
        put(&mut self.levels, i, p)
    }

    fn do_succ(&mut self, i: u32, l: u32) -> Result<()> {
        let l = self.level(l)?;
        self.add_level(i, Level::Succ(l, hash64!(SUCC_HASH, l)))
    }

    fn do_max(&mut self, i: u32, a: u32, b: u32, imax: bool) -> Result<()> {
        let (a, b) = (self.level(a)?, self.level(b)?);
        let l = if imax {
            Level::IMax(a, b, hash64!(IMAX_HASH, a, b))
        } else {
            Level::Max(a, b, hash64!(MAX_HASH, a, b))
        };
        self.add_level(i, l)
    }

    fn do_param(&mut self, i: u32, n: u32) -> Result<()> {
        let n = self.name(n)?;
        self.add_level(i, Level::Param(n, hash64!(PARAM_HASH, n)))
    }

    /// Exported expressions are already shared, so every node is new; the table is
    /// filled once at the end instead of probed per node.
    fn intern(&mut self, (e, nlb): (Expr<'a>, u16)) -> ExprPtr<'a> {
        ExprPtr::new(self.arena.alloc(e), nlb)
    }

    fn alias(&mut self, i: u32, e: u32) -> Result<()> {
        let e = self.expr(e)?;
        self.stats.expressions += 1;
        self.aliases.push(i);
        put(&mut self.exprs, i, e)
    }

    fn add_expr(&mut self, i: u32, node: (Expr<'a>, u16)) -> Result<()> {
        let p = self.intern(node);
        self.stats.expressions += 1;
        put(&mut self.exprs, i, p)
    }

    fn do_bvar(&mut self, i: u32, v: u64) -> Result<()> {
        match u16::try_from(v) {
            Ok(v) if v < 0x7ffe => self.add_expr(i, mk::var(v)),
            _ => unsupported("bound variable index too large"),
        }
    }

    fn do_sort(&mut self, i: u32, l: u32) -> Result<()> {
        let l = self.level(l)?;
        self.add_expr(i, mk::sort(l))
    }

    fn do_const(&mut self, i: u32, n: u32, us: &[u32]) -> Result<()> {
        let n = self.name(n)?;
        let us = self.level_list(us)?;
        self.add_expr(i, mk::konst(n, us))
    }

    fn level_list(&mut self, us: &[u32]) -> Result<LevelsPtr<'a>> {
        let ls = us
            .iter()
            .map(|&u| self.level(u))
            .collect::<Result<Vec<_>>>()?;
        Ok(match self.dag.find_levels(&ls) {
            Some(p) => p,
            None => self.dag.add_levels(self.arena, &ls),
        })
    }

    fn do_app(&mut self, i: u32, f: u32, a: u32) -> Result<()> {
        let (f, a) = (self.expr(f)?, self.expr(a)?);
        self.add_expr(i, mk::app(f, a))
    }

    fn do_binder(&mut self, i: u32, name: u32, ty: u32, body: u32, lam: bool) -> Result<()> {
        self.name(name)?;
        let (ty, body) = (self.expr(ty)?, self.expr(body)?);
        self.add_expr(
            i,
            if lam {
                mk::lam(ty, body)
            } else {
                mk::pi(ty, body)
            },
        )
    }

    fn do_let(
        &mut self,
        i: u32,
        name: u32,
        ty: u32,
        val: u32,
        body: u32,
        nondep: bool,
    ) -> Result<()> {
        self.name(name)?;
        let d = LetData {
            ty: self.expr(ty)?,
            val: self.expr(val)?,
            body: self.expr(body)?,
            nondep,
        };
        let (hash, sup, nlb) = mk::let_(d);
        let data = self.arena.alloc(d);
        self.add_expr(i, (Expr::Let { data, hash, sup }, nlb))
    }

    fn do_proj(&mut self, i: u32, n: u32, idx: u64, e: u32) -> Result<()> {
        let n = self.name(n)?;
        let e = self.expr(e)?;
        let Ok(idx) = u16::try_from(idx) else {
            return unsupported("projection index too large");
        };
        self.add_expr(i, mk::proj(n, idx, e))
    }

    fn do_nat(&mut self, i: u32, digits: &str) -> Result<()> {
        if digits.is_empty() || !digits.bytes().all(|c| c.is_ascii_digit()) {
            return invalid("invalid natural literal");
        }
        let n = BigUint::parse_bytes(digits.as_bytes(), 10).unwrap();
        let n = match self.dag.find_nat(&n) {
            Some(p) => p,
            None => self.dag.add_nat(self.arena, n),
        };
        self.add_expr(i, mk::nat(n))
    }

    fn do_strlit(&mut self, i: u32, s: &str) -> Result<()> {
        let s = match self.dag.find_str(s) {
            Some(p) => p,
            None => self.dag.add_str(self.arena, s),
        };
        self.add_expr(i, mk::str(s))
    }

    fn uparams(&mut self, ns: &[u32]) -> Result<LevelsPtr<'a>> {
        let mut ls = Vec::with_capacity(ns.len());
        for &n in ns {
            let n = self.name(n)?;
            let l = Level::Param(n, hash64!(PARAM_HASH, n));
            ls.push(match self.dag.find_level(&l) {
                Some(p) => p,
                None => self.dag.add_level(self.arena, l),
            });
        }
        Ok(match self.dag.find_levels(&ls) {
            Some(p) => p,
            None => self.dag.add_levels(self.arena, &ls),
        })
    }

    fn info(&mut self, name: u32, uparams: &[u32], ty: u32) -> Result<Info<'a>> {
        let name = self.name(name)?;
        let uparams = self.uparams(uparams)?;
        if uparams.distinct_params() {
            Ok(Info {
                name,
                uparams,
                ty: self.expr(ty)?,
            })
        } else {
            invalid("duplicate universe parameter")
        }
    }

    fn add_declar(&mut self, d: Declar<'a>) -> Result<()> {
        let n = d.name();
        if n.decl_idx().is_some() {
            return invalid(format!("duplicate declaration {n}"));
        }
        n.set_decl_idx(self.declars.len() as u32);
        self.declars.push(d);
        self.stats.declarations += 1;
        Ok(())
    }

    fn check_group(&self, own: u32, all: &[u32]) -> Result<()> {
        let own = self.name(own)?;
        let all = all
            .iter()
            .map(|&n| self.name(n))
            .collect::<Result<Vec<_>>>()?;
        let distinct = all.iter().collect::<crate::term::FxHashSet<_>>().len() == all.len();
        if !all.contains(&own) || !distinct {
            return invalid("invalid declaration group metadata");
        }
        Ok(())
    }

    // Keep the parsed export fields together at this boundary.
    #[allow(clippy::too_many_arguments)]
    fn do_def(
        &mut self,
        name: u32,
        uparams: &[u32],
        ty: u32,
        val: u32,
        all: &[u32],
        hint: Hint,
        safety: &str,
    ) -> Result<()> {
        match safety {
            "safe" => {}
            "unsafe" | "partial" => {
                return invalid(
                    "unsafe or partial definition is not permitted in a safe proof export",
                );
            }
            _ => return invalid("invalid definition safety"),
        }
        self.check_group(name, all)?;
        let info = self.info(name, uparams, ty)?;
        let val = self.expr(val)?;
        self.add_declar(Declar::Def(info, val, hint))
    }

    fn do_thm(&mut self, name: u32, uparams: &[u32], ty: u32, val: u32, all: &[u32]) -> Result<()> {
        self.check_group(name, all)?;
        let info = self.info(name, uparams, ty)?;
        let val = self.expr(val)?;
        self.add_declar(Declar::Thm(info, val))
    }

    fn line(&mut self, b: &[u8], first: bool) -> Result<()> {
        if !first {
            match scan::fast(b, &mut self.scratch) {
                Some(Line::Str(i, pre, s)) => return self.do_str(i, pre, s),
                Some(Line::Num(i, pre, n)) => return self.do_num(i, pre, n),
                Some(Line::Succ(i, l)) => return self.do_succ(i, l),
                Some(Line::Max(i, a, c, imax)) => return self.do_max(i, a, c, imax),
                Some(Line::Param(i, n)) => return self.do_param(i, n),
                Some(Line::App(i, f, a)) => return self.do_app(i, f, a),
                Some(Line::Bvar(i, v)) => return self.do_bvar(i, v),
                Some(Line::Sort(i, l)) => return self.do_sort(i, l),
                Some(Line::Const(i, n)) => {
                    let us = std::mem::take(&mut self.scratch);
                    let r = self.do_const(i, n, &us);
                    self.scratch = us;
                    return r;
                }
                Some(Line::Binder(i, name, ty, body, lam)) => {
                    return self.do_binder(i, name, ty, body, lam);
                }
                Some(Line::Let(i, name, ty, val, body, nondep)) => {
                    return self.do_let(i, name, ty, val, body, nondep);
                }
                Some(Line::Proj(i, n, idx, e)) => return self.do_proj(i, n, idx, e),
                None => {}
            }
        }
        let v: Value =
            serde_json::from_slice(b).map_err(|e| ImportError::Invalid(e.to_string()))?;
        self.general(&v, first)
    }

    fn general(&mut self, v: &Value, first: bool) -> Result<()> {
        let Some(o) = v.as_object() else {
            return invalid("expected object");
        };
        if first {
            if o.len() != 1 || v.get("meta").is_none() {
                return invalid("missing export metadata");
            }
            if v["meta"]["format"]["version"] != "3.1.0" {
                return unsupported("export format version");
            }
            return Ok(());
        }
        if let Some(id) = v.get("in") {
            let i = idx(id)?;
            if o.len() != 2 {
                return invalid("malformed name entry");
            }
            return if let Some(n) = v.get("str") {
                self.do_str(i, idx(&n["pre"])?, string(&n["str"])?)
            } else if let Some(n) = v.get("num") {
                let Some(k) = n["i"].as_u64() else {
                    return invalid("invalid numeric name");
                };
                self.do_num(i, idx(&n["pre"])?, k)
            } else {
                invalid("unknown name entry")
            };
        }
        if let Some(id) = v.get("il") {
            let i = idx(id)?;
            if o.len() != 2 {
                return invalid("malformed level entry");
            }
            if let Some(p) = v.get("param") {
                return self.do_param(i, idx(p)?);
            }
            if let Some(l) = v.get("succ") {
                return self.do_succ(i, idx(l)?);
            }
            let (args, imax) = match (v.get("max"), v.get("imax")) {
                (Some(a), _) => (a, false),
                (_, Some(a)) => (a, true),
                _ => return invalid("unknown level entry"),
            };
            let [a, b] = array(args)? else {
                return invalid("level operator arity");
            };
            return self.do_max(i, idx(a)?, idx(b)?, imax);
        }
        if let Some(id) = v.get("ie") {
            let i = idx(id)?;
            if o.len() != 2 {
                return invalid("malformed expression entry");
            }
            if let Some(x) = v.get("bvar") {
                let Some(x) = x.as_u64() else {
                    return invalid("expected nonnegative index");
                };
                return self.do_bvar(i, x);
            }
            if let Some(x) = v.get("natVal") {
                return self.do_nat(i, string(x)?);
            }
            if let Some(x) = v.get("strVal") {
                return self.do_strlit(i, string(x)?);
            }
            if let Some(l) = v.get("sort") {
                return self.do_sort(i, idx(l)?);
            }
            if let Some(c) = v.get("const") {
                let us = idxs(&c["us"])?;
                return self.do_const(i, idx(&c["name"])?, &us);
            }
            if let Some(a) = v.get("app") {
                return self.do_app(i, idx(&a["fn"])?, idx(&a["arg"])?);
            }
            if let Some(p) = v.get("proj") {
                let Some(k) = p["idx"].as_u64() else {
                    return invalid("expected nonnegative index");
                };
                return self.do_proj(i, idx(&p["typeName"])?, k, idx(&p["struct"])?);
            }
            if let Some(b) = v.get("lam") {
                return self.do_binder(
                    i,
                    idx(&b["name"])?,
                    idx(&b["type"])?,
                    idx(&b["body"])?,
                    true,
                );
            }
            if let Some(b) = v.get("forallE") {
                return self.do_binder(
                    i,
                    idx(&b["name"])?,
                    idx(&b["type"])?,
                    idx(&b["body"])?,
                    false,
                );
            }
            if let Some(b) = v.get("letE") {
                let nondep = b["nondep"].as_bool().unwrap_or(false);
                return self.do_let(
                    i,
                    idx(&b["name"])?,
                    idx(&b["type"])?,
                    idx(&b["value"])?,
                    idx(&b["body"])?,
                    nondep,
                );
            }
            if let Some(m) = v.get("mdata") {
                return self.alias(i, idx(&m["expr"])?);
            }
            return unsupported(format!(
                "expression {}",
                o.keys().find(|k| *k != "ie").unwrap()
            ));
        }
        if o.len() != 1 {
            return invalid("malformed declaration entry");
        }
        let (kind, d) = o.iter().next().unwrap();
        match kind.as_str() {
            "def" => {
                let hint = match &d["hints"] {
                    Value::String(s) if s == "opaque" => Hint::Opaque,
                    Value::String(s) if s == "abbrev" => Hint::Abbrev,
                    h => match h.get("regular").and_then(Value::as_u64) {
                        Some(n) => Hint::Regular(n as u32),
                        None => return invalid("invalid reducibility hint"),
                    },
                };
                let all = idxs_or_empty(d, "all")?;
                self.do_def(
                    idx(&d["name"])?,
                    &idxs(&d["levelParams"])?,
                    idx(&d["type"])?,
                    idx(&d["value"])?,
                    &all,
                    hint,
                    string(&d["safety"])?,
                )
            }
            "thm" => {
                let all = idxs_or_empty(d, "all")?;
                self.do_thm(
                    idx(&d["name"])?,
                    &idxs(&d["levelParams"])?,
                    idx(&d["type"])?,
                    idx(&d["value"])?,
                    &all,
                )
            }
            "axiom" | "opaque" => {
                if boolean(&d["isUnsafe"])? {
                    return invalid("unsafe declaration is not permitted in a safe proof export");
                }
                if d.get("all").is_some() {
                    self.check_group(idx(&d["name"])?, &idxs(&d["all"])?)?;
                }
                let info = self.info(
                    idx(&d["name"])?,
                    &idxs(&d["levelParams"])?,
                    idx(&d["type"])?,
                )?;
                if kind == "axiom" {
                    self.add_declar(Declar::Axiom(info))
                } else {
                    let val = self.expr(idx(&d["value"])?)?;
                    self.add_declar(Declar::Opaque(info, val))
                }
            }
            "quot" => {
                let kind = string(&d["kind"])?;
                let expected = match kind {
                    "type" => "Quot",
                    "ctor" => "Quot.mk",
                    "lift" => "Quot.lift",
                    "ind" => "Quot.ind",
                    _ => return invalid("invalid quotient kind"),
                };
                let actual = self.name(idx(&d["name"])?)?;
                if self.dag.lookup(self.anon, expected) != Some(actual) {
                    return invalid("quotient kind and name disagree");
                }
                let info = self.info(
                    idx(&d["name"])?,
                    &idxs(&d["levelParams"])?,
                    idx(&d["type"])?,
                )?;
                self.add_declar(Declar::Quot(info))
            }
            "inductive" => self.inductive(d),
            _ => unsupported(format!("declaration kind {kind}")),
        }
    }

    fn names_of(&self, v: &Value) -> Result<&'a [NamePtr<'a>]> {
        let ns = idxs(v)?
            .into_iter()
            .map(|n| self.name(n))
            .collect::<Result<Vec<_>>>()?;
        Ok(self.arena.alloc_slice_copy(&ns))
    }

    fn inductive(&mut self, d: &Value) -> Result<()> {
        let safe = |v: &Value| -> Result<()> {
            if boolean(&v["isUnsafe"])? {
                return invalid(
                    "unsafe inductive declaration is not permitted in a safe proof export",
                );
            }
            Ok(())
        };
        let start = self.declars.len() as u32;
        let types = array(&d["types"])?;
        for t in types {
            safe(t)?;
            let info = self.info(
                idx(&t["name"])?,
                &idxs(&t["levelParams"])?,
                idx(&t["type"])?,
            )?;
            let ind = Inductive {
                info,
                is_rec: boolean(&t["isRec"])?,
                num_nested: idx(&t["numNested"])? as usize,
                is_reflexive: boolean(&t["isReflexive"])?,
                num_params: small(&t["numParams"])?,
                num_indices: small(&t["numIndices"])?,
                all: self.names_of(&t["all"])?,
                ctors: self.names_of(&t["ctors"])?,
            };
            self.add_declar(Declar::Ind(ind))?;
        }
        if types.is_empty() {
            return invalid("empty inductive block");
        }
        let types_end = self.declars.len() as u32;
        for c in array(&d["ctors"])? {
            safe(c)?;
            let info = self.info(
                idx(&c["name"])?,
                &idxs(&c["levelParams"])?,
                idx(&c["type"])?,
            )?;
            let ctor = Constructor {
                info,
                induct: self.name(idx(&c["induct"])?)?,
                cidx: small(&c["cidx"])?,
                num_params: small(&c["numParams"])?,
                num_fields: small(&c["numFields"])?,
            };
            self.add_declar(Declar::Ctor(ctor))?;
        }
        let ctors_end = self.declars.len() as u32;
        for r in array(&d["recs"])? {
            safe(r)?;
            let info = self.info(
                idx(&r["name"])?,
                &idxs(&r["levelParams"])?,
                idx(&r["type"])?,
            )?;
            let rules = array(&r["rules"])?
                .iter()
                .map(|x| {
                    Ok(RecRule {
                        ctor: self.name(idx(&x["ctor"])?)?,
                        nfields: small(&x["nfields"])?,
                        rhs: self.expr(idx(&x["rhs"])?)?,
                    })
                })
                .collect::<Result<Vec<_>>>()?;
            let rec = Recursor {
                info,
                all: self.names_of(&r["all"])?,
                num_params: small(&r["numParams"])?,
                num_indices: small(&r["numIndices"])?,
                num_motives: small(&r["numMotives"])?,
                num_minors: small(&r["numMinors"])?,
                rules: self.arena.alloc_slice_copy(&rules),
                is_k: boolean(&r["k"])?,
            };
            self.add_declar(Declar::Rec(rec))?;
        }
        let block = Block {
            start,
            types_end,
            ctors_end,
            end: self.declars.len() as u32,
        };
        for declaration in &self.declars[start as usize..block.end as usize] {
            self.blocks.insert(declaration.name(), block);
        }
        Ok(())
    }

    fn finish(mut self) -> Store<'a> {
        self.names = Vec::new();
        self.levels = Vec::new();
        let mut aliases = self.aliases.iter().copied().peekable();
        self.dag.exprs.fill(
            (0..)
                .zip(&self.exprs)
                .filter(move |(i, _)| aliases.next_if_eq(i).is_none())
                .filter_map(|(_, e)| e.map(|e| e.as_ref())),
        );
        let names = Names::build(&self.dag, self.anon);
        Store {
            dag: self.dag,
            anon: self.anon,
            zero: self.zero,
            declars: self.declars,
            blocks: self.blocks,
            names,
            stats: self.stats,
        }
    }
}

fn idx(v: &Value) -> Result<u32> {
    match v.as_u64().and_then(|n| u32::try_from(n).ok()) {
        Some(n) => Ok(n),
        None => invalid("expected nonnegative index"),
    }
}

fn small(v: &Value) -> Result<u16> {
    match v.as_u64().and_then(|n| u16::try_from(n).ok()) {
        Some(n) => Ok(n),
        None => invalid("expected small nonnegative count"),
    }
}

fn idxs(v: &Value) -> Result<Vec<u32>> {
    array(v)?.iter().map(idx).collect()
}

fn idxs_or_empty(d: &Value, k: &str) -> Result<Vec<u32>> {
    match d.get(k) {
        Some(v) => idxs(v),
        None => Ok(Vec::new()),
    }
}

fn array(v: &Value) -> Result<&[Value]> {
    match v.as_array() {
        Some(a) => Ok(a),
        None => invalid("expected array"),
    }
}

fn string(v: &Value) -> Result<&str> {
    match v.as_str() {
        Some(s) => Ok(s),
        None => invalid("expected string"),
    }
}

fn boolean(v: &Value) -> Result<bool> {
    match v.as_bool() {
        Some(b) => Ok(b),
        None => invalid("expected boolean"),
    }
}

/// Import an export file into `arena`, streaming it so the file is never resident.
pub fn import<'a>(arena: &'a Arena, path: impl AsRef<Path>) -> Result<Store<'a>> {
    let io = |e: std::io::Error| ImportError::Invalid(e.to_string());
    let file = std::fs::File::open(path).map_err(io)?;
    let len = file.metadata().map_err(io)?.len() as usize;
    if let Some(map) = blean::map(&file).map_err(io)? {
        let im = blean::read(arena, &map)?;
        // The records are consumed; unmap before the fill peaks.
        drop(map);
        return Ok(im.finish());
    }
    import_reader(arena, file, len)
}

/// Bytes read per refill; a longer line grows the buffer to fit.
const CHUNK: usize = 16 << 20;

/// Import an export stream; `len` is a size hint in bytes, zero if unknown.
pub fn import_reader<'a>(
    arena: &'a Arena,
    mut r: impl std::io::Read,
    len: usize,
) -> Result<Store<'a>> {
    let io = |e: std::io::Error| ImportError::Invalid(e.to_string());
    let mut im = Importer::new(arena, len);
    let mut buf = vec![0u8; CHUNK];
    let (mut filled, mut n) = (0, 0);
    loop {
        if filled == buf.len() {
            buf.resize(2 * buf.len(), 0);
        }
        let k = match r.read(&mut buf[filled..]) {
            Err(e) if e.kind() == std::io::ErrorKind::Interrupted => continue,
            k => k.map_err(io)?,
        };
        filled += k;
        let end = if k == 0 {
            filled
        } else {
            match memchr::memrchr(b'\n', &buf[..filled]) {
                Some(p) => p + 1,
                None => continue,
            }
        };
        im.lines(&buf[..end], &mut n)?;
        buf.copy_within(end..filled, 0);
        filled -= end;
        if k == 0 {
            break;
        }
    }
    im.finish_lines(n)
}

fn at(e: ImportError, n: usize) -> ImportError {
    match e {
        ImportError::Invalid(s) => ImportError::Invalid(format!("line {}: {s}", n + 1)),
        ImportError::Unsupported(s) => ImportError::Unsupported(format!("line {}: {s}", n + 1)),
    }
}

pub fn import_bytes<'a>(arena: &'a Arena, bytes: &[u8]) -> Result<Store<'a>> {
    if blean::sniff(bytes) {
        return blean::import(arena, bytes);
    }
    let mut im = Importer::new(arena, bytes.len());
    let mut n = 0;
    im.lines(bytes, &mut n)?;
    im.finish_lines(n)
}
