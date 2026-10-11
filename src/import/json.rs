use super::importer::Importer;
use super::{Result, invalid, unsupported};
use crate::export::FORMAT_VERSION;
use crate::export::json::{array, boolean, string};
use crate::hash64;
use crate::schema::{ExprKind, META, Ref};
use crate::term::FxHashSet;
use crate::term::decl::{Constructor, Declar, Hint, Inductive, Info, RecRule, Recursor};
use crate::term::intern::Block;
use crate::term::level::{Level, PARAM_HASH};
use crate::term::names::{QUOT, QUOT_IND, QUOT_LIFT, QUOT_MK};
use crate::term::ptr::{LevelsPtr, NamePtr};
use serde_json::{Map, Value};

impl<'a> Importer<'a> {
    pub(super) fn general(&mut self, v: &Value, first: bool) -> Result<()> {
        let Some(o) = v.as_object() else {
            return invalid("expected object");
        };
        if first {
            return metadata(v, o);
        }
        if let Some(id) = v.get(Ref::Name.key()) {
            return self.name_entry(idx(id)?, v, o);
        }
        if let Some(id) = v.get(Ref::Level.key()) {
            return self.level_entry(idx(id)?, v, o);
        }
        if let Some(id) = v.get(Ref::Expr.key()) {
            return self.expr_entry(idx(id)?, v, o);
        }
        if o.len() != 1 {
            return invalid("malformed declaration entry");
        }
        let (kind, d) = o.iter().next().expect("length checked above");
        self.declaration(kind, d)
    }

    fn name_entry(&mut self, i: u32, v: &Value, o: &Map<String, Value>) -> Result<()> {
        if o.len() != 2 {
            return invalid("malformed name entry");
        }
        if let Some(n) = v.get("str") {
            self.do_str(i, idx(&n["pre"])?, string(&n["str"])?)
        } else if let Some(n) = v.get("num") {
            let Some(k) = n["i"].as_u64() else {
                return invalid("invalid numeric name");
            };
            self.do_num(i, idx(&n["pre"])?, k)
        } else {
            invalid("unknown name entry")
        }
    }

    fn level_entry(&mut self, i: u32, v: &Value, o: &Map<String, Value>) -> Result<()> {
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
        self.do_max(i, idx(a)?, idx(b)?, imax)
    }

    fn expr_entry(&mut self, i: u32, v: &Value, o: &Map<String, Value>) -> Result<()> {
        if o.len() != 2 {
            return invalid("malformed expression entry");
        }
        if let Some(x) = v.get(ExprKind::BVar.key()) {
            let Some(x) = x.as_u64() else {
                return invalid("expected nonnegative index");
            };
            return self.do_bvar(i, x);
        }
        if let Some(x) = v.get(ExprKind::NatVal.key()) {
            return self.do_nat(i, string(x)?);
        }
        if let Some(x) = v.get(ExprKind::StrVal.key()) {
            return self.do_strlit(i, string(x)?);
        }
        if let Some(l) = v.get(ExprKind::Sort.key()) {
            return self.do_sort(i, idx(l)?);
        }
        if let Some(c) = v.get(ExprKind::Const.key()) {
            let us = idxs(&c["us"])?;
            return self.do_const(i, idx(&c["name"])?, &us);
        }
        if let Some(a) = v.get(ExprKind::App.key()) {
            return self.do_app(i, idx(&a["fn"])?, idx(&a["arg"])?);
        }
        if let Some(p) = v.get(ExprKind::Proj.key()) {
            let Some(k) = p["idx"].as_u64() else {
                return invalid("expected nonnegative index");
            };
            return self.do_proj(i, idx(&p["typeName"])?, k, idx(&p["struct"])?);
        }
        for (key, lam) in [
            (ExprKind::Lam.key(), true),
            (ExprKind::ForallE.key(), false),
        ] {
            if let Some(b) = v.get(key) {
                return self.do_binder(
                    i,
                    idx(&b["name"])?,
                    idx(&b["type"])?,
                    idx(&b["body"])?,
                    lam,
                );
            }
        }
        if let Some(b) = v.get(ExprKind::LetE.key()) {
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
        if let Some(m) = v.get(ExprKind::MData.key()) {
            return self.alias(i, idx(&m["expr"])?);
        }
        unsupported(format!(
            "expression {}",
            o.keys()
                .find(|k| *k != Ref::Expr.key())
                .map_or("<empty>", String::as_str)
        ))
    }

    fn declaration(&mut self, kind: &str, d: &Value) -> Result<()> {
        match kind {
            "def" => {
                let hint = hint(&d["hints"])?;
                self.check_group(d)?;
                self.do_def(
                    idx(&d["name"])?,
                    &idxs(&d["levelParams"])?,
                    idx(&d["type"])?,
                    idx(&d["value"])?,
                    hint,
                    string(&d["safety"])?,
                )
            }
            "thm" => {
                self.check_group(d)?;
                self.do_thm(
                    idx(&d["name"])?,
                    &idxs(&d["levelParams"])?,
                    idx(&d["type"])?,
                    idx(&d["value"])?,
                )
            }
            "axiom" | "opaque" => {
                if boolean(&d["isUnsafe"])? {
                    return invalid("unsafe declaration is not permitted in a safe proof export");
                }
                self.check_group(d)?;
                let info = self.info_of(d)?;
                if kind == "axiom" {
                    self.add_declar(Declar::Axiom(info))
                } else {
                    let val = self.expr(idx(&d["value"])?)?;
                    self.add_declar(Declar::Opaque(info, val))
                }
            }
            "quot" => {
                let expected = match string(&d["kind"])? {
                    "type" => QUOT,
                    "ctor" => QUOT_MK,
                    "lift" => QUOT_LIFT,
                    "ind" => QUOT_IND,
                    _ => return invalid("invalid quotient kind"),
                };
                let actual = self.name(idx(&d["name"])?)?;
                if self.dag.lookup(self.anon, expected) != Some(actual) {
                    return invalid("quotient kind and name disagree");
                }
                let info = self.info_of(d)?;
                self.add_declar(Declar::Quot(info))
            }
            "inductive" => self.inductive(d),
            _ => unsupported(format!("declaration kind {kind}")),
        }
    }

    fn uparams(&mut self, ns: &[u32]) -> Result<LevelsPtr<'a>> {
        let mut ls = Vec::with_capacity(ns.len());
        for &n in ns {
            let n = self.name(n)?;
            let l = Level::Param(n, hash64!(PARAM_HASH, n));
            ls.push(self.dag.intern_level(self.arena, l));
        }
        Ok(self.dag.intern_levels(self.arena, &ls))
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

    fn info_of(&mut self, d: &Value) -> Result<Info<'a>> {
        self.info(
            idx(&d["name"])?,
            &idxs(&d["levelParams"])?,
            idx(&d["type"])?,
        )
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

    fn check_group(&self, d: &Value) -> Result<()> {
        let Some(all) = d.get("all") else {
            return Ok(());
        };
        let own = self.name(idx(&d["name"])?)?;
        let all = array(all)?
            .iter()
            .map(|n| self.name(idx(n)?))
            .collect::<Result<Vec<_>>>()?;
        let distinct = all.iter().collect::<FxHashSet<_>>().len() == all.len();
        if !all.contains(&own) || !distinct {
            return invalid("invalid declaration group metadata");
        }
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn do_def(
        &mut self,
        name: u32,
        uparams: &[u32],
        ty: u32,
        val: u32,
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
        let info = self.info(name, uparams, ty)?;
        let val = self.expr(val)?;
        self.add_declar(Declar::Def(info, val, hint))
    }

    fn do_thm(&mut self, name: u32, uparams: &[u32], ty: u32, val: u32) -> Result<()> {
        let info = self.info(name, uparams, ty)?;
        let val = self.expr(val)?;
        self.add_declar(Declar::Thm(info, val))
    }

    fn names_of(&self, v: &Value) -> Result<&'a [NamePtr<'a>]> {
        let ns = idxs(v)?
            .into_iter()
            .map(|n| self.name(n))
            .collect::<Result<Vec<_>>>()?;
        Ok(self.arena.alloc_slice_copy(&ns))
    }

    fn inductive(&mut self, d: &Value) -> Result<()> {
        let start = self.declars.len() as u32;
        let types = array(&d["types"])?;
        for t in types {
            let ind = self.inductive_type(t)?;
            self.add_declar(Declar::Ind(ind))?;
        }
        if types.is_empty() {
            return invalid("empty inductive block");
        }
        let types_end = self.declars.len() as u32;
        for c in array(&d["ctors"])? {
            let ctor = self.constructor(c)?;
            self.add_declar(Declar::Ctor(ctor))?;
        }
        let ctors_end = self.declars.len() as u32;
        for r in array(&d["recs"])? {
            let rec = self.recursor(r)?;
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

    fn inductive_type(&mut self, t: &Value) -> Result<Inductive<'a>> {
        safe_member(t)?;
        Ok(Inductive {
            info: self.info_of(t)?,
            is_rec: boolean(&t["isRec"])?,
            num_nested: idx(&t["numNested"])? as usize,
            is_reflexive: boolean(&t["isReflexive"])?,
            num_params: small(&t["numParams"])?,
            num_indices: small(&t["numIndices"])?,
            all: self.names_of(&t["all"])?,
            ctors: self.names_of(&t["ctors"])?,
        })
    }

    fn constructor(&mut self, c: &Value) -> Result<Constructor<'a>> {
        safe_member(c)?;
        Ok(Constructor {
            info: self.info_of(c)?,
            induct: self.name(idx(&c["induct"])?)?,
            cidx: small(&c["cidx"])?,
            num_params: small(&c["numParams"])?,
            num_fields: small(&c["numFields"])?,
        })
    }

    fn recursor(&mut self, r: &Value) -> Result<Recursor<'a>> {
        safe_member(r)?;
        let info = self.info_of(r)?;
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
        Ok(Recursor {
            info,
            all: self.names_of(&r["all"])?,
            num_params: small(&r["numParams"])?,
            num_indices: small(&r["numIndices"])?,
            num_motives: small(&r["numMotives"])?,
            num_minors: small(&r["numMinors"])?,
            rules: self.arena.alloc_slice_copy(&rules),
            is_k: boolean(&r["k"])?,
        })
    }
}

fn metadata(v: &Value, o: &Map<String, Value>) -> Result<()> {
    if o.len() != 1 || v.get(META).is_none() {
        return invalid("missing export metadata");
    }
    if v[META]["format"]["version"] != FORMAT_VERSION {
        return unsupported("export format version");
    }
    Ok(())
}

fn hint(h: &Value) -> Result<Hint> {
    Ok(match h {
        Value::String(s) if s == "opaque" => Hint::Opaque,
        Value::String(s) if s == "abbrev" => Hint::Abbrev,
        h => match h
            .get("regular")
            .and_then(Value::as_u64)
            .and_then(|n| u32::try_from(n).ok())
        {
            Some(n) => Hint::Regular(n),
            None => return invalid("invalid reducibility hint"),
        },
    })
}

fn safe_member(v: &Value) -> Result<()> {
    if boolean(&v["isUnsafe"])? {
        return invalid("unsafe inductive declaration is not permitted in a safe proof export");
    }
    Ok(())
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
