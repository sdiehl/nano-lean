//! Content keys for declarations. A unit is one declaration, or a whole inductive block, and its
//! key covers its own structure and the keys of every unit it references, so it covers the
//! closure. Units are hashed on first use, by whichever check worker needs them.

use super::Key;
use crate::term::FxHashMap;
use crate::term::decl::{Declar, Hint, Info};
use crate::term::expr::Expr;
use crate::term::intern::Store;
use crate::term::level::Level;
use crate::term::name::Name;
use crate::term::ptr::{ExprPtr, LevelPtr, LevelsPtr, NamePtr};
use std::sync::{Mutex, OnceLock, PoisonError};
use std::thread;

const STACK_BYTES: usize = 256 << 20;

/// The unit hash of every unit start, `None` where the unit references a later or missing name.
pub struct Keys<'a> {
    store: &'a Store<'a>,
    units: Vec<OnceLock<Option<Key>>>,
    pool: Mutex<Vec<Enc<'a>>>,
}

impl<'a> Keys<'a> {
    pub fn new(store: &'a Store<'a>) -> Self {
        Keys {
            store,
            units: (0..store.declars.len()).map(|_| OnceLock::new()).collect(),
            pool: Mutex::default(),
        }
    }

    /// Units only reference earlier units, so waiting on another worker's unit never cycles.
    fn unit_key(&self, start: u32, end: u32) -> Option<Key> {
        *self.units[start as usize].get_or_init(|| {
            let mut enc = self
                .pool
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .pop();
            let enc = enc.get_or_insert_default();
            let k = enc.unit(self, start, end);
            self.pool
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .push(std::mem::take(enc));
            k
        })
    }

    fn unit(&self, i: u32) -> (u32, u32) {
        let name = self.store.declars[i as usize].name();
        self.store
            .blocks
            .get(&name)
            .map_or((i, i + 1), |b| (b.start, b.end))
    }

    fn member(&self, i: u32) -> Option<(Key, u32)> {
        let (start, end) = self.unit(i);
        self.unit_key(start, end).map(|k| (k, i - start))
    }

    /// The cache key of a definition, theorem or opaque, the only declarations a cache skips.
    pub fn get(&self, i: u32) -> Option<Key> {
        match self.store.declars[i as usize] {
            Declar::Def(..) | Declar::Thm(..) | Declar::Opaque(..) => {
                self.member(i).map(|(k, _)| k)
            }
            _ => None,
        }
    }

    /// Covers every declaration the checkers reach by name rather than by reference. Runs on its
    /// own stack, since it hashes the closure of the primitives.
    pub fn environment(&self) -> Option<Key> {
        thread::scope(|sc| {
            thread::Builder::new()
                .stack_size(STACK_BYTES)
                .spawn_scoped(sc, || self.environment_here())
                .expect("spawn key thread")
                .join()
                .unwrap_or_else(|p| std::panic::resume_unwind(p))
        })
    }

    fn environment_here(&self) -> Option<Key> {
        let mut h = blake3::Hasher::new();
        for (path, name) in self.store.names.all() {
            h.update(path.as_bytes());
            match name.and_then(|n| n.decl_idx()) {
                None => h.update(&[0]),
                Some(i) => {
                    let (k, off) = self.member(i)?;
                    h.update(&[1]).update(&k).update(&off.to_le_bytes())
                }
            };
        }
        Some(*h.finalize().as_bytes())
    }
}

#[derive(Default)]
struct Enc<'a> {
    buf: Vec<u8>,
    exprs: FxHashMap<ExprPtr<'a>, u32>,
    nexprs: u32,
    names: FxHashMap<NamePtr<'a>, u32>,
    levels: FxHashMap<LevelPtr<'a>, u32>,
    start: u32,
    end: u32,
}

/// Every record is tagged and refers to earlier records by index, so the bytes decode uniquely.
mod tag {
    pub const ANON: u8 = 0;
    pub const STR: u8 = 1;
    pub const NUM: u8 = 2;
    pub const ZERO: u8 = 3;
    pub const SUCC: u8 = 4;
    pub const MAX: u8 = 5;
    pub const IMAX: u8 = 6;
    pub const PARAM: u8 = 7;
    pub const VAR: u8 = 8;
    pub const SORT: u8 = 9;
    pub const CONST: u8 = 10;
    pub const APP: u8 = 11;
    pub const LAM: u8 = 12;
    pub const PI: u8 = 13;
    pub const LET: u8 = 14;
    pub const PROJ: u8 = 15;
    pub const NAT: u8 = 16;
    pub const STRLIT: u8 = 17;
    pub const OWN: u8 = 18;
    pub const DEP: u8 = 19;
    pub const AXIOM: u8 = 20;
    pub const QUOT: u8 = 21;
    pub const THM: u8 = 22;
    pub const DEF: u8 = 23;
    pub const OPAQUE: u8 = 24;
    pub const IND: u8 = 25;
    pub const CTOR: u8 = 26;
    pub const REC: u8 = 27;
}

impl<'a> Enc<'a> {
    fn unit(&mut self, keys: &Keys<'a>, start: u32, end: u32) -> Option<Key> {
        self.buf.clear();
        self.exprs.clear();
        self.nexprs = 0;
        self.names.clear();
        self.levels.clear();
        (self.start, self.end) = (start, end);
        for i in start..end {
            self.declar(keys, keys.store.declars[i as usize])?;
        }
        Some(*blake3::hash(&self.buf).as_bytes())
    }

    fn u32(&mut self, mut x: u32) {
        while x >= 0x80 {
            self.buf.push(x as u8 | 0x80);
            x >>= 7;
        }
        self.buf.push(x as u8);
    }

    fn bytes(&mut self, b: &[u8]) {
        self.u32(b.len() as u32);
        self.buf.extend_from_slice(b);
    }

    #[inline(always)]
    fn record(&mut self, t: u8, args: &[u32]) {
        self.buf.push(t);
        for &a in args {
            self.u32(a);
        }
    }

    fn name(&mut self, n: NamePtr<'a>) -> u32 {
        if let Some(&i) = self.names.get(&n) {
            return i;
        }
        match n.kind {
            Name::Anon => self.buf.push(tag::ANON),
            Name::Str(p, s, _) => {
                let p = self.name(p);
                self.record(tag::STR, &[p]);
                self.bytes(s.s.as_bytes());
            }
            Name::Num(p, k, _) => {
                let p = self.name(p);
                self.record(tag::NUM, &[p]);
                self.buf.extend_from_slice(&k.to_le_bytes());
            }
        }
        let i = self.names.len() as u32;
        self.names.insert(n, i);
        i
    }

    fn level(&mut self, l: LevelPtr<'a>) -> u32 {
        if let Some(&i) = self.levels.get(&l) {
            return i;
        }
        match *l {
            Level::Zero => self.record(tag::ZERO, &[]),
            Level::Succ(x, _) => {
                let x = self.level(x);
                self.record(tag::SUCC, &[x]);
            }
            Level::Max(x, y, _) | Level::IMax(x, y, _) => {
                let t = if matches!(*l, Level::Max(..)) {
                    tag::MAX
                } else {
                    tag::IMAX
                };
                let (x, y) = (self.level(x), self.level(y));
                self.record(t, &[x, y]);
            }
            Level::Param(n, _) => {
                let n = self.name(n);
                self.record(tag::PARAM, &[n]);
            }
        }
        let i = self.levels.len() as u32;
        self.levels.insert(l, i);
        i
    }

    fn levels(&mut self, ls: LevelsPtr<'a>) -> Vec<u32> {
        ls.iter().map(|&l| self.level(l)).collect()
    }

    /// A constant inside the unit by position, an earlier one by its unit key.
    fn konst(&mut self, keys: &Keys<'a>, n: NamePtr<'a>) -> Option<()> {
        let i = n.decl_idx()?;
        if (self.start..self.end).contains(&i) {
            self.record(tag::OWN, &[i - self.start]);
        } else if i < self.start {
            let (k, off) = keys.member(i)?;
            self.buf.push(tag::DEP);
            self.buf.extend_from_slice(&k);
            self.u32(off);
        } else {
            return None;
        }
        Some(())
    }

    fn konsts(&mut self, keys: &Keys<'a>, ns: &[NamePtr<'a>]) -> Option<()> {
        self.u32(ns.len() as u32);
        ns.iter().try_for_each(|&n| self.konst(keys, n))
    }

    fn next(&mut self) -> u32 {
        self.nexprs += 1;
        self.nexprs - 1
    }

    /// Variables are re-emitted rather than memoized, which is cheaper and still canonical.
    fn expr(&mut self, keys: &Keys<'a>, e: ExprPtr<'a>) -> Option<u32> {
        if let Expr::Var { idx, .. } = *e {
            self.record(tag::VAR, &[u32::from(idx)]);
            return Some(self.next());
        }
        if let Some(&i) = self.exprs.get(&e) {
            return Some(i);
        }
        match *e {
            Expr::Var { .. } => unreachable!(),
            Expr::Sort { level, .. } => {
                let l = self.level(level);
                self.record(tag::SORT, &[l]);
            }
            Expr::Const { name, levels, .. } => {
                let ls = self.levels(levels);
                self.record(tag::CONST, &[ls.len() as u32]);
                ls.iter().for_each(|&l| self.u32(l));
                self.konst(keys, name)?;
            }
            Expr::App { fun, arg, .. } => {
                let (f, a) = (self.expr(keys, fun)?, self.expr(keys, arg)?);
                self.record(tag::APP, &[f, a]);
            }
            Expr::Lam { ty, body, .. } | Expr::Pi { ty, body, .. } => {
                let t = if e.is_lambda() { tag::LAM } else { tag::PI };
                let (x, y) = (self.expr(keys, ty)?, self.expr(keys, body)?);
                self.record(t, &[x, y]);
            }
            Expr::Let { data, .. } => {
                let ty = self.expr(keys, data.ty)?;
                let val = self.expr(keys, data.val)?;
                let body = self.expr(keys, data.body)?;
                self.record(tag::LET, &[ty, val, body, u32::from(data.nondep)]);
            }
            Expr::Proj {
                name, idx, e: x, ..
            } => {
                let x = self.expr(keys, x)?;
                self.record(tag::PROJ, &[u32::from(idx), x]);
                self.konst(keys, name)?;
            }
            Expr::NatLit { n, .. } => {
                self.buf.push(tag::NAT);
                self.bytes(&n.to_bytes_le());
            }
            Expr::StrLit { s, .. } => {
                self.buf.push(tag::STRLIT);
                self.bytes(s.s.as_bytes());
            }
            Expr::Local { .. } => return None,
        }
        let i = self.next();
        self.exprs.insert(e, i);
        Some(i)
    }

    fn info(&mut self, keys: &Keys<'a>, t: u8, i: &Info<'a>) -> Option<()> {
        let n = self.name(i.name);
        let us = self.levels(i.uparams);
        let ty = self.expr(keys, i.ty)?;
        self.record(t, &[n, ty, us.len() as u32]);
        us.iter().for_each(|&u| self.u32(u));
        Some(())
    }

    fn declar(&mut self, keys: &Keys<'a>, d: Declar<'a>) -> Option<()> {
        match d {
            Declar::Axiom(i) => self.info(keys, tag::AXIOM, &i),
            Declar::Quot(i) => self.info(keys, tag::QUOT, &i),
            Declar::Thm(i, v) => {
                let v = self.expr(keys, v)?;
                self.info(keys, tag::THM, &i)?;
                self.u32(v);
                Some(())
            }
            Declar::Opaque(i, v) => {
                let v = self.expr(keys, v)?;
                self.info(keys, tag::OPAQUE, &i)?;
                self.u32(v);
                Some(())
            }
            Declar::Def(i, v, h) => {
                let v = self.expr(keys, v)?;
                self.info(keys, tag::DEF, &i)?;
                let h = match h {
                    Hint::Opaque => 0,
                    Hint::Abbrev => 1,
                    Hint::Regular(k) => u64::from(k) + 2,
                };
                self.u32(v);
                self.buf.extend_from_slice(&h.to_le_bytes());
                Some(())
            }
            Declar::Ind(x) => {
                self.info(keys, tag::IND, &x.info)?;
                self.record(
                    tag::IND,
                    &[
                        u32::from(x.is_rec),
                        x.num_nested as u32,
                        u32::from(x.is_reflexive),
                        u32::from(x.num_params),
                        u32::from(x.num_indices),
                    ],
                );
                self.konsts(keys, x.all)?;
                self.konsts(keys, x.ctors)
            }
            Declar::Ctor(x) => {
                self.info(keys, tag::CTOR, &x.info)?;
                self.record(
                    tag::CTOR,
                    &[
                        u32::from(x.cidx),
                        u32::from(x.num_params),
                        u32::from(x.num_fields),
                    ],
                );
                self.konst(keys, x.induct)
            }
            Declar::Rec(x) => {
                self.info(keys, tag::REC, &x.info)?;
                self.record(
                    tag::REC,
                    &[
                        u32::from(x.num_params),
                        u32::from(x.num_indices),
                        u32::from(x.num_motives),
                        u32::from(x.num_minors),
                        u32::from(x.is_k),
                        x.rules.len() as u32,
                    ],
                );
                self.konsts(keys, x.all)?;
                for r in x.rules {
                    let rhs = self.expr(keys, r.rhs)?;
                    self.record(tag::REC, &[u32::from(r.nfields), rhs]);
                    self.konst(keys, r.ctor)?;
                }
                Some(())
            }
        }
    }
}
