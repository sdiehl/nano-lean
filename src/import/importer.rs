use super::scan::{self, Batch, Line};
use super::{Result, invalid, unsupported};
use crate::hash64;
use crate::term::FxHashMap;
use crate::term::arena::Arena;
use crate::term::decl::Declar;
use crate::term::expr::{Expr, LetData, Meta, NLB_MASK, mk};
use crate::term::intern::{Block, Dag, Names, Stats, Store};
use crate::term::level::{IMAX_HASH, Level, MAX_HASH, PARAM_HASH, SUCC_HASH};
use crate::term::name::{NUM_HASH, Name, STR_HASH};
use crate::term::ptr::{ExprPtr, LevelPtr, LevelsPtr, NamePtr};
use num_bigint::BigUint;
use serde_json::Value;

pub(super) const BYTES_PER_LINE: usize = 56;
const BVAR_LIMIT: u16 = NLB_MASK - 1;

pub(super) struct Importer<'a> {
    pub(super) arena: &'a Arena,
    pub(super) dag: Dag<'a>,
    pub(super) anon: NamePtr<'a>,
    zero: LevelPtr<'a>,
    names: Table<NamePtr<'a>>,
    levels: Table<LevelPtr<'a>>,
    exprs: Table<ExprPtr<'a>>,
    pub(super) declars: Vec<Declar<'a>>,
    pub(super) blocks: FxHashMap<NamePtr<'a>, Block>,
    pub(super) stats: Stats,
    scratch: Vec<u32>,
    aliases: Vec<u32>,
}

const MAX_GAP: usize = 1 << 16;

/// Ids far past the dense end go to `sparse`, so a forged id cannot force a huge allocation.
struct Table<T> {
    dense: Vec<Option<T>>,
    sparse: FxHashMap<u32, T>,
}

impl<T: Copy> Table<T> {
    fn new(dense: Vec<Option<T>>) -> Self {
        Self {
            dense,
            sparse: FxHashMap::default(),
        }
    }

    #[inline]
    fn get(&self, i: u32) -> Result<T> {
        match self.dense.get(i as usize) {
            Some(Some(x)) => Ok(*x),
            _ => self.get_sparse(i),
        }
    }

    #[cold]
    #[inline(never)]
    fn get_sparse(&self, i: u32) -> Result<T> {
        match self.sparse.get(&i) {
            Some(x) => Ok(*x),
            None => invalid("unknown or forward reference"),
        }
    }

    #[inline]
    fn put(&mut self, i: u32, x: T) -> Result<()> {
        let k = i as usize;
        if k == self.dense.len() && self.sparse.is_empty() {
            self.dense.push(Some(x));
            return Ok(());
        }
        if !self.sparse.is_empty() || k >= self.dense.len() + MAX_GAP {
            return self.put_sparse(i, x);
        }
        if self.dense.len() <= k {
            self.dense.resize_with(k + 1, || None);
        }
        if self.dense[k].is_some() {
            return invalid("duplicate index");
        }
        self.dense[k] = Some(x);
        Ok(())
    }

    #[cold]
    #[inline(never)]
    fn put_sparse(&mut self, i: u32, x: T) -> Result<()> {
        let k = i as usize;
        if self.sparse.contains_key(&i) || self.dense.get(k).is_some_and(Option::is_some) {
            return invalid("duplicate index");
        }
        if k >= self.dense.len() + MAX_GAP {
            self.sparse.insert(i, x);
        } else {
            if self.dense.len() <= k {
                self.dense.resize_with(k + 1, || None);
            }
            self.dense[k] = Some(x);
        }
        Ok(())
    }
}

impl<'a> Importer<'a> {
    pub(super) fn new(arena: &'a Arena, bytes: usize) -> Self {
        let lines = bytes / BYTES_PER_LINE;
        let mut dag = Dag::with_capacity(lines);
        let anon = dag.add_name(arena, Name::Anon);
        let zero = dag.add_level(arena, Level::Zero);
        Self {
            arena,
            dag,
            anon,
            zero,
            names: Table::new(vec![Some(anon)]),
            levels: Table::new(vec![Some(zero)]),
            exprs: Table::new(Vec::with_capacity(lines)),
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

    pub(super) fn lines(&mut self, bytes: &[u8], n: &mut usize) -> Result<()> {
        let mut start = 0;
        for end in memchr::memchr_iter(b'\n', bytes).chain([bytes.len()]) {
            let line = &bytes[start..];
            self.raw_line(line, end - start, n)?;
            start = end + 1;
        }
        Ok(())
    }

    pub(super) fn finish_lines(self, n: usize) -> Result<Store<'a>> {
        if n == 0 {
            return invalid("empty export");
        }
        self.finish()
    }

    pub(super) fn name(&self, i: u32) -> Result<NamePtr<'a>> {
        self.names.get(i)
    }

    fn level(&self, i: u32) -> Result<LevelPtr<'a>> {
        self.levels.get(i)
    }

    pub(super) fn expr(&self, i: u32) -> Result<ExprPtr<'a>> {
        self.exprs.get(i)
    }

    fn add_name(&mut self, i: u32, n: Name<'a>) -> Result<()> {
        let p = self.dag.intern_name(self.arena, n);
        self.stats.names += 1;
        self.names.put(i, p)
    }

    pub(super) fn do_str(&mut self, i: u32, pre: u32, s: &str) -> Result<()> {
        let pre = self.name(pre)?;
        let s = self.dag.intern_str(self.arena, s);
        self.add_name(i, Name::Str(pre, s, hash64!(STR_HASH, pre, s)))
    }

    pub(super) fn do_num(&mut self, i: u32, pre: u32, n: u64) -> Result<()> {
        let pre = self.name(pre)?;
        self.add_name(i, Name::Num(pre, n, hash64!(NUM_HASH, pre, n)))
    }

    fn add_level(&mut self, i: u32, l: Level<'a>) -> Result<()> {
        let p = self.dag.intern_level(self.arena, l);
        self.stats.levels += 1;
        self.levels.put(i, p)
    }

    pub(super) fn do_succ(&mut self, i: u32, l: u32) -> Result<()> {
        let l = self.level(l)?;
        self.add_level(i, Level::Succ(l, hash64!(SUCC_HASH, l)))
    }

    pub(super) fn do_max(&mut self, i: u32, a: u32, b: u32, imax: bool) -> Result<()> {
        let (a, b) = (self.level(a)?, self.level(b)?);
        let l = if imax {
            Level::IMax(a, b, hash64!(IMAX_HASH, a, b))
        } else {
            Level::Max(a, b, hash64!(MAX_HASH, a, b))
        };
        self.add_level(i, l)
    }

    pub(super) fn do_param(&mut self, i: u32, n: u32) -> Result<()> {
        let n = self.name(n)?;
        self.add_level(i, Level::Param(n, hash64!(PARAM_HASH, n)))
    }

    /// Exported nodes are already shared, so the table is bulk filled once at the end.
    fn intern(&mut self, (e, nlb): (Expr<'a>, Meta)) -> ExprPtr<'a> {
        ExprPtr::new(self.arena.alloc(e), nlb)
    }

    pub(super) fn alias(&mut self, i: u32, e: u32) -> Result<()> {
        let e = self.expr(e)?;
        self.stats.expressions += 1;
        self.aliases.push(i);
        self.exprs.put(i, e)
    }

    fn add_expr(&mut self, i: u32, node: (Expr<'a>, Meta)) -> Result<()> {
        let p = self.intern(node);
        self.stats.expressions += 1;
        self.exprs.put(i, p)
    }

    pub(super) fn do_bvar(&mut self, i: u32, v: u64) -> Result<()> {
        match u16::try_from(v) {
            Ok(v) if v < BVAR_LIMIT => self.add_expr(i, mk::var(v)),
            _ => unsupported("bound variable index too large"),
        }
    }

    pub(super) fn do_sort(&mut self, i: u32, l: u32) -> Result<()> {
        let l = self.level(l)?;
        self.add_expr(i, mk::sort(l))
    }

    pub(super) fn do_const(&mut self, i: u32, n: u32, us: &[u32]) -> Result<()> {
        let n = self.name(n)?;
        let us = self.level_list(us)?;
        self.add_expr(i, mk::konst(n, us))
    }

    fn level_list(&mut self, us: &[u32]) -> Result<LevelsPtr<'a>> {
        let ls = us
            .iter()
            .map(|&u| self.level(u))
            .collect::<Result<Vec<_>>>()?;
        Ok(self.dag.intern_levels(self.arena, &ls))
    }

    pub(super) fn do_app(&mut self, i: u32, f: u32, a: u32) -> Result<()> {
        let (f, a) = (self.expr(f)?, self.expr(a)?);
        self.add_expr(i, mk::app(f, a))
    }

    pub(super) fn do_binder(
        &mut self,
        i: u32,
        name: u32,
        ty: u32,
        body: u32,
        lam: bool,
    ) -> Result<()> {
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

    pub(super) fn do_let(
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

    pub(super) fn do_proj(&mut self, i: u32, n: u32, idx: u64, e: u32) -> Result<()> {
        let n = self.name(n)?;
        let e = self.expr(e)?;
        let Ok(idx) = u16::try_from(idx) else {
            return unsupported("projection index too large");
        };
        self.add_expr(i, mk::proj(n, idx, e))
    }

    pub(super) fn do_nat(&mut self, i: u32, digits: &str) -> Result<()> {
        if digits.is_empty() || !digits.bytes().all(|c| c.is_ascii_digit()) {
            return invalid("invalid natural literal");
        }
        let Some(n) = BigUint::parse_bytes(digits.as_bytes(), 10) else {
            return invalid("invalid natural literal");
        };
        let n = self.dag.intern_nat(self.arena, n);
        self.add_expr(i, mk::nat(n))
    }

    pub(super) fn do_strlit(&mut self, i: u32, s: &str) -> Result<()> {
        let s = self.dag.intern_str(self.arena, s);
        self.add_expr(i, mk::str(s))
    }

    /// Only the first `len` bytes of `b` are the line, the rest give the scanner read slack.
    #[inline(always)]
    fn line(&mut self, b: &[u8], len: usize, first: bool) -> Result<()> {
        if !first && let Some((l, _)) = scan::fast(b, len, &mut self.scratch) {
            if l.listed() {
                let us = std::mem::take(&mut self.scratch);
                let r = self.listed(l, &us);
                self.scratch = us;
                return r;
            }
            return self.apply(l, b);
        }
        let v: Value = serde_json::from_slice(&b[..len])?;
        self.general(&v, first)
    }

    #[inline(always)]
    pub(super) fn raw_line(&mut self, b: &[u8], len: usize, n: &mut usize) -> Result<()> {
        if len > 0 {
            self.line(b, len, *n == 0).map_err(|e| e.at("line", *n))?;
            *n += 1;
        }
        Ok(())
    }

    /// Applies a scanned chunk, completing the line `carry` holds from earlier chunks.
    pub(super) fn batch(&mut self, b: &Batch, carry: &mut Vec<u8>, n: &mut usize) -> Result<()> {
        let Some((first, last)) = b.body else {
            carry.extend_from_slice(&b.buf);
            return Ok(());
        };
        let mut head = std::mem::take(carry);
        head.extend_from_slice(&b.buf[..first]);
        self.raw_line(&head, head.len(), n)?;
        let mut us = &b.us[..];
        for &(s, e, l) in &b.lines {
            let raw = &b.buf[s as usize..e as usize];
            let r = match l {
                Some(l) if l.listed() => {
                    let (now, rest) = us[1..].split_at(us[0] as usize);
                    us = rest;
                    if *n == 0 {
                        None
                    } else {
                        Some(self.listed(l, now))
                    }
                }
                Some(l) if *n != 0 => Some(self.apply(l, raw)),
                _ => None,
            };
            let r = r.unwrap_or_else(|| {
                let v: Value = serde_json::from_slice(raw)?;
                self.general(&v, *n == 0)
            });
            r.map_err(|e| e.at("line", *n))?;
            *n += 1;
        }
        head.clear();
        head.extend_from_slice(&b.buf[last + 1..]);
        *carry = head;
        Ok(())
    }

    fn listed(&mut self, l: Line, us: &[u32]) -> Result<()> {
        match l {
            Line::Const(i, n) => self.do_const(i, n, us),
            Line::Thm(n, ty, val) => self.do_thm(n, us, ty, val),
            Line::Def(n, ty, val, h) => self.do_def(n, us, ty, val, h, "safe"),
            _ => unreachable!("only listed lines carry a universe list"),
        }
    }

    #[inline(always)]
    fn apply(&mut self, l: Line, b: &[u8]) -> Result<()> {
        match l {
            Line::Str(i, pre, s, e) => match std::str::from_utf8(&b[s as usize..e as usize]) {
                Ok(s) => self.do_str(i, pre, s),
                Err(_) => invalid("invalid string"),
            },
            Line::Num(i, pre, n) => self.do_num(i, pre, n),
            Line::Succ(i, l) => self.do_succ(i, l),
            Line::Max(i, a, c, imax) => self.do_max(i, a, c, imax),
            Line::Param(i, n) => self.do_param(i, n),
            Line::App(i, f, a) => self.do_app(i, f, a),
            Line::Bvar(i, v) => self.do_bvar(i, v),
            Line::Sort(i, l) => self.do_sort(i, l),
            Line::Const(..) | Line::Thm(..) | Line::Def(..) => {
                unreachable!("listed lines carry their universe list separately")
            }
            Line::Binder(i, name, ty, body, lam) => self.do_binder(i, name, ty, body, lam),
            Line::Let(i, name, ty, val, body, nondep) => {
                self.do_let(i, name, ty, val, body, nondep)
            }
            Line::Proj(i, n, idx, e) => self.do_proj(i, n, idx, e),
        }
    }

    pub(super) fn finish(mut self) -> Result<Store<'a>> {
        self.names = Table::new(Vec::new());
        self.levels = Table::new(Vec::new());
        self.aliases.sort_unstable();
        let all = &self.aliases;
        let mut aliases = all.iter().copied().peekable();
        let sparse = self
            .exprs
            .sparse
            .iter()
            .filter(|(i, _)| all.binary_search(i).is_err())
            .map(|(_, &e)| e);
        let fresh = self.stats.expressions - self.aliases.len();
        self.dag.exprs.fill(
            fresh,
            (0..)
                .zip(&self.exprs.dense)
                .filter(move |(i, _)| aliases.next_if_eq(i).is_none())
                .filter_map(|(_, e)| *e)
                .chain(sparse)
                .map(ExprPtr::as_ref),
        );
        let names = Names::build(&self.dag, self.anon);
        for n in [names.quot, names.quot_mk, names.quot_lift, names.quot_ind]
            .into_iter()
            .flatten()
        {
            if let Some(i) = n.decl_idx()
                && !matches!(self.declars[i as usize], Declar::Quot(_))
            {
                return invalid(format!("reserved quotient name {n}"));
            }
        }
        let store = Store {
            dag: self.dag,
            anon: self.anon,
            zero: self.zero,
            declars: self.declars,
            blocks: self.blocks,
            names,
            stats: self.stats,
        };
        super::primitives::check(&store)?;
        Ok(store)
    }
}

#[cfg(test)]
mod tests {
    use crate::import::import_bytes;
    use crate::term::arena::Arena;

    const META: &str = r#"{"meta":{"format":{"version":"3.1.0"}}}"#;

    #[test]
    fn far_ids_stay_sparse_and_unique() {
        let far = r#"{"in":4000000000,"str":{"pre":0,"str":"x"}}"#;
        let reuse = r#"{"in":1,"str":{"pre":4000000000,"str":"y"}}"#;
        let ok = format!("{META}\n{far}\n{reuse}\n");
        assert!(import_bytes(&Arena::new(), ok.as_bytes()).is_ok());
        let dup = format!("{META}\n{far}\n{far}\n");
        assert!(import_bytes(&Arena::new(), dup.as_bytes()).is_err());
    }
}
