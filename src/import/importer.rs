use super::scan::{self, Batch, Line, Scanned};
use crate::error::{Result, invalid, unsupported};
use crate::hash64;
use crate::term::FxHashMap;
use crate::term::arena::Arena;
use crate::term::decl::Declar;
use crate::term::expr::{Expr, LetData, Meta, NLB_MASK, mk};
use crate::term::intern::{Block, Dag, Deps, Names, Stats, Store};
use crate::term::level::{IMAX_HASH, Level, MAX_HASH, PARAM_HASH, SUCC_HASH};
use crate::term::name::{NUM_HASH, Name, STR_HASH};
use crate::term::ptr::{ExprPtr, LevelPtr, LevelsPtr, NamePtr};
use num_bigint::BigUint;
use serde_json::Value;

pub(super) const BYTES_PER_LINE: usize = 56;
/// How many scanned lines ahead the builder starts loading what a line will read. The tables
/// and the arena are far larger than any cache, so these loads otherwise stall it one by one.
const AHEAD_SLOTS: usize = 16;
const AHEAD_NODES: usize = 8;

/// Hints that `p` will be read soon. A hint reads nothing, so any address is allowed.
#[inline(always)]
fn prefetch<T>(p: *const T) {
    #[cfg(target_arch = "aarch64")]
    // SAFETY: `prfm` is a hint that never faults and changes no state.
    unsafe {
        std::arch::asm!("prfm pldl1keep, [{0}]", in(reg) p, options(nostack, preserves_flags, readonly));
    }
    #[cfg(target_arch = "x86_64")]
    // SAFETY: a prefetch hint never faults and changes no state.
    unsafe {
        std::arch::x86_64::_mm_prefetch(p.cast::<i8>(), std::arch::x86_64::_MM_HINT_T0);
    }
}
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
    deps: Recorder<'a>,
    /// Set while a recording thread holds `deps`, which then gets the events instead.
    log: Option<Log<'a>>,
    track: bool,
    pub(super) imported: u64,
    own: u32,
}

/// Records which earlier declarations each declaration's lines reach. Every node keeps a summary
/// of the constants under it: none, one declaration, or many, standing for the declaration that
/// follows the node, which uses it and so reaches all of them.
#[derive(Default)]
pub(super) struct Recorder<'a> {
    /// Per expression id, 0, `j + 1` for declaration `j` alone, or `MANY | d`.
    sum: Vec<u32>,
    /// Summary of the node being built.
    acc: u32,
    /// First expression id after the latest declaration.
    start: u32,
    /// Per declaration, the last declaration that marked it, to keep `out.decls` distinct.
    stamp: Vec<u32>,
    /// Constants not yet declared, which only a declaration's own block may name.
    pending: Vec<NamePtr<'a>>,
    /// Set by a replay that met an id out of order, which ends the record as it does inline.
    broken: bool,
    out: Deps<'a>,
}

const MANY: u32 = 1 << 31;

impl<'a> Recorder<'a> {
    #[inline(always)]
    fn join(&mut self, s: u32) {
        if self.acc == 0 {
            self.acc = s;
        } else if s != 0 && s != self.acc {
            self.acc = MANY;
        }
    }

    #[inline(always)]
    fn child(&mut self, i: u32, here: u32) {
        let Some(&s) = self.sum.get(i as usize) else {
            return;
        };
        self.join(s);
        if i < self.start && s != 0 {
            self.mark(if s & MANY != 0 { s & !MANY } else { s - 1 }, here);
        }
    }

    #[inline(always)]
    fn constant(&mut self, j: u32, here: u32) {
        self.join(j + 1);
        self.mark(j, here);
    }

    #[inline(always)]
    fn node(&mut self, here: u32) {
        let s = if self.acc & MANY != 0 {
            MANY | here
        } else {
            self.acc
        };
        self.sum.push(s);
        self.acc = 0;
    }

    #[inline(always)]
    fn mark(&mut self, j: u32, here: u32) {
        let s = &mut self.stamp[j as usize];
        if *s != here + 1 {
            *s = here + 1;
            self.out.decls.push(j);
        }
    }

    #[inline(always)]
    fn undeclared(&mut self, n: NamePtr<'a>) {
        self.acc = MANY;
        self.pending.push(n);
    }

    fn flush(&mut self) {
        self.stamp.push(0);
        self.out.names.append(&mut self.pending);
        let ends = (self.out.decls.len() as u32, self.out.names.len() as u32);
        self.out.ends.push(ends);
        self.start = self.sum.len() as u32;
        self.acc = 0;
    }

    /// Replays a batch. Lines the builder logged take their events from `ev`, and the others,
    /// plain expressions, are read off the scanned lines. `here` carries between batches.
    pub(super) fn replay(&mut self, lines: &[Scanned], ev: &Events<'a>, here: &mut u32) {
        let (mut args, mut names) = (ev.args.iter().copied(), ev.names.iter().copied());
        let mut arg = || args.next().unwrap_or(0);
        let mut next = 0;
        for &op in &ev.ops {
            if self.broken {
                return;
            }
            match op {
                LINE => {
                    let k = arg() as usize;
                    let Some(before) = lines.get(next..k) else {
                        self.broken = true;
                        return;
                    };
                    self.plain(before, *here);
                    next = k + 1;
                }
                CHILD => self.child(arg(), *here),
                NODE => self.ranged(arg(), *here),
                CONSTANT => self.constant(arg(), *here),
                UNDECLARED => names.next().into_iter().for_each(|n| self.undeclared(n)),
                HERE => *here = arg(),
                _ => self.flush(),
            }
        }
        match lines.get(next..) {
            Some(rest) => self.plain(rest, *here),
            None => self.broken = true,
        }
    }

    /// What the builder's `expr` and `ranged` calls record for lines it applied without logging.
    fn plain(&mut self, lines: &[Scanned], here: u32) {
        for (k, &(_, _, l)) in lines.iter().enumerate() {
            if self.broken {
                return;
            }
            // A summary is read at random from a table far larger than any cache.
            if let Some(&(_, _, Some(l))) = lines.get(k + AHEAD_SLOTS)
                && let Some((x, y)) = Importer::children(l)
            {
                prefetch(self.sum.as_ptr().wrapping_add(x as usize));
                prefetch(self.sum.as_ptr().wrapping_add(y as usize));
            }
            let (i, children) = match l {
                Some(Line::App(i, f, a)) => (i, [f, a, NONE]),
                Some(Line::Binder { id, ty, body, .. }) => (id, [ty, body, NONE]),
                Some(Line::Let {
                    id, ty, val, body, ..
                }) => (id, [ty, val, body]),
                Some(Line::Bvar(i, _) | Line::Sort(i, _)) => (i, [NONE; 3]),
                _ => continue,
            };
            for c in children {
                self.child(c, here);
            }
            self.ranged(i, here);
        }
    }

    #[inline(always)]
    fn ranged(&mut self, i: u32, here: u32) {
        if self.sum.len() == i as usize {
            self.node(here);
        } else {
            self.broken = true;
        }
    }
}

/// No expression has this id, `child` ignores ids past the summaries, so it stands for no child.
const NONE: u32 = u32::MAX;

const LINE: u8 = 0;
const CHILD: u8 = 1;
const NODE: u8 = 2;
const CONSTANT: u8 = 3;
const UNDECLARED: u8 = 4;
const HERE: u8 = 5;
const FLUSH: u8 = 6;

/// What a batch's lines record beyond what the scanned lines show: the constants they name and
/// the declarations they add, each line's events after its index. A summary lookup stalls on
/// memory and the builder is the one thread a threaded import waits on, so another replays them.
#[derive(Default)]
pub(super) struct Events<'a> {
    ops: Vec<u8>,
    args: Vec<u32>,
    names: Vec<NamePtr<'a>>,
}

struct Log<'a> {
    ev: Events<'a>,
    /// Off while the builder applies a line the replay reads off the scan.
    on: bool,
    /// The declaration count the replay holds.
    here: u32,
}

impl<'a> Log<'a> {
    /// Logs an event of a line that has `here` declarations before it at this point.
    #[inline(always)]
    fn op(&mut self, op: u8, arg: u32, here: u32) {
        self.at(here);
        self.ev.ops.push(op);
        self.ev.args.push(arg);
    }

    #[inline(always)]
    fn at(&mut self, here: u32) {
        if self.here != here {
            self.here = here;
            self.ev.ops.push(HERE);
            self.ev.args.push(here);
        }
    }

    fn uses(&mut self, n: NamePtr<'a>, here: u32) {
        match n.decl_idx() {
            Some(j) => self.op(CONSTANT, j, here),
            None => {
                self.at(here);
                self.ev.ops.push(UNDECLARED);
                self.ev.names.push(n);
            }
        }
    }
}

/// Smaller inputs check too quickly for their order to matter.
const RECORD_BYTES: usize = 64 << 20;

const MAX_GAP: usize = 1 << 16;
/// Decimal parsing is quadratic, so 4M digits would already take 10s.
const MAX_NAT_DIGITS: usize = 1 << 16;

/// Empty dense slots stay within `MAX_GAP` or the filled count, so ids that would open more go to
/// `sparse` and forged ids cannot force an allocation beyond the input's size.
struct Table<T> {
    dense: Vec<Option<T>>,
    sparse: FxHashMap<u32, T>,
    holes: usize,
}

impl<T: Copy> Table<T> {
    fn new(dense: Vec<Option<T>>) -> Self {
        Self {
            dense,
            sparse: FxHashMap::default(),
            holes: 0,
        }
    }

    fn filled(&self) -> usize {
        self.dense.len() - self.holes + self.sparse.len()
    }

    fn fits(&self, k: usize) -> bool {
        let open = self.holes + k.saturating_sub(self.dense.len());
        open <= MAX_GAP.max(self.dense.len() - self.holes)
    }

    fn place(&mut self, k: usize, x: T) {
        if self.dense.len() <= k {
            self.holes += k - self.dense.len();
            self.dense.resize_with(k + 1, || None);
        } else {
            self.holes -= 1;
        }
        self.dense[k] = Some(x);
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
            None => Err(invalid("unknown or forward reference")),
        }
    }

    #[inline(always)]
    fn put(&mut self, i: u32, x: T) -> Result<()> {
        let k = i as usize;
        if k == self.dense.len() && k < self.dense.capacity() && self.sparse.is_empty() {
            self.dense.push(Some(x));
            return Ok(());
        }
        self.put_slow(i, x)
    }

    #[cold]
    #[inline(never)]
    fn put_slow(&mut self, i: u32, x: T) -> Result<()> {
        let k = i as usize;
        if k == self.dense.len() && self.sparse.is_empty() {
            self.dense.push(Some(x));
            return Ok(());
        }
        if !self.sparse.is_empty() || !self.fits(k) {
            return self.put_sparse(i, x);
        }
        if self.dense.get(k).is_some_and(Option::is_some) {
            return Err(invalid("duplicate index"));
        }
        self.place(k, x);
        Ok(())
    }

    #[cold]
    #[inline(never)]
    fn put_sparse(&mut self, i: u32, x: T) -> Result<()> {
        let k = i as usize;
        if self.sparse.contains_key(&i) || self.dense.get(k).is_some_and(Option::is_some) {
            return Err(invalid("duplicate index"));
        }
        if self.fits(k) {
            self.place(k, x);
        } else {
            self.sparse.insert(i, x);
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
            deps: Recorder {
                sum: Vec::with_capacity(lines),
                stamp: vec![0],
                ..Recorder::default()
            },
            log: None,
            track: bytes == 0 || bytes >= RECORD_BYTES,
            imported: 0,
            own: 0,
        }
    }

    pub(super) fn lines(&mut self, bytes: &[u8], n: &mut usize) -> Result<()> {
        let mut s = 0;
        while s < bytes.len() {
            if *n != 0 {
                let (t, k) = self.apps(bytes, s);
                (s, *n) = (t, *n + k);
                if s >= bytes.len() {
                    break;
                }
            }
            let b = &bytes[s..];
            if *n != 0
                && let Some((l, e)) = scan::fast(b, usize::MAX, &mut self.scratch)
            {
                self.scanned(l, b).map_err(|e| e.at("line", *n))?;
                *n += 1;
                s += e + 1;
                continue;
            }
            let len = memchr::memchr(b'\n', b).unwrap_or(b.len());
            self.raw_line(b, len, n)?;
            s += len + 1;
        }
        Ok(())
    }

    /// Builds the run of application lines from `s` that take the dense fast path, in a loop
    /// small enough to keep its constants in registers. Returns where the run stops and its
    /// length, leaving any other line, and every error, to the general path.
    #[inline(never)]
    fn apps(&mut self, bytes: &[u8], mut s: usize) -> (usize, usize) {
        if !self.exprs.sparse.is_empty() {
            return (s, 0);
        }
        let arena = self.arena;
        let mut dense = std::mem::take(&mut self.exprs.dense);
        let mut deps = std::mem::take(&mut self.deps);
        let (track, here) = (self.track, self.declars.len() as u32);
        let start = dense.len();
        while let Some(w) = bytes[s..].first_chunk::<{ scan::WIN }>()
            && w[2] == b'a'
            && let Some((e, fa, aa, j)) = scan::app(w, usize::MAX)
            && e as usize == dense.len()
            && dense.len() < dense.capacity()
            && let Some(&Some(f)) = dense.get(fa as usize)
            && let Some(&Some(a)) = dense.get(aa as usize)
        {
            if track {
                deps.child(fa, here);
                deps.child(aa, here);
                deps.node(here);
            }
            let (node, nlb) = mk::app(f, a);
            dense.push(Some(ExprPtr::new(arena.alloc(node), nlb)));
            s += j + 1;
        }
        let k = dense.len() - start;
        self.exprs.dense = dense;
        self.deps = deps;
        (s, k)
    }

    pub(super) fn finish_lines(self, n: usize) -> Result<Store<'a>> {
        if n == 0 {
            return Err(invalid("empty export"));
        }
        self.finish()
    }

    pub(super) fn name(&self, i: u32) -> Result<NamePtr<'a>> {
        self.names.get(i)
    }

    fn level(&self, i: u32) -> Result<LevelPtr<'a>> {
        self.levels.get(i)
    }

    #[inline(always)]
    pub(super) fn expr(&mut self, i: u32) -> Result<ExprPtr<'a>> {
        let here = self.declars.len() as u32;
        match &mut self.log {
            Some(log) if log.on => log.op(CHILD, i, here),
            Some(_) => {}
            None => self.deps.child(i, here),
        }
        self.exprs.get(i)
    }

    #[inline(always)]
    fn ranged(&mut self, i: u32) {
        if !self.track {
            return;
        }
        let here = self.declars.len() as u32;
        match &mut self.log {
            Some(log) if log.on => log.op(NODE, i, here),
            Some(_) => {}
            None if self.deps.sum.len() == i as usize => self.deps.node(here),
            None => self.track = false,
        }
    }

    #[inline]
    fn uses(&mut self, n: NamePtr<'a>) {
        if !self.track {
            return;
        }
        let here = self.declars.len() as u32;
        match (&mut self.log, n.decl_idx()) {
            (Some(log), _) => log.uses(n, here),
            (None, Some(j)) => self.deps.constant(j, here),
            (None, None) => self.deps.undeclared(n),
        }
    }

    pub(super) fn flush_deps(&mut self) {
        if !self.track {
            return;
        }
        match &mut self.log {
            Some(log) => log.ev.ops.push(FLUSH),
            None => self.deps.flush(),
        }
    }

    /// Hands the recorder to a thread that replays each batch with what `logged` returns.
    pub(super) fn record_apart(&mut self) -> Recorder<'a> {
        self.log = Some(Log {
            ev: Events::default(),
            on: self.track,
            here: 0,
        });
        let mut deps = std::mem::take(&mut self.deps);
        deps.broken = !self.track;
        deps
    }

    /// The events since the last call, leaving the emptied `spare` to fill.
    pub(super) fn logged(&mut self, mut spare: Events<'a>) -> Events<'a> {
        spare.ops.clear();
        spare.args.clear();
        spare.names.clear();
        match &mut self.log {
            Some(log) => std::mem::replace(&mut log.ev, spare),
            None => spare,
        }
    }

    /// Takes the recorder back once it has replayed every batch.
    pub(super) fn recorded(&mut self, deps: Recorder<'a>) {
        self.log = None;
        self.track &= !deps.broken;
        self.deps = deps;
    }

    /// Logs the line at `k` of a batch, or leaves it to the replay if its scan shows all it
    /// records, which only holds for a line that is applied as scanned.
    #[inline(always)]
    fn log_line(&mut self, k: usize, plain: bool) {
        if let Some(log) = &mut self.log
            && self.track
        {
            log.on = !plain;
            if !plain {
                log.ev.ops.push(LINE);
                log.ev.args.push(k as u32);
            }
        }
    }

    /// Ends a logged line, telling the replay of the declarations it added.
    #[inline(always)]
    fn log_end(&mut self) {
        if let Some(log) = &mut self.log
            && self.track
        {
            log.at(self.declars.len() as u32);
            log.on = true;
        }
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

    /// Exported nodes are already shared and checking never looks them up, so they are only allocated.
    fn intern(&mut self, (e, nlb): (Expr<'a>, Meta)) -> ExprPtr<'a> {
        ExprPtr::new(self.arena.alloc(e), nlb)
    }

    pub(super) fn alias(&mut self, i: u32, e: u32) -> Result<()> {
        let e = self.expr(e)?;
        self.exprs.put(i, e)?;
        self.ranged(i);
        Ok(())
    }

    fn add_expr(&mut self, i: u32, node: (Expr<'a>, Meta)) -> Result<()> {
        let p = self.intern(node);
        self.exprs.put(i, p)?;
        self.ranged(i);
        Ok(())
    }

    pub(super) fn do_bvar(&mut self, i: u32, v: u64) -> Result<()> {
        match u16::try_from(v) {
            Ok(v) if v < BVAR_LIMIT => self.add_expr(i, mk::var(v)),
            _ => Err(unsupported("bound variable index too large")),
        }
    }

    pub(super) fn do_sort(&mut self, i: u32, l: u32) -> Result<()> {
        let l = self.level(l)?;
        self.add_expr(i, mk::sort(l))
    }

    pub(super) fn do_const(&mut self, i: u32, n: u32, us: &[u32]) -> Result<()> {
        let n = self.name(n)?;
        let us = self.level_list(us)?;
        self.uses(n);
        self.add_expr(i, mk::konst(n, us))
    }

    fn level_list(&mut self, us: &[u32]) -> Result<LevelsPtr<'a>> {
        let ls = us
            .iter()
            .map(|&u| self.level(u))
            .collect::<Result<Vec<_>>>()?;
        Ok(self.dag.intern_levels(self.arena, &ls))
    }

    #[inline(always)]
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
        self.uses(n);
        let Ok(idx) = u16::try_from(idx) else {
            return Err(unsupported("projection index too large"));
        };
        self.add_expr(i, mk::proj(n, idx, e))
    }

    pub(super) fn do_nat(&mut self, i: u32, digits: &str) -> Result<()> {
        if digits.is_empty() || !digits.bytes().all(|c| c.is_ascii_digit()) {
            return Err(invalid("invalid natural literal"));
        }
        if digits.len() > MAX_NAT_DIGITS {
            return Err(unsupported("natural literal too long"));
        }
        let Some(n) = BigUint::parse_bytes(digits.as_bytes(), 10) else {
            return Err(invalid("invalid natural literal"));
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
            return self.scanned(l, b);
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

    #[inline(always)]
    fn scanned(&mut self, l: Line, b: &[u8]) -> Result<()> {
        if l.listed() {
            let us = std::mem::take(&mut self.scratch);
            let r = self.listed(l, &us);
            self.scratch = us;
            return r;
        }
        self.apply(l, b)
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
        self.log_end();
        let mut us = &b.us[..];
        for (k, &(s, e, l)) in b.lines.iter().enumerate() {
            if let Some(&(_, _, Some(l))) = b.lines.get(k + AHEAD_SLOTS) {
                self.fetch_slots(l);
            }
            if let Some(&(_, _, Some(l))) = b.lines.get(k + AHEAD_NODES) {
                self.fetch_nodes(l);
            }
            let raw = &b.buf[s as usize..e as usize];
            let plain =
                *n != 0 && l.is_some_and(|l| !l.listed() && !matches!(l, Line::Proj { .. }));
            self.log_line(k, plain);
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
            if !plain {
                self.log_end();
            }
            *n += 1;
        }
        // The line that straddles into the next batch is parsed there, unscanned.
        self.log_end();
        head.clear();
        head.extend_from_slice(&b.buf[last + 1..]);
        *carry = head;
        Ok(())
    }

    /// The expressions a line reads. Nearly half of them sit millions of ids back.
    #[inline(always)]
    fn children(l: Line) -> Option<(u32, u32)> {
        match l {
            Line::App(_, f, a) => Some((f, a)),
            Line::Binder { ty, body, .. } => Some((ty, body)),
            _ => None,
        }
    }

    /// Starts loading the table slots of a line still `AHEAD_SLOTS` away.
    #[inline(always)]
    fn fetch_slots(&self, l: Line) {
        if let Some((x, y)) = Self::children(l) {
            for i in [x, y] {
                prefetch(self.exprs.dense.as_ptr().wrapping_add(i as usize));
            }
        }
    }

    /// Starts loading the open children of a line `AHEAD_NODES` away, whose support is read.
    #[inline(always)]
    fn fetch_nodes(&self, l: Line) {
        if let Some((x, y)) = Self::children(l) {
            for i in [x, y] {
                if let Some(&Some(p)) = self.exprs.dense.get(i as usize)
                    && !p.closed()
                {
                    prefetch(std::ptr::from_ref(p.as_ref()));
                }
            }
        }
    }

    fn listed(&mut self, l: Line, us: &[u32]) -> Result<()> {
        match l {
            Line::Const(i, n) => self.do_const(i, n, us),
            Line::Thm(n, ty, val) => self.do_thm(n, us, ty, val).and_then(|()| self.seen()),
            Line::Def(n, ty, val, h) => {
                self.do_def(n, us, ty, val, h, "safe")?;
                self.seen()
            }
            _ => unreachable!("only listed lines carry a universe list"),
        }
    }

    #[inline(always)]
    fn apply(&mut self, l: Line, b: &[u8]) -> Result<()> {
        match l {
            Line::Str {
                id,
                pre,
                start,
                end,
            } => match std::str::from_utf8(&b[start as usize..end as usize]) {
                Ok(s) => self.do_str(id, pre, s),
                Err(_) => Err(invalid("invalid string")),
            },
            Line::Num(i, pre, n) => self.do_num(i, pre, n),
            Line::Succ(i, l) => self.do_succ(i, l),
            Line::Max { id, a, b: c, imax } => self.do_max(id, a, c, imax),
            Line::Param(i, n) => self.do_param(i, n),
            Line::App(i, f, a) => self.do_app(i, f, a),
            Line::Bvar(i, v) => self.do_bvar(i, v),
            Line::Sort(i, l) => self.do_sort(i, l),
            Line::Const(..) | Line::Thm(..) | Line::Def(..) => {
                unreachable!("listed lines carry their universe list separately")
            }
            Line::Binder {
                id,
                name,
                ty,
                body,
                lam,
            } => self.do_binder(id, name, ty, body, lam),
            Line::Let {
                id,
                name,
                ty,
                val,
                body,
                nondep,
            } => self.do_let(id, name, ty, val, body, nondep),
            Line::Proj { id, name, idx, e } => self.do_proj(id, name, idx, e),
        }
    }

    /// Called after each declaration record, the first `imported` of which are a view's imports.
    pub(super) fn seen(&mut self) -> Result<()> {
        if self.imported > 0 {
            self.imported -= 1;
            self.own = self.declars.len() as u32;
        }
        Ok(())
    }

    pub(super) fn finish(mut self) -> Result<Store<'a>> {
        if self.imported > 0 {
            return Err(invalid(
                "view imports more declarations than the export holds",
            ));
        }
        self.stats.expressions = self.exprs.filled();
        self.names = Table::new(Vec::new());
        self.levels = Table::new(Vec::new());
        let names = Names::build(&self.dag, self.anon);
        for n in [names.quot, names.quot_mk, names.quot_lift, names.quot_ind]
            .into_iter()
            .flatten()
        {
            if let Some(i) = n.decl_idx()
                && !matches!(self.declars[i as usize], Declar::Quot(_))
            {
                return Err(invalid(format!("reserved quotient name {n}")));
            }
        }
        let deps = (self.track
            && self.deps.sum.len() == self.exprs.dense.len()
            && self.deps.out.ends.len() == self.declars.len()
            && self.exprs.sparse.is_empty())
        .then_some(self.deps.out);
        let store = Store {
            dag: self.dag,
            anon: self.anon,
            zero: self.zero,
            declars: self.declars,
            own: self.own,
            blocks: self.blocks,
            names,
            stats: self.stats,
            deps,
        };
        super::primitives::check(&store)?;
        Ok(store)
    }
}

#[cfg(test)]
mod tests {
    use super::{MAX_GAP, Table};
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

    #[test]
    fn stepped_gaps_cannot_grow_the_dense_table() {
        let mut t = Table::new(Vec::new());
        for n in 1..4000u32 {
            t.put(n * (MAX_GAP as u32 - 1), n).unwrap();
        }
        assert!(t.dense.len() <= 2 * MAX_GAP);
        assert_eq!(t.get(3999 * (MAX_GAP as u32 - 1)).unwrap(), 3999);
    }
}
