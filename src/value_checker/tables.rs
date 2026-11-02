use super::intern::Ptrs;
use super::value::{Env, Lazy, Sub, V, Val};
use crate::term::FxHashMap;
use crate::term::ptr::{ExprPtr, LevelsPtr, NamePtr};
use hashbrown::HashTable;
use hashbrown::hash_table::Entry;
use num_bigint::BigUint;
use rustc_hash::FxBuildHasher;
use std::borrow::Borrow;
use std::cell::RefCell;
use std::hash::{BuildHasher, Hash};
use std::mem::{replace, swap, take, transmute};
use std::ops::{Deref, Index, IndexMut};
use std::ptr;
use std::rc::Rc;

#[derive(Clone, Copy)]
pub(super) enum Hot {
    Count(u32),
    Rule(u32),
    Never,
}

#[derive(Clone, Copy)]
pub(super) enum Node<'t> {
    Leaf(Option<V<'t>>),
    Split { slot: u16, start: u32, len: u16 },
}

#[derive(Clone, Copy)]
pub(super) struct Branch<'t> {
    pub(super) ctor: NamePtr<'t>,
    pub(super) ls: LevelsPtr<'t>,
    pub(super) nargs: u16,
    pub(super) id0: u32,
    pub(super) node: u32,
}

#[derive(Clone, Copy)]
pub(super) struct Rule {
    pub(super) arity: u16,
    pub(super) id0: u32,
    pub(super) root: u32,
}

#[derive(Default)]
pub(super) struct Derived<'t> {
    pub(super) rules: Vec<Rule>,
    pub(super) nodes: Vec<Node<'t>>,
    pub(super) branches: Vec<Branch<'t>>,
}

impl Derived<'_> {
    fn clear(&mut self) {
        self.rules.clear();
        self.nodes.clear();
        self.branches.clear();
    }
}

/// Whether an inference also checks the term or only computes its type.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum Mode {
    Check,
    Only,
}

/// One table per inference mode, since an unchecked type never answers a checked query.
#[derive(Default)]
pub(super) struct ByMode<T>([T; 2]);

impl<T> Index<Mode> for ByMode<T> {
    type Output = T;
    #[inline(always)]
    fn index(&self, m: Mode) -> &T {
        &self.0[m as usize]
    }
}

impl<T> IndexMut<Mode> for ByMode<T> {
    #[inline(always)]
    fn index_mut(&mut self, m: Mode) -> &mut T {
        &mut self.0[m as usize]
    }
}

/// A type with the universe parameters it relied on, empty when it relied on none.
#[derive(Clone, Copy)]
pub(super) struct Scoped<'t> {
    pub(super) ty: V<'t>,
    pub(super) uparams: LevelsPtr<'t>,
}

/// An open application's type with the environment it was inferred in.
#[derive(Clone, Copy)]
pub(super) struct Inferred<'t> {
    pub(super) env: Env<'t>,
    pub(super) ty: Scoped<'t>,
    pub(super) mode: Mode,
}

#[derive(Default)]
pub(super) struct Tables<'t> {
    pub(super) conv_locals: Logged<(usize, usize), V<'t>>,
    pub(super) eval_memo: Lossy<(ExprPtr<'t>, Sub<'t>, usize), V<'t>, 16>,
    pub(super) eval_closed: Memo<(ExprPtr<'t>, Sub<'t>), V<'t>>,
    pub(super) delta: FxHashMap<(NamePtr<'t>, LevelsPtr<'t>), (V<'t>, Hot)>,
    pub(super) derived: Derived<'t>,
    pub(super) const_ty: FxHashMap<(NamePtr<'t>, LevelsPtr<'t>), V<'t>>,
    pub(super) rules: FxHashMap<(NamePtr<'t>, usize, LevelsPtr<'t>), V<'t>>,
    pub(super) support: FxHashMap<ExprPtr<'t>, Option<&'t [u16]>>,
    pub(super) arg_support: FxHashMap<(NamePtr<'t>, usize), Rc<[bool]>>,
    /// Valid under any parameter list that includes the one recorded.
    pub(super) infer_closed: ByMode<FxHashMap<(ExprPtr<'t>, Sub<'t>), Scoped<'t>>>,
    /// Keyed by environment identity, so a hit needs no comparison of slots.
    pub(super) infer_open: ByMode<Logged<(ExprPtr<'t>, Sub<'t>, usize), Scoped<'t>>>,
    /// Open applications by the environment they were evaluated in, matched on their support.
    pub(super) eval_proj: Lossy<(ExprPtr<'t>, Sub<'t>), (Env<'t>, V<'t>), 14>,
    /// Open applications by the environment they were inferred in, matched on their support.
    pub(super) infer_proj: Lossy<(ExprPtr<'t>, Sub<'t>), Inferred<'t>, 14>,
    pub(super) eq_cache: LoggedSet<(usize, usize)>,
    pub(super) fail_cache: LoggedSet<(usize, usize)>,
    /// Pairs decided unequal, smaller key first.
    pub(super) neq_cache: LoggedSet<(usize, usize)>,
    /// Interned values, closed at index 0 and open at 1. Both persist with the durable caches
    /// that compare them by pointer.
    pub(super) hc: [Set<'t, Val<'t>>; 2],
    /// Neutrals with their hashes, so a rehash never walks a spine.
    pub(super) neus: [HashTable<(u64, V<'t>)>; 2],
    pub(super) neu_log: Vec<(u64, V<'t>)>,
    pub(super) envs: [Lossy<(usize, usize), Env<'t>, 16>; 2],
    /// Trimmed environments by source and support mask.
    pub(super) prunes: Lossy<(usize, u32), Env<'t>, 12>,
    pub(super) frames: [Logged<&'t Ptrs<'t>, Env<'t>>; 2],
    pub(super) lazies: [Set<'t, Lazy<'t>>; 2],
    pub(super) nats: FxHashMap<BigUint, V<'t>>,
}

impl<'t> Tables<'t> {
    /// Everything outlives the declaration except budget-bound failures, the clearing log and
    /// lazies, which were measured not to pay for retention. Sound because the core reads only
    /// the store below its limit, a session moves only to a later declaration, and any failure
    /// or fallback discards it. Checked types carry the parameters they relied on. Negatives
    /// persist only as established inequality, never as an exhausted budget.
    pub(super) fn durable(&mut self) -> Tables<'t> {
        let mut d = take(self);
        self.swap_scoped(&mut d);
        d
    }

    pub(super) fn absorb(&mut self, mut d: Tables<'t>) {
        self.swap_scoped(&mut d);
        *self = d;
    }

    /// Exhaustive, so a new table has to pick a lifetime here.
    fn swap_scoped(&mut self, d: &mut Tables<'t>) {
        let Tables {
            fail_cache,
            neu_log,
            lazies,
            conv_locals: _,
            eval_memo: _,
            eval_closed: _,
            delta: _,
            derived: _,
            const_ty: _,
            rules: _,
            support: _,
            arg_support: _,
            infer_closed: _,
            infer_open: _,
            eval_proj: _,
            infer_proj: _,
            eq_cache: _,
            neq_cache: _,
            hc: _,
            neus: _,
            envs: _,
            prunes: _,
            frames: _,
            nats: _,
        } = self;
        swap(fail_cache, &mut d.fail_cache);
        swap(neu_log, &mut d.neu_log);
        swap(lazies, &mut d.lazies);
    }
}

impl Tables<'_> {
    pub(super) fn recycle(self) -> Spare {
        self.recycle_below(RECYCLE_KEEP)
    }

    pub(super) fn recycle_below(mut self, keep: usize) -> Spare {
        macro_rules! reuse {
            ($($m:expr),*) => {$(
                if $m.len() > keep {
                    $m.clear();
                    $m.shrink_to(keep);
                } else if !$m.is_empty() {
                    $m.clear();
                }
            )*};
        }
        let Tables {
            conv_locals,
            eval_memo,
            eval_closed,
            delta,
            derived,
            const_ty,
            rules,
            support,
            arg_support,
            infer_closed,
            infer_open,
            infer_proj,
            eval_proj,
            eq_cache,
            fail_cache,
            neq_cache,
            hc,
            neus,
            neu_log,
            envs,
            prunes,
            frames,
            lazies,
            nats,
        } = &mut self;
        derived.clear();
        reuse!(
            eval_closed,
            delta,
            const_ty,
            rules,
            support,
            arg_support,
            nats,
            infer_closed.0[0],
            infer_closed.0[1]
        );
        for l in [eq_cache, fail_cache, neq_cache] {
            l.empty(keep);
        }
        conv_locals.empty(keep);
        eval_memo.empty(keep);
        infer_open.0.iter_mut().for_each(|l| l.empty(keep));
        hc.iter_mut().for_each(|l| l.empty(keep));
        envs.iter_mut().for_each(|l| l.empty(keep));
        prunes.empty(keep);
        infer_proj.empty(keep);
        eval_proj.empty(keep);
        frames.iter_mut().for_each(|l| l.empty(keep));
        lazies.iter_mut().for_each(|l| l.empty(keep));
        if neus[1].len() <= neu_log.len() {
            for (h, v) in neu_log.drain(..) {
                if let Ok(e) = neus[1].find_entry(h, |&(_, x)| ptr::eq(x, v)) {
                    e.remove();
                }
            }
        }
        neu_log.clear();
        for n in neus {
            if n.len() > keep {
                *n = Default::default();
            } else if !n.is_empty() {
                n.clear();
            }
        }
        // SAFETY: the exhaustive destructure above empties every table, so no `'t` reference survives.
        Spare(unsafe { transmute::<Tables<'_>, Tables<'static>>(self) })
    }
}

/// Emptied tables, which hold no arena reference and so fit any lifetime.
pub(super) struct Spare(Tables<'static>);

impl Spare {
    pub(super) fn revive<'t>(self) -> Tables<'t> {
        // SAFETY: only `recycle_below` builds a `Spare`, and it empties every table.
        unsafe { transmute::<Tables<'static>, Tables<'t>>(self.0) }
    }
}

/// Removing this many keys costs about as much as clearing `RECYCLE_KEEP` capacity.
pub(super) const LOG: usize = 16;

const RECYCLE_KEEP: usize = 1 << 13;

#[inline]
pub(super) fn fx<K: Hash + ?Sized>(k: &K) -> u64 {
    FxBuildHasher.hash_one(k)
}

/// `probe` returns the hash that `insert_new` reuses for an absent key.
pub(super) struct Memo<K, V>(HashTable<(K, V)>);

impl<K, V> Default for Memo<K, V> {
    fn default() -> Self {
        Self(Default::default())
    }
}

impl<K: Eq + Hash, V> Memo<K, V> {
    #[inline]
    pub(super) fn get<Q>(&self, q: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Eq + Hash + ?Sized,
    {
        self.0.find(fx(q), |(x, _)| x.borrow() == q).map(|(_, v)| v)
    }

    #[inline]
    pub(super) fn contains_key(&self, k: &K) -> bool {
        self.get(k).is_some()
    }

    #[inline]
    pub(super) fn probe(&self, k: &K) -> Result<&V, u64> {
        let h = fx(k);
        self.0.find(h, |(x, _)| x == k).map(|(_, v)| v).ok_or(h)
    }

    #[inline]
    pub(super) fn insert_new(&mut self, h: u64, k: K, v: V) {
        debug_assert!(self.get(&k).is_none());
        self.0.insert_unique(h, (k, v), |(k, _)| fx(k));
    }

    pub(super) fn insert(&mut self, k: K, v: V) -> Option<V> {
        match self.0.entry(fx(&k), |(x, _)| *x == k, |(k, _)| fx(k)) {
            Entry::Occupied(mut e) => Some(replace(&mut e.get_mut().1, v)),
            Entry::Vacant(e) => {
                e.insert((k, v));
                None
            }
        }
    }

    fn remove(&mut self, k: &K) {
        if let Ok(e) = self.0.find_entry(fx(k), |(x, _)| x == k) {
            e.remove();
        }
    }

    fn len(&self) -> usize {
        self.0.len()
    }

    fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    fn clear(&mut self) {
        self.0.clear();
    }

    fn shrink_to(&mut self, n: usize) {
        self.0.shrink_to(n, |(k, _)| fx(k));
    }
}

/// Logs its first keys so a lightly used table empties by removal instead of clearing.
pub(super) struct Logged<K, V> {
    map: Memo<K, V>,
    log: Vec<K>,
}

impl<K, V> Default for Logged<K, V> {
    fn default() -> Self {
        Self {
            map: Default::default(),
            log: Vec::new(),
        }
    }
}

impl<K, V> Deref for Logged<K, V> {
    type Target = Memo<K, V>;
    fn deref(&self) -> &Self::Target {
        &self.map
    }
}

impl<K: Copy + Eq + Hash, V> Logged<K, V> {
    #[inline]
    pub(super) fn insert(&mut self, k: K, v: V) -> Option<V> {
        let old = self.map.insert(k, v);
        if old.is_none() && self.log.len() < LOG {
            self.log.push(k);
        }
        old
    }

    fn empty(&mut self, keep: usize) {
        if self.map.len() <= self.log.len() {
            for k in &self.log {
                self.map.remove(k);
            }
        } else if self.map.len() > keep {
            self.map.clear();
            self.map.shrink_to(keep);
        } else {
            self.map.clear();
        }
        self.log.clear();
    }
}

/// Direct mapped and bounded: a colliding insert evicts, so a long evaluation keeps recent
/// results instead of growing a table of entries that are mostly never read again. Slots
/// stamped with an older epoch are empty, so emptying a large table writes nothing. `BITS` caps
/// the slot count, kept small since the tables persist across declarations and a large one
/// misses the cache on every probe.
pub(super) struct Lossy<K, V, const BITS: u32> {
    slots: Vec<(u32, Option<(K, V)>)>,
    live: usize,
    grow_at: usize,
    epoch: u32,
}

impl<K, V, const BITS: u32> Default for Lossy<K, V, BITS> {
    fn default() -> Self {
        Self {
            slots: Vec::new(),
            live: 0,
            grow_at: 0,
            epoch: 0,
        }
    }
}

const LOSSY_MIN: usize = 1 << 10;
const LOSSY_KEEP: usize = 1 << 16;

impl<K: Copy + Eq + Hash, V: Copy, const BITS: u32> Lossy<K, V, BITS> {
    #[inline]
    fn slot(&self, h: u64) -> usize {
        h as usize & (self.slots.len() - 1)
    }

    #[inline]
    fn find<Q>(&self, h: u64, q: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Eq + ?Sized,
    {
        if self.slots.is_empty() {
            return None;
        }
        match &self.slots[self.slot(h)] {
            (e, Some((x, v))) if *e == self.epoch && x.borrow() == q => Some(v),
            _ => None,
        }
    }

    #[inline]
    pub(super) fn probe(&self, k: &K) -> Result<&V, u64> {
        let h = fx(k);
        self.find(h, k).ok_or(h)
    }

    #[inline]
    pub(super) fn insert_new(&mut self, h: u64, k: K, v: V) {
        if self.live >= self.grow_at {
            self.grow();
        }
        let i = self.slot(h);
        let s = &mut self.slots[i];
        self.live += usize::from(s.0 != self.epoch);
        *s = (self.epoch, Some((k, v)));
    }

    pub(super) fn insert(&mut self, k: K, v: V) {
        self.insert_new(fx(&k), k, v);
    }

    #[cold]
    fn grow(&mut self) {
        let n = (self.slots.len() * 2).max(LOSSY_MIN);
        let old = replace(&mut self.slots, vec![(self.epoch.wrapping_sub(1), None); n]);
        self.live = 0;
        self.grow_at = if n < 1 << BITS { n / 4 * 3 } else { usize::MAX };
        for (e, kv) in old {
            if let (true, Some((k, v))) = (e == self.epoch, kv) {
                let i = self.slot(fx(&k));
                self.live += usize::from(self.slots[i].0 != self.epoch);
                self.slots[i] = (self.epoch, Some((k, v)));
            }
        }
    }

    fn empty(&mut self, keep: usize) {
        if self.slots.len() > keep.max(LOSSY_KEEP) {
            self.slots = Vec::new();
            self.grow_at = 0;
        } else if self.live != 0 {
            self.epoch = self.epoch.wrapping_add(1);
            if self.epoch == 0 {
                self.slots.fill((u32::MAX, None));
            }
        }
        self.live = 0;
    }
}

/// Interned objects with their hashes, matched by a caller's predicate so an entry costs
/// no copy of its key.
pub(super) struct Set<'t, T> {
    table: HashTable<(u64, &'t T)>,
    log: Vec<(u64, &'t T)>,
}

impl<T> Default for Set<'_, T> {
    fn default() -> Self {
        Self {
            table: HashTable::new(),
            log: Vec::new(),
        }
    }
}

impl<'t, T> Set<'t, T> {
    #[inline]
    pub(super) fn find(&self, h: u64, mut eq: impl FnMut(&'t T) -> bool) -> Option<&'t T> {
        self.table
            .find(h, |&(g, t)| g == h && eq(t))
            .map(|&(_, t)| t)
    }

    #[inline]
    pub(super) fn insert(&mut self, h: u64, t: &'t T) {
        self.table.insert_unique(h, (h, t), |&(g, _)| g);
        if self.log.len() < LOG {
            self.log.push((h, t));
        }
    }

    fn empty(&mut self, keep: usize) {
        if self.table.len() <= self.log.len() {
            for &(h, t) in &self.log {
                if let Ok(e) = self.table.find_entry(h, |&(_, x)| ptr::eq(x, t)) {
                    e.remove();
                }
            }
        } else if self.table.len() > keep {
            self.table = HashTable::new();
        } else {
            self.table.clear();
        }
        self.log.clear();
    }
}

pub(super) struct LoggedSet<K>(Logged<K, ()>);

impl<K> Default for LoggedSet<K> {
    fn default() -> Self {
        Self(Logged::default())
    }
}

impl<K> Deref for LoggedSet<K> {
    type Target = Memo<K, ()>;
    fn deref(&self) -> &Self::Target {
        &self.0.map
    }
}

impl<K: Copy + Eq + Hash> LoggedSet<K> {
    #[inline]
    pub(super) fn insert(&mut self, k: K) -> bool {
        self.0.insert(k, ()).is_none()
    }

    #[inline]
    pub(super) fn contains(&self, k: &K) -> bool {
        self.0.map.contains_key(k)
    }

    fn empty(&mut self, keep: usize) {
        self.0.empty(keep);
    }
}

impl LoggedSet<(usize, usize)> {
    #[inline]
    pub(super) fn insert_both(&mut self, a: usize, b: usize) {
        self.insert((a, b));
        self.insert((b, a));
    }
}

thread_local! {
    pub(super) static POOL: RefCell<Option<Spare>> = const { RefCell::new(None) };
}

#[cfg(feature = "vstats")]
trait Footprint {
    fn footprint(&self) -> (usize, usize);
}

#[cfg(feature = "vstats")]
impl<K, V> Footprint for Memo<K, V> {
    fn footprint(&self) -> (usize, usize) {
        (self.0.len(), self.0.capacity() * (size_of::<(K, V)>() + 1))
    }
}

#[cfg(feature = "vstats")]
impl<T> Footprint for Set<'_, T> {
    fn footprint(&self) -> (usize, usize) {
        let (n, b) = self.table.footprint();
        (n, b + self.log.capacity() * size_of::<(u64, &T)>())
    }
}

#[cfg(feature = "vstats")]
impl<K, V, const BITS: u32> Footprint for Lossy<K, V, BITS> {
    fn footprint(&self) -> (usize, usize) {
        (
            self.live,
            self.slots.capacity() * size_of::<(u32, Option<(K, V)>)>(),
        )
    }
}

#[cfg(feature = "vstats")]
impl<K, V> Footprint for Logged<K, V> {
    fn footprint(&self) -> (usize, usize) {
        let (n, b) = self.map.footprint();
        (n, b + self.log.capacity() * size_of::<K>())
    }
}

#[cfg(feature = "vstats")]
impl<K> Footprint for LoggedSet<K> {
    fn footprint(&self) -> (usize, usize) {
        self.0.footprint()
    }
}

#[cfg(feature = "vstats")]
impl<K, V, S> Footprint for std::collections::HashMap<K, V, S> {
    fn footprint(&self) -> (usize, usize) {
        (self.len(), self.capacity() * (size_of::<(K, V)>() + 1))
    }
}

#[cfg(feature = "vstats")]
impl<T> Footprint for HashTable<T> {
    fn footprint(&self) -> (usize, usize) {
        (self.len(), self.capacity() * (size_of::<T>() + 1))
    }
}

#[cfg(feature = "vstats")]
impl Tables<'_> {
    pub(super) fn footprint(&self) -> Vec<(&'static str, usize, usize)> {
        macro_rules! rows {
            ($($n:literal $f:expr),* $(,)?) => {
                vec![$({ let (l, b) = $f.footprint(); ($n, l, b) }),*]
            };
        }
        let mut v = rows!(
            "conv_locals" self.conv_locals,
            "eval_memo" self.eval_memo,
            "eval_closed" self.eval_closed,
            "delta" self.delta,
            "const_ty" self.const_ty,
            "rules" self.rules,
            "support" self.support,
            "arg_support" self.arg_support,
            "infer_closed0" self.infer_closed[Mode::Check],
            "infer_closed1" self.infer_closed[Mode::Only],
            "infer_open0" self.infer_open[Mode::Check],
            "infer_open1" self.infer_open[Mode::Only],
            "eq_cache" self.eq_cache,
            "fail_cache" self.fail_cache,
            "neq_cache" self.neq_cache,
            "hc_closed" self.hc[0],
            "hc_open" self.hc[1],
            "neus_closed" self.neus[0],
            "neus_open" self.neus[1],
            "envs_closed" self.envs[0],
            "envs_open" self.envs[1],
            "prunes" self.prunes,
            "frames_closed" self.frames[0],
            "frames_open" self.frames[1],
            "lazies_closed" self.lazies[0],
            "lazies_open" self.lazies[1],
            "nats" self.nats,
        );
        v.push((
            "neu_log",
            self.neu_log.len(),
            self.neu_log.capacity() * size_of::<(u64, V<'_>)>(),
        ));
        v
    }
}
