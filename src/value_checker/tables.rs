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
use std::mem::{replace, take, transmute};
use std::ops::Deref;
use std::ptr;
use std::rc::Rc;

#[derive(Default)]
pub(super) struct Tables<'t> {
    pub(super) conv_locals: Logged<(usize, usize), V<'t>>,
    pub(super) eval_memo: Lossy<(ExprPtr<'t>, Sub<'t>, usize), V<'t>>,
    pub(super) eval_closed: Memo<(ExprPtr<'t>, Sub<'t>), V<'t>>,
    pub(super) delta: FxHashMap<(NamePtr<'t>, LevelsPtr<'t>), V<'t>>,
    pub(super) const_ty: FxHashMap<(NamePtr<'t>, LevelsPtr<'t>), V<'t>>,
    pub(super) rules: FxHashMap<(NamePtr<'t>, usize, LevelsPtr<'t>), V<'t>>,
    pub(super) support: FxHashMap<ExprPtr<'t>, Option<&'t [u16]>>,
    pub(super) arg_support: FxHashMap<(NamePtr<'t>, usize), Rc<[bool]>>,
    /// Closed results with the parameter list they relied on, valid under any list including it.
    pub(super) infer_closed: [FxHashMap<(ExprPtr<'t>, Sub<'t>), (V<'t>, LevelsPtr<'t>)>; 2],
    pub(super) infer_open: [Logged<(ExprPtr<'t>, Sub<'t>, usize), V<'t>>; 2],
    pub(super) type_of: Logged<usize, V<'t>>,
    pub(super) whnf_core_cache: Lossy<usize, V<'t>>,
    pub(super) whnf_cache: Lossy<usize, V<'t>>,
    pub(super) unfold_cache: Lossy<usize, Option<V<'t>>>,
    pub(super) eq_cache: LoggedSet<(usize, usize)>,
    pub(super) fail_cache: LoggedSet<(usize, usize)>,
    /// Pairs decided unequal, smaller key first.
    pub(super) neq_cache: LoggedSet<(usize, usize)>,
    /// Closed values (index 0) persist so durable caches stay pointer-comparable.
    pub(super) hc: [Set<'t, Val<'t>>; 2],
    /// Neutrals with their hashes, so a rehash never walks a spine.
    pub(super) neus: [HashTable<(u64, V<'t>)>; 2],
    pub(super) neu_log: Vec<(u64, V<'t>)>,
    pub(super) envs: [Lossy<(usize, usize), Env<'t>>; 2],
    /// Trimmed environments by source and support mask.
    pub(super) prunes: Lossy<(usize, u32), Env<'t>>,
    pub(super) frames: [Logged<&'t Ptrs<'t>, Env<'t>>; 2],
    pub(super) lazies: [Set<'t, Lazy<'t>>; 2],
    pub(super) nats: FxHashMap<BigUint, V<'t>>,
}

impl<'t> Tables<'t> {
    pub(super) fn durable(&mut self) -> Tables<'t> {
        Tables {
            delta: take(&mut self.delta),
            const_ty: take(&mut self.const_ty),
            rules: take(&mut self.rules),
            eval_closed: take(&mut self.eval_closed),
            support: take(&mut self.support),
            arg_support: take(&mut self.arg_support),
            infer_closed: take(&mut self.infer_closed),
            nats: take(&mut self.nats),
            hc: [take(&mut self.hc[0]), Default::default()],
            neus: [take(&mut self.neus[0]), Default::default()],
            ..Default::default()
        }
    }

    pub(super) fn absorb(&mut self, d: Tables<'t>) {
        self.delta = d.delta;
        self.const_ty = d.const_ty;
        self.rules = d.rules;
        self.eval_closed = d.eval_closed;
        self.support = d.support;
        self.arg_support = d.arg_support;
        self.infer_closed = d.infer_closed;
        self.nats = d.nats;
        let [h, _] = d.hc;
        let [n, _] = d.neus;
        (self.hc[0], self.neus[0]) = (h, n);
    }
}

impl Tables<'_> {
    pub(super) fn recycle(self) -> Tables<'static> {
        self.recycle_below(RECYCLE_KEEP)
    }

    pub(super) fn recycle_below(mut self, keep: usize) -> Tables<'static> {
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
        reuse!(
            self.eval_closed,
            self.delta,
            self.const_ty,
            self.rules,
            self.support,
            self.arg_support,
            self.nats,
            self.infer_closed[0],
            self.infer_closed[1]
        );
        self.type_of.empty(keep);
        self.whnf_core_cache.empty(keep);
        self.whnf_cache.empty(keep);
        for l in [
            &mut self.eq_cache,
            &mut self.fail_cache,
            &mut self.neq_cache,
        ] {
            l.empty(keep);
        }
        self.conv_locals.empty(keep);
        self.eval_memo.empty(keep);
        self.unfold_cache.empty(keep);
        self.infer_open.iter_mut().for_each(|l| l.empty(keep));
        self.hc.iter_mut().for_each(|l| l.empty(keep));
        self.envs.iter_mut().for_each(|l| l.empty(keep));
        self.prunes.empty(keep);
        self.frames.iter_mut().for_each(|l| l.empty(keep));
        self.lazies.iter_mut().for_each(|l| l.empty(keep));
        if self.neus[1].len() <= self.neu_log.len() {
            for (h, v) in self.neu_log.drain(..) {
                if let Ok(e) = self.neus[1].find_entry(h, |&(_, x)| ptr::eq(x, v)) {
                    e.remove();
                }
            }
        }
        self.neu_log.clear();
        for n in &mut self.neus {
            if n.len() > keep {
                *n = Default::default();
            } else if !n.is_empty() {
                n.clear();
            }
        }
        // SAFETY: every table is empty, so no `'t` reference survives.
        unsafe { transmute::<Tables<'_>, Tables<'static>>(self) }
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
/// stamped with an older epoch are empty, so emptying a large table writes nothing.
pub(super) struct Lossy<K, V> {
    slots: Vec<(u32, Option<(K, V)>)>,
    live: usize,
    epoch: u32,
}

impl<K, V> Default for Lossy<K, V> {
    fn default() -> Self {
        Self {
            slots: Vec::new(),
            live: 0,
            epoch: 0,
        }
    }
}

const LOSSY_MIN: usize = 1 << 10;
const LOSSY_MAX: usize = 1 << 20;

impl<K: Copy + Eq + Hash, V: Copy> Lossy<K, V> {
    #[inline]
    fn slot(&self, h: u64) -> usize {
        (h >> (64 - self.slots.len().trailing_zeros())) as usize
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
    pub(super) fn get<Q>(&self, q: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Eq + Hash + ?Sized,
    {
        self.find(fx(q), q)
    }

    #[inline]
    pub(super) fn insert_new(&mut self, h: u64, k: K, v: V) {
        if self.live * 4 >= self.slots.len() * 3 && self.slots.len() < LOSSY_MAX {
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
        for (e, kv) in old {
            if let (true, Some((k, v))) = (e == self.epoch, kv) {
                let i = self.slot(fx(&k));
                self.live += usize::from(self.slots[i].0 != self.epoch);
                self.slots[i] = (self.epoch, Some((k, v)));
            }
        }
    }

    fn empty(&mut self, keep: usize) {
        if self.slots.len() > keep {
            self.slots = Vec::new();
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
    pub(super) static POOL: RefCell<Option<Tables<'static>>> = const { RefCell::new(None) };
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
impl<K, V> Footprint for Lossy<K, V> {
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
            "infer_closed0" self.infer_closed[0],
            "infer_closed1" self.infer_closed[1],
            "infer_open0" self.infer_open[0],
            "infer_open1" self.infer_open[1],
            "type_of" self.type_of,
            "whnf_core_cache" self.whnf_core_cache,
            "whnf_cache" self.whnf_cache,
            "unfold_cache" self.unfold_cache,
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
