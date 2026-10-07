//! Value-based checker for ordinary declarations. Inductive and quotient
//! declarations are bridged to the existing checker and counted.

mod conv;
mod eval;
mod infer;
#[cfg(test)]
mod tests;
pub mod value;
mod whnf;

use crate::checker::{self, Adapter, Limits};
use crate::term::FxHashMap;
use crate::term::arena::Arena;
use crate::term::ctx::Ctx;
use crate::term::decl::Declar;
use crate::term::expr::Expr;
use crate::term::intern::{Names, Store};
use crate::term::level::Level;
use crate::term::outcome::{self, Failure};
use crate::term::ptr::{ExprPtr, LevelPtr, LevelsPtr, NamePtr};
use crate::{ensure, reject};
use smallvec::SmallVec;
use value::*;

#[derive(Clone, Copy, Hash, PartialEq, Eq)]
enum HKey<'t> {
    Sort(LevelPtr<'t>),
    Pi(usize, (usize, Sub<'t>, ExprPtr<'t>, bool)),
    Lam(usize, (usize, Sub<'t>, ExprPtr<'t>, bool)),
    Const(NamePtr<'t>, LevelsPtr<'t>),
    Proj(NamePtr<'t>, u16, usize),
    Str(usize, usize),
}

/// Probe budget ran out. Never a semantic answer.
#[derive(Debug)]
pub struct Stop;
pub type R<T> = Result<T, Stop>;

#[derive(Default)]
struct Tables<'t> {
    conv_locals: Logged<(usize, usize), V<'t>>,
    eval_memo: Logged<(ExprPtr<'t>, Sub<'t>, usize), V<'t>>,
    eval_closed: Memo<(ExprPtr<'t>, Sub<'t>), V<'t>>,
    delta: FxHashMap<(NamePtr<'t>, LevelsPtr<'t>), V<'t>>,
    const_ty: FxHashMap<(NamePtr<'t>, LevelsPtr<'t>), V<'t>>,
    rules: FxHashMap<(NamePtr<'t>, usize, LevelsPtr<'t>), V<'t>>,
    support: FxHashMap<ExprPtr<'t>, &'t [u16]>,
    arg_support: FxHashMap<(NamePtr<'t>, usize), std::rc::Rc<[bool]>>,
    /// Closed results with the universe parameters a checked result relies
    /// on: empty, or the list it was checked under. They hold under any list
    /// that includes it.
    infer_closed: [FxHashMap<(ExprPtr<'t>, Sub<'t>), (V<'t>, LevelsPtr<'t>)>; 2],
    infer_open: [Logged<(ExprPtr<'t>, Sub<'t>, usize), V<'t>>; 2],
    type_of: Logged<usize, V<'t>>,
    whnf_core_cache: Logged<usize, V<'t>>,
    whnf_cache: Logged<usize, V<'t>>,
    unfold_cache: Logged<usize, Option<V<'t>>>,
    eq_cache: LoggedSet<(usize, usize)>,
    fail_cache: LoggedSet<(usize, usize)>,
    /// Pairs decided unequal, smaller key first.
    neq_cache: LoggedSet<(usize, usize)>,
    /// Interning split by openness; closed values (index 0) persist across a
    /// session so durable caches stay pointer-comparable with fresh values.
    hc: [Logged<HKey<'t>, V<'t>>; 2],
    /// Neutrals with their hashes, so a rehash never walks a spine.
    neus: [hashbrown::HashTable<(u64, V<'t>)>; 2],
    /// Hashes of the first open neutrals of a declaration.
    neu_log: Vec<(u64, V<'t>)>,
    envs: [Logged<(usize, usize), Env<'t>>; 2],
    frames: [Logged<&'t Ptrs<'t>, Env<'t>>; 2],
    lazies: [Logged<(usize, Sub<'t>, ExprPtr<'t>), &'t Lazy<'t>>; 2],
    nats: FxHashMap<num_bigint::BigUint, V<'t>>,
}

impl<'t> Tables<'t> {
    /// Move the tables keyed by constants and syntax, which stay small and pay
    /// off across declarations, into a fresh `Tables`.
    fn durable(&mut self) -> Tables<'t> {
        use std::mem::take;
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

    fn absorb(&mut self, d: Tables<'t>) {
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
    fn recycle(self) -> Tables<'static> {
        self.recycle_below(1 << 13)
    }

    /// Empty every table, keeping the capacity of those that held at most
    /// `keep` entries.
    fn recycle_below(mut self, keep: usize) -> Tables<'static> {
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
        for l in [
            &mut self.type_of,
            &mut self.whnf_core_cache,
            &mut self.whnf_cache,
        ] {
            l.empty(keep);
        }
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
        self.frames.iter_mut().for_each(|l| l.empty(keep));
        self.lazies.iter_mut().for_each(|l| l.empty(keep));
        if self.neus[1].len() <= self.neu_log.len() {
            for (h, v) in self.neu_log.drain(..) {
                if let Ok(e) = self.neus[1].find_entry(h, |&(_, x)| std::ptr::eq(x, v)) {
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
        unsafe { std::mem::transmute::<Tables<'_>, Tables<'static>>(self) }
    }
}

/// Keys logged per table. Removing this many costs about as much as clearing
/// a retained capacity of `1 << 13`.
const LOG: usize = 16;

#[inline]
fn fx<K: std::hash::Hash + ?Sized>(k: &K) -> u64 {
    use std::hash::BuildHasher;
    rustc_hash::FxBuildHasher.hash_one(k)
}

/// A hash map that is probed once per miss: `probe` hands back the hash,
/// which `insert_new` reuses for a key known to be absent.
struct Memo<K, V>(hashbrown::HashTable<(K, V)>);

impl<K, V> Default for Memo<K, V> {
    fn default() -> Self {
        Self(Default::default())
    }
}

impl<K: Eq + std::hash::Hash, V> Memo<K, V> {
    #[inline]
    fn get<Q>(&self, q: &Q) -> Option<&V>
    where
        K: std::borrow::Borrow<Q>,
        Q: Eq + std::hash::Hash + ?Sized,
    {
        self.0.find(fx(q), |(x, _)| x.borrow() == q).map(|(_, v)| v)
    }

    #[inline]
    fn contains_key(&self, k: &K) -> bool {
        self.get(k).is_some()
    }

    /// The value at `k`, or the hash to insert it under.
    #[inline]
    fn probe(&self, k: &K) -> Result<&V, u64> {
        let h = fx(k);
        self.0.find(h, |(x, _)| x == k).map(|(_, v)| v).ok_or(h)
    }

    #[inline]
    fn insert_new(&mut self, h: u64, k: K, v: V) {
        debug_assert!(self.get(&k).is_none());
        self.0.insert_unique(h, (k, v), |(k, _)| fx(k));
    }

    fn insert(&mut self, k: K, v: V) -> Option<V> {
        match self.0.entry(fx(&k), |(x, _)| *x == k, |(k, _)| fx(k)) {
            hashbrown::hash_table::Entry::Occupied(mut e) => {
                Some(std::mem::replace(&mut e.get_mut().1, v))
            }
            hashbrown::hash_table::Entry::Vacant(e) => {
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

/// A per-declaration map that logs its first keys, so a lightly used table is
/// emptied by removing them instead of clearing its whole capacity.
struct Logged<K, V> {
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

impl<K, V> std::ops::Deref for Logged<K, V> {
    type Target = Memo<K, V>;
    fn deref(&self) -> &Self::Target {
        &self.map
    }
}

impl<K: Copy + Eq + std::hash::Hash, V> Logged<K, V> {
    #[inline]
    fn insert(&mut self, k: K, v: V) -> Option<V> {
        let old = self.map.insert(k, v);
        if old.is_none() && self.log.len() < LOG {
            self.log.push(k);
        }
        old
    }

    #[inline]
    fn insert_new(&mut self, h: u64, k: K, v: V) {
        self.map.insert_new(h, k, v);
        if self.log.len() < LOG {
            self.log.push(k);
        }
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

struct LoggedSet<K>(Logged<K, ()>);

impl<K> Default for LoggedSet<K> {
    fn default() -> Self {
        Self(Logged::default())
    }
}

impl<K> std::ops::Deref for LoggedSet<K> {
    type Target = Memo<K, ()>;
    fn deref(&self) -> &Self::Target {
        &self.0.map
    }
}

impl<K: Copy + Eq + std::hash::Hash> LoggedSet<K> {
    #[inline]
    fn insert(&mut self, k: K) -> bool {
        self.0.insert(k, ()).is_none()
    }

    #[inline]
    fn contains(&self, k: &K) -> bool {
        self.0.map.contains_key(k)
    }

    fn empty(&mut self, keep: usize) {
        self.0.empty(keep)
    }
}

thread_local! {
    static POOL: std::cell::RefCell<Option<Tables<'static>>> = const { std::cell::RefCell::new(None) };
}

impl Drop for Vc<'_, '_> {
    fn drop(&mut self) {
        let t = std::mem::take(&mut self.t).recycle();
        POOL.with(|p| *p.borrow_mut() = Some(t));
    }
}

fn head_eq<'t>(a: Head<'t>, b: Head<'t>) -> bool {
    match (a, b) {
        (Head::Local(i, _), Head::Local(j, _)) => i == j,
        (Head::Const(n, l), Head::Const(m, k)) => n == m && l == k,
        (Head::Proj(n, i, x), Head::Proj(m, j, y)) => n == m && i == j && std::ptr::eq(x, y),
        _ => false,
    }
}

fn neu_hash<'t, 'v>(h: Head<'t>, n: usize, args: impl Iterator<Item = &'v V<'t>>) -> u64
where
    't: 'v,
{
    use std::hash::{BuildHasher, Hash, Hasher};
    let mut s = rustc_hash::FxBuildHasher.build_hasher();
    match h {
        Head::Local(i, _) => (0u8, i).hash(&mut s),
        Head::Const(c, l) => (1u8, c, l).hash(&mut s),
        Head::Proj(c, i, x) => (2u8, c, i, key(x)).hash(&mut s),
    }
    s.write_usize(n);
    for &a in args {
        s.write_usize(key(a));
    }
    s.finish()
}

/// A spine hashed and compared by element identity.
#[repr(transparent)]
struct Ptrs<'t>([V<'t>]);

impl<'t> Ptrs<'t> {
    fn new<'s>(a: &'s [V<'t>]) -> &'s Self {
        // SAFETY: `Ptrs` is a transparent wrapper over the slice.
        unsafe { &*(a as *const [V<'t>] as *const Self) }
    }
}

impl std::hash::Hash for Ptrs<'_> {
    fn hash<H: std::hash::Hasher>(&self, h: &mut H) {
        h.write_usize(self.0.len());
        for &v in &self.0 {
            h.write_usize(key(v));
        }
    }
}

impl PartialEq for Ptrs<'_> {
    fn eq(&self, o: &Self) -> bool {
        self.0.len() == o.0.len() && self.0.iter().zip(&o.0).all(|(&a, &b)| std::ptr::eq(a, b))
    }
}

impl Eq for Ptrs<'_> {}

struct Vc<'t, 'a: 't> {
    pub ctx: Ctx<'t, 'a>,
    names: Names<'t>,
    uparams: LevelsPtr<'t>,
    limit: u32,
    limits: Limits,
    steps_left: u64,
    probe_remaining: Option<u32>,
    next_local: u32,
    depth: usize,
    /// Bumped whenever a check depends on the universe parameters in scope.
    scoped: u64,
    /// Parameter lists already compared against `uparams`, and whether they
    /// are included in it.
    included: SmallVec<[(LevelsPtr<'t>, bool); 4]>,
    id: Sub<'t>,
    dummy: V<'t>,
    t: Tables<'t>,
    base: usize,
    #[cfg(feature = "vstats")]
    pub stats: Stats,
    #[cfg(feature = "vstats")]
    pub unfolded: FxHashMap<crate::term::ptr::NamePtr<'t>, u64>,
}

macro_rules! stats {
    ($($f:ident),*) => {
        #[cfg(feature = "vstats")]
        #[derive(Default, Clone, Copy, Debug)]
        pub struct Stats {
            $(pub $f: u64,)*
        }

        #[cfg(feature = "vstats")]
        impl Stats {
            fn mk_kind(&mut self, kind: usize, hit: bool) {
                let f = match (kind, hit) {
                    (0, true) => &mut self.mk_sort_hit,
                    (0, false) => &mut self.mk_sort_miss,
                    (1, true) => &mut self.mk_pi_open_hit,
                    (1, false) => &mut self.mk_pi_open_miss,
                    (2, true) => &mut self.mk_pi_closed_hit,
                    (2, false) => &mut self.mk_pi_closed_miss,
                    (3, true) => &mut self.mk_lam_open_hit,
                    (3, false) => &mut self.mk_lam_open_miss,
                    (4, true) => &mut self.mk_lam_closed_hit,
                    (4, false) => &mut self.mk_lam_closed_miss,
                    (5, true) => &mut self.mk_neu0_open_hit,
                    (5, false) => &mut self.mk_neu0_open_miss,
                    (6, true) => &mut self.mk_str_hit,
                    (6, false) => &mut self.mk_str_miss,
                    (_, true) => &mut self.mk_neu0_closed_hit,
                    (_, false) => &mut self.mk_neu0_closed_miss,
                };
                *f += 1;
            }

            fn add(&mut self, o: &Self) {
                $(self.$f += o.$f;)*
            }
        }
    };
}

stats!(
    vals,
    evals,
    applies,
    whnfs,
    unfolds,
    memo_hits,
    probes,
    exhausted,
    neq_hit,
    probe_ticks,
    ev_app,
    ev_lam,
    ev_pi,
    ev_let,
    ev_other,
    mk_req,
    push_req,
    push_new,
    spine_req,
    spine_new,
    spine_copied,
    beta_chain,
    beta_neu,
    trims,
    beta_runs,
    spine_old,
    spine_new_args,
    nat_req,
    spine_empty_prefix,
    frame_req,
    frame_new,
    sup_mask,
    sup_wide,
    sup_wide_new,
    mk_sort_hit,
    mk_sort_miss,
    mk_pi_open_hit,
    mk_pi_open_miss,
    mk_pi_closed_hit,
    mk_pi_closed_miss,
    mk_lam_open_hit,
    mk_lam_open_miss,
    mk_lam_closed_hit,
    mk_lam_closed_miss,
    mk_neu0_open_hit,
    mk_neu0_open_miss,
    mk_neu0_closed_hit,
    mk_neu0_closed_miss,
    mk_str_hit,
    mk_str_miss,
    neu_open_hit,
    neu_open_miss,
    neu_closed_hit,
    neu_closed_miss,
    push_open_req,
    push_open_new,
    deq_calls,
    deq_ptr_eq,
    deq_binding,
    deq_args,
    deq_same,
    closed_hit,
    closed_miss,
    resets
);

/// Totals over every declaration checked by a session, for `NL_VSTATS`.
#[cfg(feature = "vstats")]
pub static TOTAL: std::sync::Mutex<Option<Stats>> = std::sync::Mutex::new(None);

#[cfg(feature = "vstats")]
pub static RESETS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

#[cfg(feature = "vstats")]
pub fn report() {
    if std::env::var_os("NL_VSTATS").is_none() {
        return;
    }
    for (path, [n, t]) in ["native", "legacy"].iter().zip(&checker::BLOCKS) {
        use std::sync::atomic::Ordering::Relaxed;
        let (n, t) = (n.load(Relaxed), t.load(Relaxed));
        eprintln!("vstats ind {path} blocks {n} {:.3} s", t as f64 * 1e-9);
    }
    if let Some(s) = *TOTAL.lock().unwrap() {
        let mut s = s;
        s.resets = RESETS.load(std::sync::atomic::Ordering::Relaxed);
        eprintln!("vstats total {s:?}");
    }
}

macro_rules! stat {
    ($s:expr, $f:ident) => {
        #[cfg(feature = "vstats")]
        {
            $s.stats.$f += 1;
        }
    };
}
pub(crate) use stat;

impl<'t, 'a: 't> Vc<'t, 'a> {
    pub fn new(store: &'a Store<'a>, arena: &'t Arena, limits: Limits) -> Self {
        let mut ctx = Ctx::new(store, arena);
        let e = ctx.levels(&[]);
        let z = ctx.zero();
        let dummy = arena.alloc(Val {
            k: K::Sort(z),
            open: false,
        });
        Self {
            names: store.names,
            ctx,
            uparams: e,
            limit: 0,
            limits,
            steps_left: limits.steps,
            probe_remaining: None,
            next_local: 0,
            depth: 0,
            scoped: 0,
            included: SmallVec::new(),
            id: Sub { ks: e, vs: e },
            dummy,
            // SAFETY: pooled tables are empty.
            t: POOL
                .with(|p| p.borrow_mut().take())
                .map_or_else(Default::default, |t| unsafe {
                    std::mem::transmute::<Tables<'static>, Tables<'t>>(t)
                }),
            base: arena.allocated_bytes(),
            #[cfg(feature = "vstats")]
            stats: Stats::default(),
            #[cfg(feature = "vstats")]
            unfolded: Default::default(),
        }
    }

    fn used(&self) -> usize {
        self.ctx.arena.allocated_bytes() - self.base
    }

    /// Work accounting without spending the probe budget.
    #[inline]
    pub(crate) fn work(&mut self) {
        if self.steps_left & 1023 >= 2 {
            self.steps_left -= 1;
        } else {
            self.work_slow();
        }
    }

    #[cold]
    #[inline(never)]
    fn work_slow(&mut self) {
        if self.steps_left == 0 {
            crate::unsupported!("declaration work budget exhausted");
        }
        self.steps_left -= 1;
        if self.steps_left & 1023 == 0 && self.used() > self.limits.arena_bytes {
            crate::unsupported!("declaration arena budget exhausted");
        }
    }

    #[inline]
    pub(crate) fn tick(&mut self) -> R<()> {
        if self.steps_left & 1023 >= 2 {
            self.steps_left -= 1;
            return Ok(());
        }
        self.tick_slow()
    }

    #[inline(never)]
    fn tick_slow(&mut self) -> R<()> {
        if self.steps_left == 0 {
            crate::unsupported!("declaration work budget exhausted");
        }
        self.steps_left -= 1;
        if self.steps_left & 1023 == 0 && self.used() > self.limits.arena_bytes {
            crate::unsupported!("declaration arena budget exhausted");
        }
        Ok(())
    }

    /// Hash-consed: structurally equal values share a pointer, as interned
    /// terms do in the term checker.
    pub(crate) fn mk(&mut self, k: K<'t>, open: bool) -> V<'t> {
        // Open Pi values almost never recur, so probing for them only costs.
        if open && matches!(k, K::Pi(..)) {
            stat!(self, vals);
            return self.ctx.arena.alloc(Val { k, open });
        }
        let ck = |c: Clo<'t>| (c.env.key(), c.sub, c.body, c.typed);
        let hk = match k {
            K::Sort(l) => HKey::Sort(l),
            K::Pi(d, c) => HKey::Pi(key(d), ck(c)),
            K::Lam(d, c) => HKey::Lam(d as *const Lazy as usize, ck(c)),
            K::Neu(h, a) => {
                // Applied neutrals are interned by `neu`, keeping one address each.
                debug_assert!(a.is_empty());
                match h {
                    Head::Local(..) => unreachable!("locals are not interned"),
                    Head::Const(n, ls) => HKey::Const(n, ls),
                    Head::Proj(n, i, x) => HKey::Proj(n, i, key(x)),
                }
            }
            K::Nat(n) => return self.nat(n.clone()),
            K::Str(x) => HKey::Str(x.as_ptr() as usize, x.len()),
        };
        stat!(self, mk_req);
        #[cfg(feature = "vstats")]
        let kind = match (&hk, open) {
            (HKey::Sort(_), _) => 0,
            (HKey::Pi(..), true) => 1,
            (HKey::Pi(..), false) => 2,
            (HKey::Lam(..), true) => 3,
            (HKey::Lam(..), false) => 4,
            (HKey::Str(..), _) => 6,
            (_, true) => 5,
            (_, false) => 7,
        };
        let hc = &mut self.t.hc[usize::from(open)];
        let h = match hc.probe(&hk) {
            Ok(&v) => {
                #[cfg(feature = "vstats")]
                self.stats.mk_kind(kind, true);
                return v;
            }
            Err(h) => h,
        };
        #[cfg(feature = "vstats")]
        self.stats.mk_kind(kind, false);
        let v = self.ctx.arena.alloc(Val { k, open });
        hc.insert_new(h, hk, v);
        stat!(self, vals);
        v
    }

    /// The neutral `h` applied to `sp` then `rest`, interned by head and
    /// argument identity so the spine and value are allocated only on a miss.
    pub(crate) fn neu(&mut self, h: Head<'t>, sp: &[V<'t>], rest: &[V<'t>], open: bool) -> V<'t> {
        stat!(self, spine_req);
        let n = sp.len() + rest.len();
        let hash = neu_hash(h, n, sp.iter().chain(rest));
        let same = |&(hv, v): &(u64, V<'t>)| {
            hv == hash
                && matches!(v.k, K::Neu(g, a) if a.len() == n && head_eq(g, h)
                && a.iter().zip(sp.iter().chain(rest)).all(|(&x, &y)| std::ptr::eq(x, y)))
        };
        let o = usize::from(open);
        if let Some(&(_, v)) = self.t.neus[o].find(hash, same) {
            #[cfg(feature = "vstats")]
            if open {
                self.stats.neu_open_hit += 1
            } else {
                self.stats.neu_closed_hit += 1
            }
            return v;
        }
        #[cfg(feature = "vstats")]
        if open {
            self.stats.neu_open_miss += 1
        } else {
            self.stats.neu_closed_miss += 1
        }
        let all: &'t [V<'t>] = if sp.is_empty() {
            self.ctx.arena.alloc_slice_copy(rest)
        } else {
            let m = sp.len();
            self.ctx
                .arena
                .alloc_slice_fill_with(n, |i| if i < m { sp[i] } else { rest[i - m] })
        };
        #[cfg(feature = "vstats")]
        {
            self.stats.spine_new += 1;
            self.stats.spine_copied += n as u64;
        }
        stat!(self, vals);
        let v = self.ctx.arena.alloc(Val {
            k: K::Neu(h, all),
            open,
        });
        if open && self.t.neu_log.len() < LOG {
            self.t.neu_log.push((hash, v));
        }
        self.t.neus[o].insert_unique(hash, (hash, v), |&(g, _)| g);
        v
    }

    pub(crate) fn declar(&self, n: NamePtr<'t>) -> Option<Declar<'t>> {
        let i = n.decl_idx()?;
        (i < self.limit).then(|| self.ctx.store.declars[i as usize])
    }

    pub(crate) fn sub(&self, ks: LevelsPtr<'t>, vs: LevelsPtr<'t>) -> Sub<'t> {
        if ks.is_empty() || ks == vs {
            self.id
        } else {
            Sub { ks, vs }
        }
    }

    pub(crate) fn fresh_local(&mut self, ty: V<'t>) -> V<'t> {
        self.next_local += 1;
        let id = self.next_local;
        // Ids are never reused, so interning could only miss.
        stat!(self, vals);
        self.ctx.arena.alloc(Val {
            k: K::Neu(Head::Local(id, ty), &[]),
            open: true,
        })
    }

    pub(crate) fn konst0(&mut self, n: Option<NamePtr<'t>>) -> V<'t> {
        let Some(n) = n else {
            reject!("missing builtin constant")
        };
        let e = self.ctx.levels(&[]);
        self.mk(K::Neu(Head::Const(n, e), &[]), false)
    }

    /// Whether every parameter in `ls` is in scope.
    fn within(&mut self, ls: LevelsPtr<'t>) -> bool {
        if ls.is_empty() || ls == self.uparams {
            return true;
        }
        if let Some(&(_, ok)) = self.included.iter().find(|w| w.0 == ls) {
            return ok;
        }
        let ok = ls.iter().all(|l| self.uparams.contains(l));
        if self.included.len() < 8 {
            self.included.push((ls, ok));
        }
        ok
    }

    fn check_level(&mut self, l: LevelPtr<'t>) {
        fn has_param(l: LevelPtr<'_>) -> bool {
            match *l {
                Level::Zero => false,
                Level::Succ(l, _) => has_param(l),
                Level::Max(l, r, _) | Level::IMax(l, r, _) => has_param(l) || has_param(r),
                Level::Param(..) => true,
            }
        }
        if has_param(l) {
            self.scoped += 1;
            ensure!(l.params_in(self.uparams), "undeclared universe parameter");
        }
    }

    fn check(&mut self, idx: u32) {
        if self.used() > self.limits.arena_bytes {
            crate::unsupported!("declaration arena budget exhausted");
        }
        let d = self.ctx.store.declars[idx as usize];
        self.uparams = d.uparams();
        self.included.clear();
        self.limit = idx;
        let r: R<()> = (|| {
            match d {
                Declar::Axiom(i) => {
                    self.check_type(i.ty)?;
                }
                Declar::Def(i, v, _) | Declar::Opaque(i, v) => {
                    self.check_telescope(i.ty)?;
                    self.check_value(v, i.ty)?;
                }
                Declar::Thm(i, v) => {
                    let l = self.check_telescope(i.ty)?;
                    let z = self.ctx.zero();
                    ensure!(self.ctx.level_eq(l, z), "theorem type is not a proposition");
                    self.check_value(v, i.ty)?;
                }
                _ => unreachable!("bridged declaration"),
            }
            Ok(())
        })();
        r.expect("probe exhaustion escaped its probe");
    }

    fn check_type(&mut self, ty: ExprPtr<'t>) -> R<LevelPtr<'t>> {
        let id = self.id;
        let s = self.infer(Env::EMPTY, id, ty, false)?;
        self.ensure_sort(s)
    }

    /// Checks a declared type as `check_type` does, walking its leading Pi
    /// binders by hand under the canonical binder locals, so the value check
    /// meets the same environments and reuses what the type check cached.
    fn check_telescope(&mut self, ty: ExprPtr<'t>) -> R<LevelPtr<'t>> {
        if !ty.closed()
            || !matches!(*ty, Expr::Pi { .. })
            || self.t.infer_closed[0].contains_key(&(ty, self.id))
        {
            return self.check_type(ty);
        }
        let saved = self.depth;
        let r = self.check_telescope_in(ty);
        self.depth = saved;
        r
    }

    fn check_telescope_in(&mut self, ty: ExprPtr<'t>) -> R<LevelPtr<'t>> {
        let id = self.id;
        let mark = self.scoped;
        let (mut env, mut e) = (Env::EMPTY, ty);
        let mut sorts = SmallVec::<[LevelPtr<'t>; 8]>::new();
        while let Expr::Pi { ty: b, body, .. } = *e {
            self.tick()?;
            let s = self.infer(env, id, b, false)?;
            sorts.push(self.ensure_sort(s)?);
            let dom = self.eval(env, id, b)?;
            let x = self.binder_local(dom);
            env = self.push(env, x);
            e = body;
        }
        let s = self.infer(env, id, e, false)?;
        let mut l = self.ensure_sort(s)?;
        for &s1 in sorts.iter().rev() {
            l = self.ctx.imax(s1, l);
        }
        let t = self.mk(K::Sort(l), false);
        let s = if self.scoped == mark {
            LevelsPtr::new(&[])
        } else {
            self.uparams
        };
        self.t.infer_closed[0].insert((ty, id), (t, s));
        Ok(l)
    }

    /// Checks leading lambdas against leading Pi binders of the declared type
    /// under one shared local each, instead of building the lambda's Pi type
    /// and inferring its body again during conversion. A binder domain that
    /// is the type's own domain needs no check: the type is well formed.
    fn check_value(&mut self, v: ExprPtr<'t>, ty: ExprPtr<'t>) -> R<()> {
        let saved = self.depth;
        let r = self.check_value_in(v, ty);
        self.depth = saved;
        r
    }

    fn check_value_in(&mut self, mut v: ExprPtr<'t>, mut ty: ExprPtr<'t>) -> R<()> {
        let id = self.id;
        let mut env = Env::EMPTY;
        let mut doms = SmallVec::<[(V<'t>, Env<'t>, ExprPtr<'t>); 8]>::new();
        while let (
            Expr::Lam { ty: a, body, .. },
            Expr::Pi {
                ty: b, body: tb, ..
            },
        ) = (*v, *ty)
        {
            let dom = self.eval(env, id, a)?;
            if a != b {
                let s = self.infer(env, id, a, false)?;
                self.ensure_sort(s)?;
                doms.push((dom, env, b));
            }
            let x = self.binder_local(dom);
            env = self.push(env, x);
            (v, ty) = (body, tb);
        }
        let vt = self.infer(env, id, v, false)?;
        for (dom, env, b) in doms {
            let d = self.eval(env, id, b)?;
            ensure!(self.def_eq(dom, d)?, "declaration type mismatch");
        }
        let tv = self.eval(env, id, ty)?;
        ensure!(self.def_eq(vt, tv)?, "declaration type mismatch");
        Ok(())
    }
}

/// An obligation from the native inductive path: a declared type that must
/// be well formed, or the exported term and the generated one it must match,
/// as a recursor type or as a rule.
#[derive(Clone, Copy)]
pub(crate) enum RecCheck<'t> {
    Sort(ExprPtr<'t>),
    Type(ExprPtr<'t>, ExprPtr<'t>),
    Rule(ExprPtr<'t>, ExprPtr<'t>),
}

impl<'t, 'a: 't> Vc<'t, 'a> {
    fn rec_check(&mut self, c: RecCheck<'t>) -> R<()> {
        let id = self.id;
        match c {
            RecCheck::Sort(ty) => {
                self.check_type(ty)?;
            }
            RecCheck::Type(ty, want) => {
                self.check_type(ty)?;
                if ty != want {
                    let a = self.eval(Env::EMPTY, id, ty)?;
                    let b = self.eval(Env::EMPTY, id, want)?;
                    ensure!(self.def_eq(a, b)?, "incorrect recursor type");
                }
            }
            RecCheck::Rule(rhs, want) => {
                let wt = self.infer(Env::EMPTY, id, want, false)?;
                if rhs != want {
                    let at = self.infer(Env::EMPTY, id, rhs, false)?;
                    ensure!(self.def_eq(at, wt)?, "incorrect recursor computation rule");
                    let a = self.eval(Env::EMPTY, id, rhs)?;
                    let b = self.eval(Env::EMPTY, id, want)?;
                    ensure!(self.def_eq(a, b)?, "incorrect recursor computation rule");
                }
            }
        }
        Ok(())
    }
}

/// Run recursor obligations in the term checker's context and work budget.
/// Returns the index of the first rejected one; declines propagate.
pub(crate) fn check_recursor<'t, 'a: 't>(
    ctx: &mut Ctx<'t, 'a>,
    limits: Limits,
    steps: &mut u64,
    uparams: LevelsPtr<'t>,
    limit: u32,
    checks: &[RecCheck<'t>],
) -> Result<(), usize> {
    let mut vc = Vc::new(ctx.store, ctx.arena, limits);
    std::mem::swap(&mut vc.ctx, ctx);
    let e = vc.ctx.levels(&[]);
    vc.id = Sub { ks: e, vs: e };
    vc.steps_left = *steps;
    vc.uparams = uparams;
    vc.limit = limit;
    let mut at = 0;
    let result = outcome::run(|| {
        for (i, &c) in checks.iter().enumerate() {
            at = i;
            vc.rec_check(c).expect("probe exhaustion escaped its probe");
        }
    });
    std::mem::swap(&mut vc.ctx, ctx);
    *steps = vc.steps_left;
    match result {
        Ok(()) => Ok(()),
        Err(Failure::Rejected(_)) => Err(at),
        Err(Failure::Declined(m)) => crate::unsupported!("{m}"),
        Err(Failure::Internal(m)) => panic!("{m}"),
    }
}

/// Bridge counts by kind: quot, inductive, constructor, recursor.
pub static BRIDGED: [std::sync::atomic::AtomicU64; 4] =
    [const { std::sync::atomic::AtomicU64::new(0) }; 4];

pub fn check<'a>(
    store: &'a Store<'a>,
    arena: &mut Arena,
    idx: u32,
    limits: Limits,
    adapter: Option<&mut Adapter<'a>>,
    native_only: bool,
) -> Result<bool, Failure> {
    let k = match store.declars[idx as usize] {
        Declar::Quot(_) => Some(0),
        Declar::Ind(_) => Some(1),
        Declar::Ctor(_) => Some(2),
        Declar::Rec(_) => Some(3),
        _ => None,
    };
    if let Some(k) = k {
        BRIDGED[k].fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        return checker::check_with_adapter(store, arena, idx, limits, adapter, native_only);
    }
    let mut vc = Vc::new(store, arena, limits);
    let result = outcome::run(|| vc.check(idx));
    #[cfg(feature = "vstats")]
    if std::env::var_os("NL_VSTATS").is_some() {
        eprintln!(
            "vstats {} {:?} arena {}",
            store.declars[idx as usize].name(),
            vc.stats,
            vc.ctx.arena.allocated_bytes()
        );
        let mut top: Vec<_> = vc
            .unfolded
            .iter()
            .map(|(n, c)| (*c, n.to_string()))
            .collect();
        top.sort_unstable_by(|a, b| b.cmp(a));
        for (c, n) in top.iter().take(15) {
            eprintln!("  unfold {c} {n}");
        }
    }
    let mut rest = limits;
    rest.steps = vc.steps_left;
    drop(vc);
    match result {
        Err(Failure::Declined(reason))
            if !native_only && reason == "declaration arena budget exhausted" =>
        {
            arena.reset();
            checker::check_existing_only(store, arena, idx, rest, adapter).map(|()| true)
        }
        r => r.map(|()| false),
    }
}

/// Caches carried between declarations checked in increasing order.
struct State {
    last: u32,
    next_local: u32,
    ctx: Ctx<'static, 'static>,
    t: Tables<'static>,
}

/// A checker that owns its arena, so values and caches can outlive one
/// declaration. `state` borrows from `arena` and is declared first so it drops
/// first; it is discarded before any mutable access to the arena.
pub struct Session<'a> {
    state: Option<State>,
    /// The durable tables of the last state, emptied but with their capacity,
    /// so a reset does not regrow them from nothing.
    spare: Option<Tables<'static>>,
    store: &'a Store<'a>,
    arena: Box<Arena>,
}

impl<'a> Session<'a> {
    pub fn new(store: &'a Store<'a>) -> Self {
        Self {
            state: None,
            spare: None,
            store,
            arena: Box::default(),
        }
    }

    pub fn arena(&self) -> &Arena {
        &self.arena
    }

    pub fn arena_mut(&mut self) -> &mut Arena {
        if let Some(s) = self.state.take() {
            self.spare = Some(s.t.recycle_below(usize::MAX));
        }
        &mut self.arena
    }

    pub fn reset(&mut self) {
        self.arena_mut().reset();
    }

    pub fn check(
        &mut self,
        idx: u32,
        limits: Limits,
        mut adapter: Option<&mut Adapter<'a>>,
        native_only: bool,
    ) -> Result<bool, Failure> {
        let store = self.store;
        let k = match store.declars[idx as usize] {
            Declar::Quot(_) => Some(0),
            Declar::Ind(_) => Some(1),
            Declar::Ctor(_) => Some(2),
            Declar::Rec(_) => Some(3),
            _ => None,
        };
        if let Some(k) = k {
            BRIDGED[k].fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            let (r, steps) =
                checker::check_shared(store, &self.arena, idx, limits, adapter.as_deref_mut());
            return match r {
                Err(Failure::Declined(reason))
                    if !native_only && reason == "declaration arena budget exhausted" =>
                {
                    self.reset();
                    let mut rest = limits;
                    rest.steps = steps;
                    checker::check_existing_only(store, &mut self.arena, idx, rest, adapter)
                        .map(|()| true)
                }
                r => {
                    if r.is_err() {
                        self.state = None;
                    }
                    r.map(|()| false)
                }
            };
        }
        let state = self.state.take().filter(|s| s.last < idx);
        let arena: &Arena = &self.arena;
        let mut vc = Vc::new(store, arena, limits);
        if let Some(s) = state {
            // SAFETY: `s` was built from this session's arena, which has not been
            // reset or mutably borrowed since.
            unsafe {
                vc.t.absorb(std::mem::transmute::<Tables<'static>, Tables<'_>>(s.t));
                vc.ctx = std::mem::transmute::<Ctx<'static, 'static>, Ctx<'_, '_>>(s.ctx);
            }
            vc.next_local = s.next_local;
        } else if let Some(t) = self.spare.take() {
            // SAFETY: spare tables are empty.
            vc.t.absorb(unsafe { std::mem::transmute::<Tables<'static>, Tables<'_>>(t) });
        }
        let result = outcome::run(|| vc.check(idx));
        #[cfg(feature = "vstats")]
        TOTAL.lock().unwrap().get_or_insert_default().add(&vc.stats);
        if result.is_ok() {
            let ctx = std::mem::replace(&mut vc.ctx, Ctx::new(store, arena));
            let t = vc.t.durable();
            // SAFETY: the state only lives inside this session, next to its arena.
            self.state = Some(unsafe {
                State {
                    last: idx,
                    next_local: vc.next_local,
                    ctx: std::mem::transmute::<Ctx<'_, '_>, Ctx<'static, 'static>>(ctx),
                    t: std::mem::transmute::<Tables<'_>, Tables<'static>>(t),
                }
            });
            return Ok(false);
        }
        let mut rest = limits;
        rest.steps = vc.steps_left;
        drop(vc);
        match result {
            Err(Failure::Declined(reason))
                if !native_only && reason == "declaration arena budget exhausted" =>
            {
                self.reset();
                checker::check_existing_only(store, &mut self.arena, idx, rest, adapter)
                    .map(|()| true)
            }
            r => r.map(|()| false),
        }
    }
}
