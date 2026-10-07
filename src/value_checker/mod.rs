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
use crate::term::arena::Arena;
use crate::term::ctx::Ctx;
use crate::term::decl::Declar;
use crate::term::intern::{Names, Store};
use crate::term::outcome::{self, Failure};
use crate::term::ptr::{ExprPtr, LevelPtr, LevelsPtr, NamePtr};
use crate::term::{FxHashMap, FxHashSet};
use crate::{ensure, reject};
use value::*;

#[derive(Hash, PartialEq, Eq)]
enum HKey<'t> {
    Sort(LevelPtr<'t>),
    Pi(usize, (usize, Sub<'t>, ExprPtr<'t>, bool)),
    Lam(usize, (usize, Sub<'t>, ExprPtr<'t>, bool)),
    Local(u32, usize),
    Const(NamePtr<'t>, LevelsPtr<'t>, usize),
    Proj(NamePtr<'t>, u16, usize, usize),
    Str(usize, usize),
}

/// Probe budget ran out. Never a semantic answer.
#[derive(Debug)]
pub struct Stop;
pub type R<T> = Result<T, Stop>;

#[derive(Default)]
struct Tables<'t> {
    conv_locals: FxHashMap<(usize, usize), V<'t>>,
    eval_memo: FxHashMap<(ExprPtr<'t>, Sub<'t>, usize), V<'t>>,
    eval_closed: FxHashMap<(ExprPtr<'t>, Sub<'t>), V<'t>>,
    delta: FxHashMap<(NamePtr<'t>, LevelsPtr<'t>), V<'t>>,
    const_ty: FxHashMap<(NamePtr<'t>, LevelsPtr<'t>), V<'t>>,
    rules: FxHashMap<(NamePtr<'t>, usize, LevelsPtr<'t>), V<'t>>,
    support: FxHashMap<ExprPtr<'t>, &'t [u16]>,
    arg_support: FxHashMap<(NamePtr<'t>, usize), std::rc::Rc<[bool]>>,
    infer_closed: [FxHashMap<(ExprPtr<'t>, Sub<'t>), V<'t>>; 2],
    infer_open: [FxHashMap<(ExprPtr<'t>, Sub<'t>, usize), V<'t>>; 2],
    type_of: FxHashMap<usize, V<'t>>,
    whnf_core_cache: FxHashMap<usize, V<'t>>,
    whnf_cache: FxHashMap<usize, V<'t>>,
    unfold_cache: FxHashMap<usize, Option<V<'t>>>,
    eq_cache: FxHashSet<(usize, usize)>,
    fail_cache: FxHashSet<(usize, usize)>,
    /// Interning split by openness; closed values (index 0) persist across a
    /// session so durable caches stay pointer-comparable with fresh values.
    hc: [FxHashMap<HKey<'t>, V<'t>>; 2],
    spines: [FxHashSet<&'t Ptrs<'t>>; 2],
    envs: [FxHashMap<(usize, usize), Env<'t>>; 2],
    frames: [FxHashMap<&'t Ptrs<'t>, Env<'t>>; 2],
    lazies: [FxHashMap<(usize, Sub<'t>, ExprPtr<'t>), &'t Lazy<'t>>; 2],
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
            spines: [take(&mut self.spines[0]), Default::default()],
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
        let [sp, _] = d.spines;
        (self.hc[0], self.spines[0]) = (h, sp);
    }
}

impl Tables<'_> {
    fn recycle(mut self) -> Tables<'static> {
        macro_rules! reuse {
            ($($m:expr),*) => {$(
                if $m.len() > 1 << 13 {
                    $m = Default::default();
                } else if !$m.is_empty() {
                    $m.clear();
                }
            )*};
        }
        reuse!(
            self.conv_locals,
            self.eval_memo,
            self.eval_closed,
            self.delta,
            self.const_ty,
            self.rules,
            self.support,
            self.arg_support,
            self.type_of,
            self.whnf_core_cache,
            self.whnf_cache,
            self.unfold_cache,
            self.eq_cache,
            self.fail_cache,
            self.nats
        );
        reuse!(
            self.infer_closed[0],
            self.infer_closed[1],
            self.infer_open[0],
            self.infer_open[1],
            self.hc[0],
            self.hc[1],
            self.spines[0],
            self.spines[1],
            self.envs[0],
            self.envs[1],
            self.frames[0],
            self.frames[1],
            self.lazies[0],
            self.lazies[1]
        );
        // SAFETY: every table is empty, so no `'t` reference survives.
        unsafe { std::mem::transmute::<Tables<'_>, Tables<'static>>(self) }
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
    spine_hashed,
    nat_req,
    spine_empty_prefix,
    frame_req,
    frame_new
);

/// Totals over every declaration checked by a session, for `NL_VSTATS`.
#[cfg(feature = "vstats")]
pub static TOTAL: std::sync::Mutex<Option<Stats>> = std::sync::Mutex::new(None);

#[cfg(feature = "vstats")]
pub fn report() {
    if std::env::var_os("NL_VSTATS").is_some()
        && let Some(s) = *TOTAL.lock().unwrap()
    {
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
    pub(crate) fn work(&mut self) {
        if self.steps_left == 0 {
            crate::unsupported!("declaration work budget exhausted");
        }
        self.steps_left -= 1;
        if self.steps_left & 1023 == 0 && self.used() > self.limits.arena_bytes {
            crate::unsupported!("declaration arena budget exhausted");
        }
    }

    pub(crate) fn tick(&mut self) -> R<()> {
        if self.steps_left == 0 {
            crate::unsupported!("declaration work budget exhausted");
        }
        self.steps_left -= 1;
        if self.steps_left & 1023 == 0 && self.used() > self.limits.arena_bytes {
            crate::unsupported!("declaration arena budget exhausted");
        }
        if let Some(r) = &mut self.probe_remaining {
            if *r == 0 {
                return Err(Stop);
            }
            *r -= 1;
        }
        Ok(())
    }

    /// Hash-consed: structurally equal values share a pointer, as interned
    /// terms do in the term checker.
    pub(crate) fn mk(&mut self, k: K<'t>, open: bool) -> V<'t> {
        let sp = |a: &[V<'t>]| if a.is_empty() { 0 } else { a.as_ptr() as usize };
        let ck = |c: Clo<'t>| (c.env.key(), c.sub, c.body, c.typed);
        let hk = match k {
            K::Sort(l) => HKey::Sort(l),
            K::Pi(d, c) => HKey::Pi(key(d), ck(c)),
            K::Lam(d, c) => HKey::Lam(d as *const Lazy as usize, ck(c)),
            K::Neu(Head::Local(i, _), a) => HKey::Local(i, sp(a)),
            K::Neu(Head::Const(n, ls), a) => HKey::Const(n, ls, sp(a)),
            K::Neu(Head::Proj(n, i, x), a) => HKey::Proj(n, i, key(x), sp(a)),
            K::Nat(n) => return self.nat(n.clone()),
            K::Str(x) => HKey::Str(x.as_ptr() as usize, x.len()),
        };
        stat!(self, mk_req);
        let hc = &mut self.t.hc[usize::from(open)];
        if let Some(&v) = hc.get(&hk) {
            return v;
        }
        let v = self.ctx.arena.alloc(Val { k, open });
        hc.insert(hk, v);
        stat!(self, vals);
        v
    }

    pub(crate) fn spine(&mut self, a: &[V<'t>]) -> &'t [V<'t>] {
        stat!(self, spine_req);
        #[cfg(feature = "vstats")]
        {
            self.stats.spine_hashed += a.len() as u64;
        }
        let o = usize::from(a.iter().any(|v| v.open));
        if let Some(s) = self.t.spines[o].get(Ptrs::new(a)) {
            return &s.0;
        }
        let s: &'t [V<'t>] = self.ctx.arena.alloc_slice_copy(a);
        #[cfg(feature = "vstats")]
        {
            self.stats.spine_new += 1;
            self.stats.spine_copied += a.len() as u64;
        }
        self.t.spines[o].insert(Ptrs::new(s));
        s
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
        self.mk(K::Neu(Head::Local(id, ty), &[]), true)
    }

    pub(crate) fn konst0(&mut self, n: Option<NamePtr<'t>>) -> V<'t> {
        let Some(n) = n else {
            reject!("missing builtin constant")
        };
        let e = self.ctx.levels(&[]);
        self.mk(K::Neu(Head::Const(n, e), &[]), false)
    }

    fn check_level(&self, l: LevelPtr<'t>) {
        ensure!(l.params_in(self.uparams), "undeclared universe parameter");
    }

    fn check(&mut self, idx: u32) {
        if self.used() > self.limits.arena_bytes {
            crate::unsupported!("declaration arena budget exhausted");
        }
        let d = self.ctx.store.declars[idx as usize];
        self.uparams = d.uparams();
        self.limit = idx;
        let r: R<()> = (|| {
            match d {
                Declar::Axiom(i) => {
                    self.check_type(i.ty)?;
                }
                Declar::Def(i, v, _) | Declar::Opaque(i, v) => {
                    self.check_type(i.ty)?;
                    self.check_value(v, i.ty)?;
                }
                Declar::Thm(i, v) => {
                    let l = self.check_type(i.ty)?;
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

    fn check_value(&mut self, v: ExprPtr<'t>, ty: ExprPtr<'t>) -> R<()> {
        let id = self.id;
        let vt = self.infer(Env::EMPTY, id, v, false)?;
        let tv = self.eval(Env::EMPTY, id, ty)?;
        ensure!(self.def_eq(vt, tv)?, "declaration type mismatch");
        Ok(())
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
    uparams: (usize, usize),
    next_local: u32,
    ctx: Ctx<'static, 'static>,
    t: Tables<'static>,
}

/// A checker that owns its arena, so values and caches can outlive one
/// declaration. `state` borrows from `arena` and is declared first so it drops
/// first; it is discarded before any mutable access to the arena.
/// Identity of a universe parameter list; the length matters because an
/// empty slice may share its address with a nonempty one.
fn scope(ls: LevelsPtr<'_>) -> (usize, usize) {
    (ls.as_ref().as_ptr() as usize, ls.len())
}

pub struct Session<'a> {
    state: Option<State>,
    store: &'a Store<'a>,
    arena: Box<Arena>,
}

impl<'a> Session<'a> {
    pub fn new(store: &'a Store<'a>) -> Self {
        Self {
            state: None,
            store,
            arena: Box::default(),
        }
    }

    pub fn arena(&self) -> &Arena {
        &self.arena
    }

    pub fn arena_mut(&mut self) -> &mut Arena {
        self.state = None;
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
            // Checked results also vouch for universe parameters in scope.
            if scope(store.declars[idx as usize].uparams()) != s.uparams {
                vc.t.infer_closed[0].clear();
            }
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
                    uparams: scope(vc.uparams),
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
