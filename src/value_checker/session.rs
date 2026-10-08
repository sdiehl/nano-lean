use super::Vc;
#[cfg(feature = "vstats")]
use super::stats::TOTAL;
use super::tables::Tables;
use crate::checker::{self, Adapter, Limits};
use crate::resource::Budget;
use crate::term::arena::Arena;
use crate::term::ctx::Ctx;
use crate::term::decl::Declar;
use crate::term::intern::Store;
use crate::term::outcome::{self, Decline, Failure};
use std::mem::{replace, transmute};
use std::sync::atomic::AtomicU64;
use std::sync::atomic::Ordering::Relaxed;

pub static BRIDGED: [AtomicU64; 4] = [const { AtomicU64::new(0) }; 4];

fn bridged(d: Declar<'_>) -> bool {
    let k = match d {
        Declar::Quot(_) => 0,
        Declar::Ind(_) => 1,
        Declar::Ctor(_) => 2,
        Declar::Rec(_) => 3,
        _ => return false,
    };
    BRIDGED[k].fetch_add(1, Relaxed);
    true
}

fn arena_exhausted<T>(r: &Result<T, Failure>, native_only: bool) -> bool {
    !native_only && matches!(r, Err(Failure::Declined(Decline::Exhausted(Budget::Arena))))
}

pub fn check<'a>(
    store: &'a Store<'a>,
    arena: &mut Arena,
    idx: u32,
    limits: Limits,
    adapter: Option<&mut Adapter<'a>>,
    native_only: bool,
) -> Result<bool, Failure> {
    if bridged(store.declars[idx as usize]) {
        return checker::check_with_adapter(store, arena, idx, limits, adapter, native_only);
    }
    let mut vc = Vc::new(store, arena, limits);
    let result = outcome::run(|| vc.check(idx));
    #[cfg(feature = "vstats")]
    vc.report_declaration(idx);
    let rest = Limits {
        steps: vc.steps_left,
        ..limits
    };
    drop(vc);
    if arena_exhausted(&result, native_only) {
        arena.reset();
        return checker::check_existing_only(store, arena, idx, rest, adapter).map(|()| true);
    }
    result.map(|()| false)
}

struct State {
    last: u32,
    next_local: u32,
    ctx: Ctx<'static, 'static>,
    t: Tables<'static>,
}

/// `state` borrows from `arena`, so it is declared first to drop first.
pub struct Session<'a> {
    state: Option<State>,
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

    fn recheck(
        &mut self,
        idx: u32,
        rest: Limits,
        adapter: Option<&mut Adapter<'a>>,
    ) -> Result<bool, Failure> {
        self.reset();
        checker::check_existing_only(self.store, &mut self.arena, idx, rest, adapter).map(|()| true)
    }

    pub fn check(
        &mut self,
        idx: u32,
        limits: Limits,
        mut adapter: Option<&mut Adapter<'a>>,
        native_only: bool,
    ) -> Result<bool, Failure> {
        let store = self.store;
        if bridged(store.declars[idx as usize]) {
            let (r, steps) =
                checker::check_shared(store, &self.arena, idx, limits, adapter.as_deref_mut());
            if arena_exhausted(&r, native_only) {
                return self.recheck(idx, Limits { steps, ..limits }, adapter);
            }
            if r.is_err() {
                self.state = None;
            }
            return r.map(|()| false);
        }
        let state = self.state.take().filter(|s| s.last < idx);
        let arena: &Arena = &self.arena;
        let mut vc = Vc::new(store, arena, limits);
        if let Some(s) = state {
            // SAFETY: `s` came from this session's arena, untouched since.
            unsafe {
                vc.t.absorb(transmute::<Tables<'static>, Tables<'_>>(s.t));
                vc.ctx = transmute::<Ctx<'static, 'static>, Ctx<'_, '_>>(s.ctx);
            }
            vc.next_local = s.next_local;
        } else if let Some(t) = self.spare.take() {
            // SAFETY: spare tables are empty.
            vc.t.absorb(unsafe { transmute::<Tables<'static>, Tables<'_>>(t) });
        }
        let result = outcome::run(|| vc.check(idx));
        #[cfg(feature = "vstats")]
        TOTAL
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .get_or_insert_default()
            .add(&vc.stats);
        if result.is_ok() {
            let ctx = replace(&mut vc.ctx, Ctx::new(store, arena));
            let t = vc.t.durable();
            // SAFETY: the state only lives inside this session, next to its arena.
            self.state = Some(unsafe {
                State {
                    last: idx,
                    next_local: vc.next_local,
                    ctx: transmute::<Ctx<'_, '_>, Ctx<'static, 'static>>(ctx),
                    t: transmute::<Tables<'_>, Tables<'static>>(t),
                }
            });
            return Ok(false);
        }
        let rest = Limits {
            steps: vc.steps_left,
            ..limits
        };
        drop(vc);
        if arena_exhausted(&result, native_only) {
            return self.recheck(idx, rest, adapter);
        }
        result.map(|()| false)
    }
}
