use super::Vc;
#[cfg(feature = "vstats")]
use super::stats::TOTAL;
use super::tables::{Spare, Tables};
use crate::checker::{self, Adapter, CheckPath, Limits};
use crate::resource::Budget;
use crate::term::arena::Arena;
use crate::term::ctx::Ctx;
use crate::term::decl::Declar;
use crate::term::intern::Store;
use crate::term::outcome::{Decline, Failure};
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
) -> Result<CheckPath, Failure> {
    if bridged(store.declars[idx as usize]) {
        return checker::check_with_adapter(store, arena, idx, limits, adapter, native_only);
    }
    let mut vc = Vc::new(store, arena, limits);
    let result = vc.check(idx);
    #[cfg(feature = "vstats")]
    vc.report_declaration(idx);
    let rest = Limits {
        steps: vc.steps_left,
        ..limits
    };
    drop(vc);
    if arena_exhausted(&result, native_only) {
        arena.reset();
        return checker::check_existing_only(store, arena, idx, rest, adapter)
            .map(|()| CheckPath::Fallback);
    }
    result.map(|()| CheckPath::Primary)
}

/// Fresh tables restart local ids long before they could wrap.
const LOCAL_RESTART: u32 = 1 << 31;

/// A finished checker's durable tables and context with the arena lifetime erased. Sound to
/// resume while the arena that `epoch` names is unreset, since every reference points into it
/// or into the store, which outlives the session.
struct State {
    epoch: u64,
    last: u32,
    memo: u32,
    next_local: u32,
    ctx: Ctx<'static, 'static>,
    t: Tables<'static>,
}

impl State {
    fn suspend(vc: &mut Vc<'_, '_>, epoch: u64, last: u32) -> Self {
        let fresh = Ctx::new(vc.ctx.store, vc.ctx.arena);
        let ctx = replace(&mut vc.ctx, fresh);
        let t = vc.t.durable();
        // SAFETY: erased until `resume` checks the epoch.
        unsafe {
            State {
                epoch,
                last,
                memo: vc.epoch,
                next_local: vc.next_local,
                ctx: transmute::<Ctx<'_, '_>, Ctx<'static, 'static>>(ctx),
                t: transmute::<Tables<'_>, Tables<'static>>(t),
            }
        }
    }

    fn resume<'t>(self, vc: &mut Vc<'t, '_>, arena: &'t Arena) {
        assert!(self.epoch == arena.epoch(), "state outlived its arena");
        // SAFETY: the epoch ties the state to this arena, unreset since.
        unsafe {
            vc.t.absorb(transmute::<Tables<'static>, Tables<'t>>(self.t));
            vc.ctx = transmute::<Ctx<'static, 'static>, Ctx<'t, '_>>(self.ctx);
        }
        vc.next_local = self.next_local;
        vc.epoch = self.memo;
    }
}

/// `state` borrows from `arena`, so it is declared first to drop first.
pub struct Session<'a> {
    state: Option<State>,
    spare: Option<Spare>,
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
    ) -> Result<CheckPath, Failure> {
        self.reset();
        checker::check_existing_only(self.store, &mut self.arena, idx, rest, adapter)
            .map(|()| CheckPath::Fallback)
    }

    pub fn check(
        &mut self,
        idx: u32,
        limits: Limits,
        mut adapter: Option<&mut Adapter<'a>>,
        native_only: bool,
    ) -> Result<CheckPath, Failure> {
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
            return r.map(|()| CheckPath::Primary);
        }
        let state = self
            .state
            .take()
            .filter(|s| s.last < idx && s.next_local < LOCAL_RESTART);
        let arena: &Arena = &self.arena;
        let mut vc = Vc::new(store, arena, limits);
        if let Some(s) = state {
            s.resume(&mut vc, arena);
        } else if let Some(t) = self.spare.take() {
            vc.t.absorb(t.revive());
        }
        let result = vc.check(idx);
        #[cfg(feature = "vstats")]
        vc.report_declaration(idx);
        #[cfg(feature = "vstats")]
        TOTAL
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .get_or_insert_default()
            .add(&vc.stats);
        if result.is_ok() {
            self.state = Some(State::suspend(&mut vc, arena.epoch(), idx));
            return Ok(CheckPath::Primary);
        }
        let rest = Limits {
            steps: vc.steps_left,
            ..limits
        };
        drop(vc);
        if arena_exhausted(&result, native_only) {
            return self.recheck(idx, rest, adapter);
        }
        result.map(|()| CheckPath::Primary)
    }
}
