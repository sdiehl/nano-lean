#[cfg(feature = "vstats")]
use super::Vc;
#[cfg(feature = "vstats")]
use crate::checker;
#[cfg(feature = "vstats")]
use std::env;
#[cfg(feature = "vstats")]
use std::sync::Mutex;
#[cfg(feature = "vstats")]
use std::sync::atomic::AtomicU64;
#[cfg(feature = "vstats")]
use std::sync::atomic::Ordering::Relaxed;

macro_rules! stats {
    ($($f:ident),*) => {
        #[cfg(feature = "vstats")]
        #[derive(Default, Clone, Copy, Debug)]
        pub struct Stats {
            $(pub $f: u64,)*
        }

        #[cfg(feature = "vstats")]
        impl Stats {
            pub(super) fn mk_kind(&mut self, kind: usize, hit: bool) {
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

            pub(super) fn add(&mut self, o: &Self) {
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
    resets,
    b_val,
    b_spine,
    b_env,
    b_frame,
    b_lazy,
    b_nat,
    b_sup
);

#[cfg(feature = "vstats")]
const ENV: &str = "NL_VSTATS";

#[cfg(feature = "vstats")]
const TOP_UNFOLDS: usize = 15;

#[cfg(feature = "vstats")]
pub static TOTAL: Mutex<Option<Stats>> = Mutex::new(None);

#[cfg(feature = "vstats")]
pub static RESETS: AtomicU64 = AtomicU64::new(0);

#[cfg(feature = "vstats")]
pub fn report() {
    if env::var_os(ENV).is_none() {
        return;
    }
    for (path, [n, t]) in ["native", "legacy"].iter().zip(&checker::BLOCKS) {
        let (n, t) = (n.load(Relaxed), t.load(Relaxed));
        eprintln!("vstats ind {path} blocks {n} {:.3} s", t as f64 * 1e-9);
    }
    if let Some(mut s) = *TOTAL
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
    {
        s.resets = RESETS.load(Relaxed);
        eprintln!("vstats total {s:?}");
    }
}

#[cfg(feature = "vstats")]
impl Vc<'_, '_> {
    pub(super) fn report_declaration(&self, idx: u32) {
        if env::var_os(ENV).is_none() {
            return;
        }
        eprintln!(
            "vstats {} {:?} arena {}",
            self.ctx.store.declars[idx as usize].name(),
            self.stats,
            self.ctx.arena.allocated_bytes()
        );
        let mut top: Vec<_> = self
            .unfolded
            .iter()
            .map(|(n, c)| (*c, n.to_string()))
            .collect();
        let s = &self.stats;
        let own = [
            s.b_val, s.b_spine, s.b_env, s.b_frame, s.b_lazy, s.b_nat, s.b_sup,
        ];
        eprintln!(
            "  bytes val {} spine {} env {} frame {} lazy {} nat {} sup {} rest {} headroom {}",
            s.b_val,
            s.b_spine,
            s.b_env,
            s.b_frame,
            s.b_lazy,
            s.b_nat,
            s.b_sup,
            self.used().saturating_sub(own.iter().sum::<u64>() as usize),
            self.ctx.arena.chunk_capacity()
        );
        let mut tables = self.t.footprint();
        tables.sort_unstable_by_key(|t| std::cmp::Reverse(t.2));
        for (name, len, bytes) in tables.iter().filter(|t| t.2 > 0) {
            eprintln!("  table {name} {len} {bytes}");
        }
        top.sort_unstable_by(|a, b| b.cmp(a));
        for (c, n) in top.iter().take(TOP_UNFOLDS) {
            eprintln!("  unfold {c} {n}");
        }
    }
}

macro_rules! bytes {
    ($s:expr, $f:ident, $n:expr) => {
        #[cfg(feature = "vstats")]
        {
            $s.stats.$f += ($n) as u64;
        }
    };
}
pub(crate) use bytes;

macro_rules! stat {
    ($s:expr, $f:ident) => {
        #[cfg(feature = "vstats")]
        {
            $s.stats.$f += 1;
        }
    };
}
pub(crate) use stat;
