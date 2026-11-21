use super::Vc;
use crate::checker;
use std::env;
use std::sync::Mutex;
use std::sync::atomic::AtomicU64;
use std::sync::atomic::Ordering::Relaxed;

/// Interned value shapes, counted apart by `mk`.
#[derive(Clone, Copy)]
pub(super) enum Mk {
    Sort,
    PiOpen,
    PiClosed,
    LamOpen,
    LamClosed,
    NeuOpen,
    NeuClosed,
    Str,
}

macro_rules! stats {
    ($($f:ident),*) => {
                #[derive(Default, Clone, Copy, Debug)]
        pub struct Stats {
            $(pub $f: u64,)*
        }

                impl Stats {
            pub(super) fn mk_kind(&mut self, kind: Mk, hit: bool) {
                let [h, m] = match kind {
                    Mk::Sort => [&mut self.mk_sort_hit, &mut self.mk_sort_miss],
                    Mk::PiOpen => [&mut self.mk_pi_open_hit, &mut self.mk_pi_open_miss],
                    Mk::PiClosed => [&mut self.mk_pi_closed_hit, &mut self.mk_pi_closed_miss],
                    Mk::LamOpen => [&mut self.mk_lam_open_hit, &mut self.mk_lam_open_miss],
                    Mk::LamClosed => [&mut self.mk_lam_closed_hit, &mut self.mk_lam_closed_miss],
                    Mk::NeuOpen => [&mut self.mk_neu0_open_hit, &mut self.mk_neu0_open_miss],
                    Mk::NeuClosed => [&mut self.mk_neu0_closed_hit, &mut self.mk_neu0_closed_miss],
                    Mk::Str => [&mut self.mk_str_hit, &mut self.mk_str_miss],
                };
                *if hit { h } else { m } += 1;
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
    derives,
    derive_fails,
    fires,
    fire_misses,
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
    hit_app,
    hit_lam,
    hit_pi,
    hit_let,
    hit_leaf,
    hit_closed,
    hit_open,
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
    proj_probe,
    proj_hit,
    proj_put,
    eproj_probe,
    eproj_hit,
    resets,
    b_val,
    b_spine,
    b_env,
    b_frame,
    b_lazy,
    b_nat,
    b_sup,
    inst_hit,
    inst_miss
);

const ENV: &str = "NL_VSTATS";

const TOP_UNFOLDS: usize = 15;

pub static TOTAL: Mutex<Option<Stats>> = Mutex::new(None);

pub static RESETS: AtomicU64 = AtomicU64::new(0);

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
