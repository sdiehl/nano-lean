//! Opt-in counters and inclusive timings for a single export check.
use std::{cell::RefCell, collections::BTreeMap, time::Instant};

#[derive(Default)]
struct Stats {
    counts: BTreeMap<&'static str, u64>,
    seconds: BTreeMap<&'static str, f64>,
}
thread_local! {
    static STATS: RefCell<Stats> = RefCell::new(Stats::default());
}

pub(crate) fn count(name: &'static str) {
    STATS.with_borrow_mut(|s| *s.counts.entry(name).or_default() += 1);
}

pub(crate) struct Span(&'static str, Instant);
pub(crate) fn span(name: &'static str) -> Span {
    Span(name, Instant::now())
}
impl Drop for Span {
    fn drop(&mut self) {
        let seconds = self.1.elapsed().as_secs_f64();
        STATS.with_borrow_mut(|s| *s.seconds.entry(self.0).or_default() += seconds);
    }
}

pub(crate) struct Export(Instant);
pub(crate) fn export() -> Export {
    STATS.with_borrow_mut(|s| *s = Stats::default());
    Export(Instant::now())
}
impl Drop for Export {
    fn drop(&mut self) {
        STATS.with_borrow(|s| {
            eprintln!(
                "{}",
                serde_json::json!({"profile": {"counts": s.counts,
                    "inclusive_seconds": s.seconds, "total_seconds": self.0.elapsed().as_secs_f64()}})
            );
        });
    }
}
