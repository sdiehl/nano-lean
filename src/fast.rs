//! The parallel checking loop behind `nl-fast` and `nl-watch`.

use crate::cache::Cache;
use crate::checker::{Adapter, CheckPath, Core, Limits};
use crate::error::ExportError;
use crate::import;
use crate::resource::Budget;
use crate::term::arena::Arena;
use crate::term::intern::Store;
use crate::term::outcome::{Decline, Failure};
use crate::value_checker::{self, Session};
use indicatif::{ProgressBar, ProgressStyle};
use serde::Deserialize;
use std::io::{self, IsTerminal, Write};
use std::ops::RangeInclusive;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, AtomicU32, AtomicUsize, Ordering::Relaxed};
use std::sync::mpsc::{self, RecvTimeoutError};
use std::thread;
use std::time::{Duration, Instant};
use std::{fs, io::ErrorKind};

const PROGRESS_TEMPLATE: &str = "{spinner:.green} [{elapsed_precise}] {wide_bar:.cyan/blue} {pos}/{len} {per_sec} ETA {eta_precise} {msg}";
pub const CONFIG: &str = "nano-lean.toml";
pub const DEFAULT_STEPS: u64 = 200_000_000;
pub const DEFAULT_ARENA_MIB: u32 = 4096;
const WARM_SHARE: usize = 16;
pub const MAX_THREADS: i64 = 1024;
const MIB: usize = 1 << 20;
const WORKER_STACK_BYTES: usize = 256 << 20;
const FAILURES_SHOWN: usize = 30;
const TICK: Duration = Duration::from_millis(250);
const REPORT_INTERVAL: Duration = Duration::from_secs(10);
pub const DEFAULT_SESSION_MIB: u32 = 64;
/// The slot bits `table_bits` can cap the lossy memo tables at.
pub const TABLE_BITS: RangeInclusive<i64> = 10..=16;

/// The same settings as the `nl-fast` flags, which override them.
#[derive(Default, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Config {
    pub threads: Option<u16>,
    pub import_threads: Option<u16>,
    pub steps: Option<u64>,
    pub arena_mib: Option<u32>,
    pub session_mib: Option<u32>,
    pub table_bits: Option<u32>,
    #[serde(default)]
    pub fallback: bool,
    #[serde(default)]
    pub term_core: bool,
    pub prelude: Option<PathBuf>,
    pub axioms: Option<Vec<String>>,
    pub cache: Option<PathBuf>,
    #[serde(default)]
    pub cache_audit: bool,
}

impl Config {
    /// Reads `path`, or `nano-lean.toml` if it exists, resolving paths against its directory.
    pub fn load(path: Option<&Path>) -> Result<Self, String> {
        let (path, explicit) = match path {
            Some(p) => (p, true),
            None => (Path::new(CONFIG), false),
        };
        let fail = |e: &dyn std::fmt::Display| format!("{}: {e}", path.display());
        let text = match fs::read_to_string(path) {
            Ok(t) => t,
            Err(e) if explicit || e.kind() != ErrorKind::NotFound => return Err(fail(&e)),
            Err(_) => return Ok(Self::default()),
        };
        let mut c: Self = toml::from_str(&text).map_err(|e| fail(&e))?;
        if [c.threads, c.import_threads]
            .iter()
            .flatten()
            .any(|&j| !(1..=MAX_THREADS).contains(&i64::from(j)))
        {
            return Err(fail(&format!("threads must be in 1..={MAX_THREADS}")));
        }
        if c.table_bits
            .is_some_and(|b| !TABLE_BITS.contains(&i64::from(b)))
        {
            return Err(fail(&format!("table_bits must be in {TABLE_BITS:?}")));
        }
        let dir = path.parent().unwrap_or(Path::new(""));
        c.prelude = c.prelude.map(|p| dir.join(p));
        c.cache = c.cache.map(|p| dir.join(p));
        Ok(c)
    }

    /// Rejects `store` unless its primitives match the trusted prelude and it declares only
    /// permitted axioms.
    pub fn admit(&self, store: &Store<'_>) -> Result<(), ExportError> {
        if let Some(p) = &self.prelude {
            let arena = Arena::new();
            import::check_prelude(store, &import::import(&arena, p)?)?;
        }
        if let Some(a) = &self.axioms {
            import::check_axioms(store, a)?;
        }
        Ok(())
    }

    pub fn core(&self) -> Core {
        if self.term_core {
            Core::Term
        } else {
            Core::Value
        }
    }

    pub fn limits(&self) -> Limits {
        Limits {
            steps: self.steps.unwrap_or(DEFAULT_STEPS),
            arena_bytes: self.arena_mib.unwrap_or(DEFAULT_ARENA_MIB) as usize * MIB,
        }
    }

    pub fn checks(&self, threads: usize, trace: bool, quiet: bool) -> Checks {
        Checks {
            threads,
            trace,
            quiet,
            native_only: !self.fallback,
            cache_audit: self.cache_audit,
            core: self.core(),
            limits: self.limits(),
            session_bytes: self.session_mib.unwrap_or(DEFAULT_SESSION_MIB) as usize * MIB,
            table_bits: self.table_bits,
        }
    }
}

/// Installs `handler` for SIGINT and SIGTERM.
///
/// # Safety
///
/// `handler` must be async-signal-safe.
pub unsafe fn on_signals(handler: extern "C" fn(libc::c_int)) {
    for sig in [libc::SIGINT, libc::SIGTERM] {
        // SAFETY: the caller guarantees the handler is async-signal-safe.
        unsafe { libc::signal(sig, handler as *const () as libc::sighandler_t) };
    }
}

/// The session's tables count against the declaration's memory budget, so a warm session can
/// starve a declaration that fits in a fresh one.
fn budget_exhausted<T>(r: &Result<T, Failure>) -> bool {
    matches!(r, Err(Failure::Declined(Decline::Exhausted(Budget::Arena))))
}

/// Returns freed import buffers to the OS. Up to `KEEP_FREED_THREADS` workers, later frees stay
/// mapped for reuse, which saves instructions; beyond that, each worker would keep its peak
/// declaration resident, so frees are purged as usual.
pub fn release_import_memory(threads: usize) {
    const MI_OPTION_PURGE_DELAY: libmimalloc_sys::mi_option_t = 15;
    const KEEP_FREED_THREADS: usize = 16;
    // SAFETY: plain mimalloc calls, and -1 disables the purge delay.
    unsafe {
        libmimalloc_sys::mi_collect(true);
        if threads <= KEEP_FREED_THREADS {
            libmimalloc_sys::mi_option_set(MI_OPTION_PURGE_DELAY, -1);
        }
    }
}

pub struct Checks {
    pub threads: usize,
    pub trace: bool,
    pub quiet: bool,
    pub native_only: bool,
    pub cache_audit: bool,
    pub core: Core,
    pub limits: Limits,
    /// Session arena size past which a worker drops its tables and starts afresh.
    pub session_bytes: usize,
    /// Slot bits every lossy memo table is capped at, below its own size.
    pub table_bits: Option<u32>,
}

impl Checks {
    pub fn open_cache<'a>(
        &self,
        store: &'a Store<'a>,
        path: &Path,
    ) -> io::Result<Option<Cache<'a>>> {
        let t = Instant::now();
        let c = Cache::open(store, path, self.core, self.cache_audit)?;
        if !self.quiet {
            eprintln!("cache keys {:.2?}", t.elapsed());
        }
        if c.is_none() {
            eprintln!("cache disabled: a primitive references an undeclared name");
        }
        Ok(c)
    }

    /// Checks `indices` until done or `stop` is set, and returns the exit code: 1 when the
    /// cache audit caught a recorded rejection, 2 for any other failure.
    pub fn run<'a>(
        &self,
        store: &'a Store<'a>,
        indices: &[u32],
        cache: Option<&Cache<'a>>,
        stop: &AtomicBool,
    ) -> usize {
        let o = self;
        if let Some(b) = o.table_bits {
            value_checker::cap_tables(b);
        }
        let t = Instant::now();
        let next = AtomicU32::new(0);
        let fails = AtomicUsize::new(0);
        let fallbacks = AtomicUsize::new(0);
        let n = indices.len() as u32;
        let workers = o.threads.min(indices.len()).max(1);
        // Neighbours share constants, so runs keep a session's tables warm, shrinking near the end.
        let claim = || {
            let left = n.saturating_sub(next.load(Relaxed));
            let k = (left / (4 * workers as u32)).max(1);
            let at = next.fetch_add(k, Relaxed);
            (at < n).then(|| at..(at + k).min(n))
        };
        let exit = AtomicUsize::new(0);
        let tally = || {
            format!(
                "{} fail, {} fallback",
                fails.load(Relaxed),
                fallbacks.load(Relaxed)
            )
        };
        let progress = if o.trace || o.quiet {
            ProgressBar::hidden()
        } else {
            let p = ProgressBar::new(u64::from(n));
            p.set_style(
                ProgressStyle::with_template(PROGRESS_TEMPLATE).expect("valid progress template"),
            );
            p.set_message(tally());
            p.enable_steady_tick(TICK);
            p
        };
        let (done, stopped) = mpsc::channel::<()>();
        thread::scope(|sc| {
            // Stop the reporter even if joining a worker unwinds.
            let done = done;
            if !o.trace && !o.quiet && !io::stderr().is_terminal() {
                let (progress, tally) = (&progress, &tally);
                sc.spawn(move || {
                    while let Err(RecvTimeoutError::Timeout) = stopped.recv_timeout(REPORT_INTERVAL)
                    {
                        let eta = progress.eta().as_secs();
                        eprintln!(
                            "[progress] {}/{n} checked; {:.0}/s; estimated remaining {}m {}s; {}",
                            progress.position(),
                            progress.per_sec(),
                            eta / 60,
                            eta % 60,
                            tally()
                        );
                    }
                });
            }
            let workers: Vec<_> = (0..workers)
                .map(|_| {
                    thread::Builder::new()
                        .stack_size(WORKER_STACK_BYTES)
                        .spawn_scoped(sc, || {
                            let mut session = Session::new(store);
                            let mut adapter = Adapter::new(store);
                            let mut accepted = Vec::new();
                            let mut run = 0..0;
                            loop {
                                if stop.load(Relaxed) {
                                    break;
                                }
                                let Some(job) = run.next().or_else(|| {
                                    run = claim()?;
                                    run.next()
                                }) else {
                                    break;
                                };
                                let idx = indices[job as usize];
                                let (key, hit) = cache.map_or((None, false), |c| c.lookup(idx));
                                if hit && cache.is_some_and(|c| !c.audit) {
                                    if o.trace {
                                        eprintln!(
                                            "start {idx} {}",
                                            store.declars[idx as usize].name()
                                        );
                                        eprintln!("end {idx} cached");
                                    }
                                    accepted.extend(key);
                                    progress.inc(1);
                                    continue;
                                }
                                let started = Instant::now();
                                if o.trace {
                                    eprintln!("start {idx} {}", store.declars[idx as usize].name());
                                }
                                // A fresh session only rescues a declaration the warm one starved.
                                let warm = session.arena().used_bytes()
                                    > o.limits.arena_bytes / WARM_SHARE;
                                let mut r = o.core.check(
                                    store,
                                    &mut session,
                                    idx,
                                    o.limits,
                                    &mut adapter,
                                    o.native_only,
                                );
                                if warm && budget_exhausted(&r) {
                                    session.reset();
                                    r = o.core.check(
                                        store,
                                        &mut session,
                                        idx,
                                        o.limits,
                                        &mut adapter,
                                        o.native_only,
                                    );
                                }
                                if r.is_ok() {
                                    accepted.extend(key);
                                } else if hit && r.as_ref().is_err_and(|f| f.exit_code() == 1) {
                                    exit.fetch_or(1 << 1, Relaxed);
                                    println!(
                                        "cache audit: {} is recorded as accepted",
                                        store.declars[idx as usize].name()
                                    );
                                }
                                if matches!(r, Ok(CheckPath::Fallback)) {
                                    fallbacks.fetch_add(1, Relaxed);
                                    progress.set_message(tally());
                                }
                                if o.trace {
                                    eprintln!(
                                        "end {idx} elapsed {:?} arena {} bytes",
                                        started.elapsed(),
                                        session.arena().allocated_bytes()
                                    );
                                }
                                if o.core == Core::Term
                                    || r.is_err()
                                    || session.arena().allocated_bytes() > o.session_bytes
                                {
                                    #[cfg(feature = "vstats")]
                                    value_checker::RESETS.fetch_add(1, Relaxed);
                                    session.reset();
                                }
                                progress.inc(1);
                                if let Err(f) = r {
                                    exit.fetch_or(1 << f.exit_code(), Relaxed);
                                    let k = fails.fetch_add(1, Relaxed);
                                    progress.set_message(tally());
                                    if k < FAILURES_SHOWN {
                                        progress.suspend(|| {
                                            println!(
                                                "{} {}: {}",
                                                store.declars[idx as usize].name().as_ref(),
                                                f.status(),
                                                f.reason()
                                            );
                                            io::stdout().flush().ok();
                                        });
                                    }
                                }
                            }
                            if let Some(c) = cache {
                                c.record(&accepted);
                            }
                        })
                        .expect("spawn worker thread")
                })
                .collect();
            for worker in workers {
                worker
                    .join()
                    .unwrap_or_else(|p| std::panic::resume_unwind(p));
            }
            drop(done);
        });
        progress.finish_and_clear();
        let hits = cache.map_or(0, |c| c.hits.load(Relaxed));
        if o.quiet {
            let checked = progress.position();
            let fails = fails.load(Relaxed);
            let cut = if checked < u64::from(n) {
                format!(", interrupted after {checked} of {n}")
            } else {
                String::new()
            };
            eprintln!(
                "{} {n} declarations, {hits} cached, {fails} failed in {:.2?}{cut}",
                if fails == 0 { "ok" } else { "FAIL" },
                t.elapsed(),
            );
        } else {
            eprintln!(
                "experimental checks {:.2?}: {} attempted, {} failures, {} fallbacks",
                t.elapsed(),
                n,
                fails.load(Relaxed),
                fallbacks.load(Relaxed)
            );
        }
        if o.core == Core::Value && !o.quiet {
            let b = &value_checker::BRIDGED;
            eprintln!(
                "bridged quot {} ind {} ctor {} rec {}",
                b[0].load(Relaxed),
                b[1].load(Relaxed),
                b[2].load(Relaxed),
                b[3].load(Relaxed)
            );
            #[cfg(feature = "vstats")]
            value_checker::report();
        }
        match exit.load(Relaxed) {
            0 => 0,
            b if b & 1 << 1 != 0 => 1,
            _ => 2,
        }
    }
}
