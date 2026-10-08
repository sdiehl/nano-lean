use clap::{Parser, value_parser};
use indicatif::{ProgressBar, ProgressStyle};
use libmimalloc_sys::{mi_collect, mi_option_set, mi_option_t};
use nano_lean::checker::{Adapter, Limits};
use nano_lean::import::{self, ImportError, blean};
use nano_lean::term::{arena::Arena, intern::Store, outcome};
use nano_lean::value_checker::{self, Session};
use nano_lean::verdict::Core;
use std::collections::HashSet;
use std::io::{self, BufRead, IsTerminal, Read, Write};
use std::sync::atomic::{AtomicU32, AtomicUsize, Ordering::Relaxed};
use std::sync::mpsc::{self, RecvTimeoutError};
use std::time::{Duration, Instant};
use std::{fs, process, thread};

#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

const PROGRESS_TEMPLATE: &str = "{spinner:.green} [{elapsed_precise}] {wide_bar:.cyan/blue} {pos}/{len} {per_sec} ETA {eta_precise} {msg}";
const DEFAULT_STEPS: u64 = 200_000_000;
const DEFAULT_ARENA_MIB: u32 = 2048;
const MIB: usize = 1 << 20;
const MAX_THREADS: i64 = 64;
const WORKER_STACK_BYTES: usize = 64 << 20;
const FAILURES_SHOWN: usize = 30;
const TICK: Duration = Duration::from_millis(250);
const REPORT_INTERVAL: Duration = Duration::from_secs(10);
const SESSION_BYTES: usize = 64 << 20;
const MI_OPTION_PURGE_DELAY: mi_option_t = 15;

/// Check a Lean export (ndjson or blean) with the fast checker.
#[derive(Parser)]
#[command(name = "nl-fast")]
struct Cli {
    /// Export to check, or `-` for stdin
    path: Option<String>,
    #[arg(short = 'j', long, default_value_t = 1, value_parser = value_parser!(u16).range(1..=MAX_THREADS))]
    threads: u16,
    /// Check only this declaration
    #[arg(long, value_name = "NAME")]
    declaration: Option<String>,
    /// Check only the declarations listed one per line in FILE
    #[arg(long, value_name = "FILE")]
    only: Option<String>,
    /// Check at most N declarations
    #[arg(long, value_name = "N")]
    limit: Option<usize>,
    /// Work budget per declaration
    #[arg(long, value_name = "N", default_value_t = DEFAULT_STEPS)]
    steps: u64,
    #[arg(long, value_name = "MIB", default_value_t = DEFAULT_ARENA_MIB)]
    arena_mib: u32,
    /// Stop after import
    #[arg(long)]
    import_only: bool,
    #[arg(long)]
    trace: bool,
    /// Retry with a reset arena when a declaration exhausts it
    #[arg(long)]
    fallback: bool,
    /// Use the term core instead of the value core
    #[arg(long)]
    term_core: bool,
}

struct Options {
    path: Option<String>,
    threads: usize,
    selected: Option<String>,
    only: Option<HashSet<String>>,
    limit: usize,
    import_only: bool,
    trace: bool,
    native_only: bool,
    core: Core,
    limits: Limits,
}

fn names(file: &str) -> HashSet<String> {
    let text = fs::read_to_string(file).unwrap_or_else(|e| {
        eprintln!("{file}: {e}");
        process::exit(2)
    });
    text.lines()
        .map(str::trim)
        .filter(|l| !l.is_empty())
        .map(String::from)
        .collect()
}

fn options() -> Options {
    let cli = Cli::parse();
    Options {
        path: cli.path.filter(|p| p != "-"),
        threads: cli.threads.into(),
        selected: cli.declaration,
        only: cli.only.as_deref().map(names),
        limit: cli.limit.unwrap_or(usize::MAX),
        import_only: cli.import_only,
        trace: cli.trace,
        native_only: !cli.fallback,
        core: if cli.term_core {
            Core::Term
        } else {
            Core::Value
        },
        limits: Limits {
            steps: cli.steps,
            arena_bytes: cli.arena_mib as usize * MIB,
        },
    }
}

fn load<'a>(arena: &'a Arena, path: Option<&str>) -> Store<'a> {
    let imported = match path {
        Some(p) => import::import(arena, p),
        None => {
            let mut stdin = io::stdin().lock();
            if stdin.fill_buf().is_ok_and(blean::sniff) {
                let mut bytes = Vec::new();
                match stdin.read_to_end(&mut bytes) {
                    Ok(_) => import::import_bytes(arena, &bytes),
                    Err(e) => Err(ImportError::Invalid(e.to_string())),
                }
            } else {
                import::import_reader(arena, stdin, 0)
            }
        }
    };
    imported.unwrap_or_else(|e| {
        println!("{e}");
        process::exit(match e {
            ImportError::Invalid(_) => 1,
            ImportError::Unsupported(_) => 2,
        })
    })
}

fn main() {
    let o = options();
    let t = Instant::now();
    let arena = Arena::new();
    let store = load(&arena, o.path.as_deref());
    // Freed import buffers go back to the OS, and later frees stay mapped for reuse.
    // SAFETY: plain mimalloc calls, and -1 disables the purge delay.
    unsafe {
        mi_collect(true);
        mi_option_set(MI_OPTION_PURGE_DELAY, -1);
    }
    let s = store.stats;
    eprintln!(
        "import {:.2?} arena {} MiB, {} decls {} exprs {} names {} levels",
        t.elapsed(),
        arena.allocated_bytes() >> 20,
        s.declarations,
        s.expressions,
        s.names,
        s.levels
    );
    if o.import_only {
        return;
    }
    let filtered = o.selected.is_some() || o.only.is_some();
    let indices: Vec<_> = store
        .declars
        .iter()
        .enumerate()
        .filter(|(_, d)| {
            !filtered || {
                let name = d.name().to_string();
                o.selected.as_ref().is_none_or(|s| name == *s)
                    && o.only.as_ref().is_none_or(|set| set.contains(&name))
            }
        })
        .take(o.limit)
        .map(|(i, _)| i as u32)
        .collect();
    if filtered && indices.is_empty() {
        eprintln!("requested declaration not found");
        process::exit(2);
    }
    outcome::install_hook();
    let code = check(&o, &store, &indices);
    if code != 0 {
        process::exit(code as i32);
    }
}

fn check<'a>(o: &Options, store: &'a Store<'a>, indices: &[u32]) -> usize {
    let t = Instant::now();
    let next = AtomicU32::new(0);
    let fails = AtomicUsize::new(0);
    let fallbacks = AtomicUsize::new(0);
    let n = indices.len() as u32;
    let exit = AtomicUsize::new(0);
    let progress = if o.trace {
        ProgressBar::hidden()
    } else {
        ProgressBar::new(u64::from(n))
    };
    progress.set_style(
        ProgressStyle::with_template(PROGRESS_TEMPLATE).expect("valid progress template"),
    );
    let tally = || {
        format!(
            "{} fail, {} fallback",
            fails.load(Relaxed),
            fallbacks.load(Relaxed)
        )
    };
    progress.set_message(tally());
    progress.enable_steady_tick(TICK);
    let (stop, stopped) = mpsc::channel::<()>();
    thread::scope(|sc| {
        // Stop the reporter even if joining a worker unwinds.
        let stop = stop;
        if !o.trace && !io::stderr().is_terminal() {
            let (progress, tally) = (&progress, &tally);
            sc.spawn(move || {
                while let Err(RecvTimeoutError::Timeout) = stopped.recv_timeout(REPORT_INTERVAL) {
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
        let workers: Vec<_> = (0..o.threads)
            .map(|_| {
                thread::Builder::new()
                    .stack_size(WORKER_STACK_BYTES)
                    .spawn_scoped(sc, || {
                        let mut session = Session::new(store);
                        let mut adapter = Adapter::new(store);
                        loop {
                            let job = next.fetch_add(1, Relaxed);
                            if job >= n {
                                break;
                            }
                            let idx = indices[job as usize];
                            let started = Instant::now();
                            if o.trace {
                                eprintln!("start {idx} {}", store.declars[idx as usize].name());
                            }
                            let r = o.core.check(
                                store,
                                &mut session,
                                idx,
                                o.limits,
                                &mut adapter,
                                o.native_only,
                            );
                            if matches!(r, Ok(true)) {
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
                                || session.arena().allocated_bytes() > SESSION_BYTES
                            {
                                #[cfg(feature = "vstats")]
                                value_checker::RESETS.fetch_add(1, Relaxed);
                                session.reset();
                            }
                            progress.inc(1);
                            if let Err(f) = r {
                                exit.fetch_max(f.exit_code() as usize, Relaxed);
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
                                        let _ = io::stdout().flush();
                                    });
                                }
                            }
                        }
                    })
                    .unwrap()
            })
            .collect();
        for worker in workers {
            worker.join().unwrap();
        }
        drop(stop);
    });
    progress.finish_and_clear();
    eprintln!(
        "experimental checks {:.2?}: {} attempted, {} failures, {} fallbacks",
        t.elapsed(),
        n,
        fails.load(Relaxed),
        fallbacks.load(Relaxed)
    );
    if o.core == Core::Value {
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
    exit.load(Relaxed)
}
