use indicatif::{ProgressBar, ProgressStyle};
use nano_lean::checker::{Adapter, Limits};
use nano_lean::import::{self, ImportError, blean};
use nano_lean::term::{arena::Arena, intern::Store, outcome};
use nano_lean::value_checker::{self, Session};
use nano_lean::verdict::Core;
use std::collections::HashSet;
use std::ffi::c_long;
use std::io::{self, BufRead, IsTerminal, Read, Write};
use std::sync::atomic::{AtomicU32, AtomicUsize, Ordering::Relaxed};
use std::sync::mpsc::{self, RecvTimeoutError};
use std::time::{Duration, Instant};
use std::{env, fs, process, thread};

#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

const USAGE: &str = "usage: nl-fast [FILE|-] [-j THREADS] [--fallback] [--term-core] [--declaration NAME] [--only FILE] [--limit N] [--steps N] [--arena-mib N] [--import-only] [--trace]\nReads stdin when FILE is omitted or `-`.";
const PROGRESS_TEMPLATE: &str = "{spinner:.green} [{elapsed_precise}] {wide_bar:.cyan/blue} {pos}/{len} {per_sec} ETA {eta_precise} {msg}";
const DEFAULT_STEPS: u64 = 200_000_000;
const DEFAULT_ARENA_MIB: usize = 2048;
const MIB: usize = 1 << 20;
const MAX_THREADS: usize = 64;
const WORKER_STACK_BYTES: usize = 64 << 20;
const FAILURES_SHOWN: usize = 30;
const TICK: Duration = Duration::from_millis(250);
const REPORT_INTERVAL: Duration = Duration::from_secs(10);
const SESSION_BYTES: usize = 64 << 20;
const MI_OPTION_PURGE_DELAY: i32 = 15;

unsafe extern "C" {
    fn mi_option_set(option: i32, value: c_long);
    fn mi_collect(force: bool);
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

fn usage() -> ! {
    eprintln!("{USAGE}");
    process::exit(2)
}

fn number<T: std::str::FromStr>(args: &mut impl Iterator<Item = String>) -> T {
    value(args).parse().unwrap_or_else(|_| usage())
}

fn value(args: &mut impl Iterator<Item = String>) -> String {
    args.next().unwrap_or_else(|| usage())
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

fn options() -> Option<Options> {
    let mut o = Options {
        path: None,
        threads: 1,
        selected: None,
        only: None,
        limit: usize::MAX,
        import_only: false,
        trace: false,
        native_only: true,
        core: Core::Value,
        limits: Limits {
            steps: DEFAULT_STEPS,
            arena_bytes: DEFAULT_ARENA_MIB * MIB,
        },
    };
    let mut args = env::args().skip(1);
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "-h" | "--help" => {
                println!("{USAGE}");
                return None;
            }
            "-j" | "--threads" => o.threads = number(&mut args),
            "--declaration" => o.selected = Some(value(&mut args)),
            "--only" => o.only = Some(names(&value(&mut args))),
            "--limit" => o.limit = number(&mut args),
            "--import-only" => o.import_only = true,
            "--trace" => o.trace = true,
            "--fallback" => o.native_only = false,
            "--term-core" => o.core = Core::Term,
            "--steps" => o.limits.steps = number(&mut args),
            "--arena-mib" => {
                o.limits.arena_bytes = number::<usize>(&mut args)
                    .checked_mul(MIB)
                    .unwrap_or_else(|| usage())
            }
            "-" => o.path = None,
            a if a.starts_with('-') => usage(),
            _ if o.path.is_none() => o.path = Some(arg),
            _ => usage(),
        }
    }
    assert!(
        (1..=MAX_THREADS).contains(&o.threads),
        "thread count must be between 1 and 64"
    );
    Some(o)
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
    let Some(o) = options() else {
        return;
    };
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
