use clap::{Parser, value_parser};
use indicatif::{ProgressBar, ProgressStyle};
use libmimalloc_sys::{mi_collect, mi_option_set, mi_option_t};
use nano_lean::cache::Cache;
use nano_lean::checker::{Adapter, Limits};
use nano_lean::export::ExportError;
use nano_lean::import::{self, blean};
use nano_lean::term::{arena::Arena, intern::Store};
use nano_lean::value_checker::{self, Session};
use nano_lean::verdict::Core;
use serde::Deserialize;
use std::collections::HashSet;
use std::io::{self, BufRead, IsTerminal, Read, Write};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU32, AtomicUsize, Ordering::Relaxed};
use std::sync::mpsc::{self, RecvTimeoutError};
use std::time::{Duration, Instant};
use std::{fs, process, thread};

#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

const PROGRESS_TEMPLATE: &str = "{spinner:.green} [{elapsed_precise}] {wide_bar:.cyan/blue} {pos}/{len} {per_sec} ETA {eta_precise} {msg}";
const DEFAULT_STEPS: u64 = 200_000_000;
const DEFAULT_ARENA_MIB: u32 = 2048;
const CONFIG: &str = "nano-lean.toml";
const MIB: usize = 1 << 20;
const MAX_THREADS: i64 = 64;
const WORKER_STACK_BYTES: usize = 256 << 20;
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
    /// Settings file, `nano-lean.toml` in the working directory by default
    #[arg(long, value_name = "FILE")]
    config: Option<PathBuf>,
    #[arg(short = 'j', long, value_parser = value_parser!(u16).range(1..=MAX_THREADS))]
    threads: Option<u16>,
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
    #[arg(long, value_name = "N")]
    steps: Option<u64>,
    #[arg(long, value_name = "MIB")]
    arena_mib: Option<u32>,
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
    /// Reject the export unless its primitives match this trusted export
    #[arg(long, value_name = "FILE")]
    prelude: Option<PathBuf>,
    /// Reject the export if it declares an axiom outside this list
    #[arg(long, value_name = "NAMES", value_delimiter = ',')]
    axioms: Option<Vec<String>>,
    /// Skip definitions and theorems FILE records as accepted, and record new ones
    #[arg(long, value_name = "FILE")]
    cache: Option<PathBuf>,
    /// Ignore the cache set in the config file
    #[arg(long, conflicts_with = "cache")]
    no_cache: bool,
    /// Check every declaration anyway, and fail if the cache records a rejected one as accepted
    #[arg(long)]
    cache_audit: bool,
}

/// The same settings as the flags, which override them.
#[derive(Default, Deserialize)]
#[serde(deny_unknown_fields)]
struct Config {
    threads: Option<u16>,
    steps: Option<u64>,
    arena_mib: Option<u32>,
    fallback: Option<bool>,
    term_core: Option<bool>,
    prelude: Option<PathBuf>,
    axioms: Option<Vec<String>>,
    cache: Option<PathBuf>,
    cache_audit: Option<bool>,
}

fn config(path: Option<&Path>) -> Config {
    let (path, explicit) = match path {
        Some(p) => (p, true),
        None => (Path::new(CONFIG), false),
    };
    let text = match fs::read_to_string(path) {
        Ok(t) => t,
        Err(e) if explicit || e.kind() != io::ErrorKind::NotFound => {
            eprintln!("{}: {e}", path.display());
            process::exit(2)
        }
        Err(_) => return Config::default(),
    };
    let mut c: Config = toml::from_str(&text).unwrap_or_else(|e| {
        eprintln!("{}: {e}", path.display());
        process::exit(2)
    });
    if c.threads
        .is_some_and(|j| !(1..=MAX_THREADS).contains(&i64::from(j)))
    {
        eprintln!("{}: threads must be in 1..={MAX_THREADS}", path.display());
        process::exit(2)
    }
    let dir = path.parent().unwrap_or(Path::new(""));
    c.prelude = c.prelude.map(|p| dir.join(p));
    c.cache = c.cache.map(|p| dir.join(p));
    c
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
    prelude: Option<PathBuf>,
    axioms: Option<Vec<String>>,
    cache: Option<PathBuf>,
    cache_audit: bool,
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
    let c = config(cli.config.as_deref());
    Options {
        path: cli.path.filter(|p| p != "-"),
        threads: cli.threads.or(c.threads).unwrap_or(1).into(),
        selected: cli.declaration,
        only: cli.only.as_deref().map(names),
        limit: cli.limit.unwrap_or(usize::MAX),
        import_only: cli.import_only,
        trace: cli.trace,
        native_only: !(cli.fallback || c.fallback == Some(true)),
        prelude: cli.prelude.or(c.prelude),
        axioms: cli.axioms.or(c.axioms),
        cache: cli.cache.or(c.cache).filter(|_| !cli.no_cache),
        cache_audit: cli.cache_audit || c.cache_audit == Some(true),
        core: if cli.term_core || c.term_core == Some(true) {
            Core::Term
        } else {
            Core::Value
        },
        limits: Limits {
            steps: cli.steps.or(c.steps).unwrap_or(DEFAULT_STEPS),
            arena_bytes: cli.arena_mib.or(c.arena_mib).unwrap_or(DEFAULT_ARENA_MIB) as usize * MIB,
        },
    }
}

fn exit_on(e: &ExportError) -> ! {
    println!("{e}");
    process::exit(match e {
        ExportError::Invalid(_) => 1,
        ExportError::Unsupported(_) => 2,
    })
}

fn load<'a>(arena: &'a Arena, path: Option<&Path>) -> Store<'a> {
    let imported = match path {
        Some(p) => import::import(arena, p),
        None => {
            let mut stdin = io::stdin().lock();
            if stdin.fill_buf().is_ok_and(blean::sniff) {
                let mut bytes = Vec::new();
                match stdin.read_to_end(&mut bytes) {
                    Ok(_) => import::import_bytes(arena, &bytes),
                    Err(e) => Err(ExportError::Invalid(e.to_string())),
                }
            } else {
                import::import_reader(arena, stdin, 0)
            }
        }
    };
    imported.unwrap_or_else(|e| exit_on(&e))
}

fn main() {
    let o = options();
    let t = Instant::now();
    let arena = Arena::new();
    let store = load(&arena, o.path.as_deref().map(Path::new));
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
    if let Some(p) = &o.prelude {
        let arena = Arena::new();
        let reference = load(&arena, Some(p));
        import::check_prelude(&store, &reference).unwrap_or_else(|e| exit_on(&e));
    }
    if let Some(a) = &o.axioms {
        import::check_axioms(&store, a).unwrap_or_else(|e| exit_on(&e));
    }
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
        .map(|(i, d)| match store.blocks.get(&d.name()) {
            Some(b) if filtered => b.start,
            _ => i as u32,
        })
        .collect();
    let mut indices = indices;
    indices.dedup();
    if filtered && indices.is_empty() {
        eprintln!("requested declaration not found");
        process::exit(2);
    }
    let code = {
        let cache = o.cache.as_deref().map(|p| open_cache(&o, &store, p));
        let code = check(
            &o,
            &store,
            &indices,
            cache.as_ref().and_then(Option::as_ref),
        );
        if let (Some(p), Some(Some(c))) = (&o.cache, &cache) {
            let keep = filtered || o.limit != usize::MAX;
            match c.save(p, keep) {
                Ok(k) => eprintln!("cache {} hits, {k} recorded", c.hits.load(Relaxed)),
                Err(e) => eprintln!("{}: {e}", p.display()),
            }
        }
        code
    };
    if code != 0 {
        process::exit(code as i32);
    }
}

fn open_cache<'a>(o: &Options, store: &'a Store<'a>, path: &Path) -> Option<Cache<'a>> {
    let t = Instant::now();
    let core = if o.core == Core::Term {
        "term"
    } else {
        "value"
    };
    let c = Cache::open(store, path, core, o.cache_audit).unwrap_or_else(|e| {
        eprintln!("{}: {e}", path.display());
        process::exit(2)
    });
    eprintln!("cache keys {:.2?}", t.elapsed());
    if c.is_none() {
        eprintln!("cache disabled: a primitive references an undeclared name");
    }
    c
}

fn check<'a>(
    o: &Options,
    store: &'a Store<'a>,
    indices: &[u32],
    cache: Option<&Cache<'a>>,
) -> usize {
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
                        let mut accepted = Vec::new();
                        loop {
                            let job = next.fetch_add(1, Relaxed);
                            if job >= n {
                                break;
                            }
                            let idx = indices[job as usize];
                            let (key, hit) = cache.map_or((None, false), |c| c.lookup(idx));
                            if hit && cache.is_some_and(|c| !c.audit) {
                                if o.trace {
                                    eprintln!("start {idx} {}", store.declars[idx as usize].name());
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
                            let r = o.core.check(
                                store,
                                &mut session,
                                idx,
                                o.limits,
                                &mut adapter,
                                o.native_only,
                            );
                            if r.is_ok() {
                                accepted.extend(key);
                            } else if hit && r.as_ref().is_err_and(|f| f.exit_code() == 1) {
                                exit.fetch_or(1 << 1, Relaxed);
                                println!(
                                    "cache audit: {} is recorded as accepted",
                                    store.declars[idx as usize].name()
                                );
                            }
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
    match exit.load(Relaxed) {
        0 => 0,
        b if b & 1 << 1 != 0 => 1,
        _ => 2,
    }
}
