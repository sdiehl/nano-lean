use clap::{Parser, value_parser};
use libmimalloc_sys::{mi_collect, mi_option_set, mi_option_t};
use nano_lean::export::ExportError;
use nano_lean::fast::{Checks, Config, MAX_THREADS};
use nano_lean::import::{self, blean};
use nano_lean::term::{arena::Arena, intern::Store};
use std::collections::HashSet;
use std::io::{self, BufRead, Read};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, Ordering::Relaxed};
use std::time::Instant;
use std::{fs, process};

#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

const MI_OPTION_PURGE_DELAY: mi_option_t = 15;

/// Check a Lean export (ndjson or blean) with the fast checker.
#[derive(Parser)]
#[command(name = "nl-fast")]
struct Cli {
    /// Export to check, or `-` for stdin
    #[arg(conflicts_with = "olean")]
    path: Option<String>,
    /// Check these modules and their imports from `.olean` files on `LEAN_PATH`
    #[arg(long, value_name = "MODULES", value_delimiter = ',')]
    olean: Option<Vec<String>>,
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
    /// Print only failures and a summary line
    #[arg(short, long)]
    quiet: bool,
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

struct Options {
    path: Option<String>,
    olean: Option<Vec<String>>,
    quiet: bool,
    selected: Option<String>,
    only: Option<HashSet<String>>,
    limit: usize,
    import_only: bool,
    prelude: Option<PathBuf>,
    axioms: Option<Vec<String>>,
    cache: Option<PathBuf>,
    checks: Checks,
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
    let mut c = Config::load(cli.config.as_deref()).unwrap_or_else(|e| {
        eprintln!("{e}");
        process::exit(2)
    });
    c.steps = cli.steps.or(c.steps);
    c.arena_mib = cli.arena_mib.or(c.arena_mib);
    c.term_core = Some(cli.term_core || c.term_core == Some(true));
    Options {
        path: cli.path.filter(|p| p != "-"),
        olean: cli.olean,
        quiet: cli.quiet,
        selected: cli.declaration,
        only: cli.only.as_deref().map(names),
        limit: cli.limit.unwrap_or(usize::MAX),
        import_only: cli.import_only,
        checks: Checks {
            threads: cli.threads.or(c.threads).unwrap_or(1).into(),
            trace: cli.trace,
            quiet: cli.quiet,
            native_only: !(cli.fallback || c.fallback == Some(true)),
            cache_audit: cli.cache_audit || c.cache_audit == Some(true),
            core: c.core(),
            limits: c.limits(),
        },
        prelude: cli.prelude.or(c.prelude),
        axioms: cli.axioms.or(c.axioms),
        cache: cli.cache.or(c.cache).filter(|_| !cli.no_cache),
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

/// Set once a signal arrives while checking, so workers stop and the cache is saved.
static STOP: AtomicBool = AtomicBool::new(false);
static CHECKING: AtomicBool = AtomicBool::new(false);

extern "C" fn interrupt(_: libc::c_int) {
    if !CHECKING.load(Relaxed) || STOP.swap(true, Relaxed) {
        // SAFETY: _exit is async-signal-safe.
        unsafe { libc::_exit(130) }
    }
}

fn on_interrupt() {
    for sig in [libc::SIGINT, libc::SIGTERM] {
        // SAFETY: the handler only touches atomics and calls _exit.
        unsafe { libc::signal(sig, interrupt as *const () as libc::sighandler_t) };
    }
}

fn main() {
    let o = options();
    if o.cache.is_some() {
        on_interrupt();
    }
    let t = Instant::now();
    let arena = Arena::new();
    let store = match &o.olean {
        Some(roots) => {
            let roots: Vec<&str> = roots.iter().map(String::as_str).collect();
            import::olean(&arena, &olean_export::search_path(), &roots)
                .unwrap_or_else(|e| exit_on(&e))
        }
        None => load(&arena, o.path.as_deref().map(Path::new)),
    };
    // Freed import buffers go back to the OS, and later frees stay mapped for reuse.
    // SAFETY: plain mimalloc calls, and -1 disables the purge delay.
    unsafe {
        mi_collect(true);
        mi_option_set(MI_OPTION_PURGE_DELAY, -1);
    }
    let s = store.stats;
    if !o.quiet {
        eprintln!(
            "import {:.2?} arena {} MiB, {} decls {} exprs {} names {} levels",
            t.elapsed(),
            arena.allocated_bytes() >> 20,
            s.declarations,
            s.expressions,
            s.names,
            s.levels
        );
    }
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
        let cache = o.cache.as_deref().map(|p| {
            o.checks.open_cache(&store, p).unwrap_or_else(|e| {
                eprintln!("{}: {e}", p.display());
                process::exit(2)
            })
        });
        CHECKING.store(true, Relaxed);
        let code = o.checks.run(
            &store,
            &indices,
            cache.as_ref().and_then(Option::as_ref),
            &STOP,
        );
        if let (Some(p), Some(Some(c))) = (&o.cache, &cache) {
            let keep = filtered || o.limit != usize::MAX || STOP.load(Relaxed);
            match c.save(p, keep) {
                Ok(k) if !o.quiet => {
                    eprintln!("cache {} hits, {k} recorded", c.hits.load(Relaxed));
                }
                Ok(_) => {}
                Err(e) => eprintln!("{}: {e}", p.display()),
            }
        }
        if STOP.load(Relaxed) {
            process::exit(130);
        }
        code
    };
    if code != 0 {
        process::exit(code as i32);
    }
}
