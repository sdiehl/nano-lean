//! Kernel benchmarks. `cargo bench --bench kernel -- --help` lists the flags, and
//! docs/BENCH.md describes the suite. Without `--bench`, as under `cargo test`, every micro
//! bench runs once and must check cleanly.

use clap::Parser;
use libmimalloc_sys::{mi_collect, mi_option_set, mi_option_t};
use nano_lean::checker::{Adapter, Limits};
use nano_lean::fast::Config;
use nano_lean::term::{arena::Arena, intern::Store};
use nano_lean::value_checker::Session;
use nano_lean::verdict::Core;
use nano_lean::{emit, import, parser};
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::time::Instant;
use std::{fs, process, thread};

// The nl-fast worker settings, kept local so the harness also builds against older revisions.
const WORKER_STACK_BYTES: usize = 256 << 20;
const SESSION_BYTES: usize = 64 << 20;

#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

const MI_OPTION_PURGE_DELAY: mi_option_t = 15;
const ROOT: &str = env!("CARGO_MANIFEST_DIR");

#[derive(Parser)]
#[command(name = "kernel")]
struct Cli {
    /// Run only benches whose name contains this
    filter: Option<String>,
    /// Override every bench's repetition count
    #[arg(long)]
    reps: Option<usize>,
    /// Save results as NAME under target/nl-bench
    #[arg(long, value_name = "NAME")]
    save: Option<String>,
    /// Compare against results saved as NAME
    #[arg(long, value_name = "NAME")]
    baseline: Option<String>,
    /// Print one JSON record per bench instead of a table
    #[arg(long)]
    json: bool,
    /// List benches and whether their inputs are present
    #[arg(long)]
    list: bool,
    /// Suite manifest, benches/suite.toml by default
    #[arg(long, value_name = "FILE")]
    suite: Option<PathBuf>,
    #[arg(long, hide = true)]
    bench: bool,
}

#[derive(Deserialize)]
struct Suite {
    bench: Vec<Spec>,
}

#[derive(Clone, Copy, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "lowercase")]
enum Kind {
    /// Every declaration in order on one session, as `nl-fast -j 1` does.
    All,
    /// One declaration on a fresh session, the last one unless named.
    Target,
    /// Decoding the export into a store.
    Import,
}

#[derive(Deserialize)]
struct Spec {
    name: String,
    file: PathBuf,
    kind: Kind,
    declaration: Option<String>,
    #[serde(default = "default_reps")]
    reps: usize,
}

fn default_reps() -> usize {
    5
}

#[derive(Clone, Copy, Default)]
struct Sample {
    instructions: u64,
    cycles: u64,
    user_ns: u64,
    wall_ns: u64,
}

#[derive(Default)]
struct Work {
    decls: usize,
    failed: usize,
    arena: u64,
}

#[derive(Serialize, Deserialize)]
struct Record {
    name: String,
    decls: usize,
    failed: usize,
    reps: usize,
    instructions: u64,
    cycles: u64,
    user_ms: f64,
    wall_ms: f64,
    arena: u64,
    arena_stable: bool,
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    vstats: BTreeMap<String, u64>,
}

#[cfg(target_os = "macos")]
fn counters() -> (u64, u64) {
    // SAFETY: rusage_info_v4 is plain data, and the call writes at most its size.
    unsafe {
        let mut ri: libc::rusage_info_v4 = std::mem::zeroed();
        let r = libc::proc_pid_rusage(
            libc::getpid(),
            libc::RUSAGE_INFO_V4,
            (&raw mut ri).cast::<libc::rusage_info_t>().cast(),
        );
        if r == 0 {
            (ri.ri_instructions, ri.ri_cycles)
        } else {
            (0, 0)
        }
    }
}

#[cfg(not(target_os = "macos"))]
fn counters() -> (u64, u64) {
    (0, 0)
}

fn user_ns() -> u64 {
    // SAFETY: getrusage fills the struct it is given.
    let ru = unsafe {
        let mut ru: libc::rusage = std::mem::zeroed();
        libc::getrusage(libc::RUSAGE_SELF, &raw mut ru);
        ru
    };
    ru.ru_utime.tv_sec as u64 * 1_000_000_000 + ru.ru_utime.tv_usec as u64 * 1000
}

fn measure(f: impl FnOnce() -> Work) -> (Sample, Work) {
    let (i0, c0) = counters();
    let u0 = user_ns();
    let t = Instant::now();
    let w = f();
    let wall_ns = t.elapsed().as_nanos() as u64;
    let (i1, c1) = counters();
    let s = Sample {
        instructions: i1 - i0,
        cycles: c1 - c0,
        user_ns: user_ns() - u0,
        wall_ns,
    };
    (s, w)
}

#[cfg(feature = "vstats")]
fn vstats() -> BTreeMap<String, u64> {
    let s = nano_lean::value_checker::TOTAL
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
        .take();
    s.map(|s| {
        [
            ("evals", s.evals),
            ("applies", s.applies),
            ("whnfs", s.whnfs),
            ("unfolds", s.unfolds),
            ("deq_calls", s.deq_calls),
            ("probes", s.probes),
            ("memo_hits", s.memo_hits),
        ]
        .into_iter()
        .map(|(k, v)| (k.to_owned(), v))
        .collect()
    })
    .unwrap_or_default()
}

#[cfg(not(feature = "vstats"))]
fn vstats() -> BTreeMap<String, u64> {
    BTreeMap::new()
}

fn source(path: &Path) -> Result<Vec<u8>, String> {
    let fail = |e: &dyn std::fmt::Display| format!("{}: {e}", path.display());
    if path.extension().is_some_and(|e| e == "ltc") {
        let text = fs::read_to_string(path).map_err(|e| fail(&e))?;
        let decls = parser::declarations(&text).map_err(|e| fail(&e))?;
        return emit::ndjson(&decls)
            .map(String::into_bytes)
            .map_err(|e| fail(&e));
    }
    fs::read(path).map_err(|e| fail(&e))
}

fn load<'a>(arena: &'a Arena, bytes: &[u8]) -> Result<Store<'a>, String> {
    import::import_bytes(arena, bytes).map_err(|e| e.to_string())
}

fn target(store: &Store<'_>, name: Option<&str>) -> Result<u32, String> {
    let n = store.declars.len();
    let idx = match name {
        None => n.checked_sub(1).ok_or("empty export")?,
        Some(s) => store
            .declars
            .iter()
            .position(|d| d.name().to_string() == s)
            .ok_or_else(|| format!("declaration {s} not found"))?,
    };
    let d = store.declars[idx];
    Ok(store.blocks.get(&d.name()).map_or(idx as u32, |b| b.start))
}

/// Bytes in use, where `allocated_bytes` counts whole chunks.
fn used(a: &Arena) -> u64 {
    let bump: &bumpalo::Bump = a;
    // SAFETY: nothing allocates in the arena while its chunks are walked.
    let chunks: usize = unsafe { bump.iter_allocated_chunks_raw().map(|(_, n)| n).sum() };
    (chunks + a.allocated_bytes() - bump.allocated_bytes()) as u64
}

fn check<'a>(store: &'a Store<'a>, indices: impl Iterator<Item = u32>, limits: Limits) -> Work {
    let mut session = Session::new(store);
    let mut adapter = Adapter::new(store);
    let mut w = Work::default();
    for idx in indices {
        let before = used(session.arena());
        let r = Core::Value.check(store, &mut session, idx, limits, &mut adapter, true);
        w.decls += 1;
        w.arena += used(session.arena()).saturating_sub(before);
        if r.is_err() {
            w.failed += 1;
        }
        if r.is_err() || session.arena().allocated_bytes() > SESSION_BYTES {
            session.reset();
        }
    }
    w
}

fn median(mut xs: Vec<u64>) -> u64 {
    xs.sort_unstable();
    xs[xs.len() / 2]
}

fn run(spec: &Spec, path: &Path, reps: usize, warm: usize) -> Result<Record, String> {
    let bytes = source(path)?;
    let limits = Config::default().limits();
    let arena = Arena::new();
    let store = if spec.kind == Kind::Import {
        None
    } else {
        Some(load(&arena, &bytes)?)
    };
    let idx = match &store {
        Some(s) if spec.kind == Kind::Target => Some(target(s, spec.declaration.as_deref())?),
        _ => None,
    };
    // SAFETY: plain mimalloc call.
    unsafe { mi_collect(true) };
    let mut samples = Vec::with_capacity(reps);
    let mut works = Vec::with_capacity(reps);
    let mut stats = BTreeMap::new();
    for i in 0..warm + reps {
        vstats();
        let (s, w) = match (&store, idx) {
            (None, _) => {
                let (s, r) = measure(|| {
                    let a = Arena::new();
                    let decls = load(&a, &bytes).map_or(0, |s| s.declars.len());
                    Work {
                        decls,
                        failed: 0,
                        arena: used(&a),
                    }
                });
                (s, r)
            }
            (Some(st), Some(t)) => measure(|| check(st, std::iter::once(t), limits)),
            (Some(st), None) => measure(|| check(st, 0..st.declars.len() as u32, limits)),
        };
        if i >= warm {
            samples.push(s);
            works.push(w);
            stats = vstats();
        }
    }
    let w = &works[0];
    Ok(Record {
        name: spec.name.clone(),
        decls: w.decls,
        failed: w.failed,
        reps,
        instructions: samples.iter().map(|s| s.instructions).min().unwrap_or(0),
        cycles: samples.iter().map(|s| s.cycles).min().unwrap_or(0),
        user_ms: median(samples.iter().map(|s| s.user_ns).collect()) as f64 / 1e6,
        wall_ms: median(samples.iter().map(|s| s.wall_ns).collect()) as f64 / 1e6,
        arena: w.arena,
        arena_stable: works.iter().all(|x| x.arena == w.arena),
        vstats: stats,
    })
}

fn si(x: u64) -> String {
    match x {
        0 => "-".into(),
        x if x >= 1_000_000_000 => format!("{:.2}G", x as f64 / 1e9),
        x if x >= 1_000_000 => format!("{:.2}M", x as f64 / 1e6),
        x if x >= 1_000 => format!("{:.1}K", x as f64 / 1e3),
        x => x.to_string(),
    }
}

fn delta(new: f64, old: f64) -> String {
    if old == 0.0 {
        "-".into()
    } else {
        format!("{:+.2}%", (new / old - 1.0) * 100.0)
    }
}

fn row(r: &Record, base: Option<&Record>) -> String {
    let mut s = format!(
        "{:<34} {:>7} {:>4} {:>9} {:>9} {:>10.2} {:>10.2} {:>9}{}",
        r.name,
        r.decls,
        r.failed,
        si(r.instructions),
        si(r.cycles),
        r.wall_ms,
        r.user_ms,
        si(r.arena),
        if r.arena_stable { ' ' } else { '~' }
    );
    if let Some(b) = base {
        let (i, w) = (
            delta(r.instructions as f64, b.instructions as f64),
            delta(r.wall_ms, b.wall_ms),
        );
        let a = if r.arena == b.arena {
            "="
        } else {
            "arena changed"
        };
        let _ = write!(s, " {i:>9} {w:>9}  {a}");
    }
    for (k, v) in &r.vstats {
        let _ = write!(s, " {k}={}", si(*v));
    }
    s
}

fn saved(name: &str) -> PathBuf {
    Path::new(ROOT)
        .join("target/nl-bench")
        .join(format!("{name}.json"))
}

fn main() {
    let cli = Cli::parse();
    // SAFETY: plain mimalloc call; -1 keeps freed pages mapped, as nl-fast does.
    unsafe { mi_option_set(MI_OPTION_PURGE_DELAY, -1) };
    let worker = thread::Builder::new()
        .stack_size(WORKER_STACK_BYTES)
        .spawn(move || bench(&cli))
        .expect("spawn bench thread");
    let code = worker.join().unwrap_or(2);
    process::exit(code);
}

fn bench(cli: &Cli) -> i32 {
    let suite_path = cli
        .suite
        .clone()
        .unwrap_or_else(|| Path::new(ROOT).join("benches/suite.toml"));
    let dir = suite_path.parent().unwrap_or(Path::new("."));
    let suite: Suite = match fs::read_to_string(&suite_path)
        .map_err(|e| e.to_string())
        .and_then(|t| toml::from_str(&t).map_err(|e| e.to_string()))
    {
        Ok(s) => s,
        Err(e) => {
            eprintln!("{}: {e}", suite_path.display());
            return 2;
        }
    };
    let smoke = !cli.bench;
    let base: BTreeMap<String, Record> = match &cli.baseline {
        Some(n) => match fs::read(saved(n))
            .map_err(|e| e.to_string())
            .and_then(|b| serde_json::from_slice::<Vec<Record>>(&b).map_err(|e| e.to_string()))
        {
            Ok(v) => v.into_iter().map(|r| (r.name.clone(), r)).collect(),
            Err(e) => {
                eprintln!("{}: {e}", saved(n).display());
                return 2;
            }
        },
        None => BTreeMap::new(),
    };
    if !cli.json && !cli.list {
        let mut h = format!(
            "{:<34} {:>7} {:>4} {:>9} {:>9} {:>10} {:>10} {:>10}",
            "bench", "decls", "fail", "instr", "cycles", "wall ms", "user ms", "arena"
        );
        if cli.baseline.is_some() {
            let _ = write!(h, " {:>9} {:>9}", "d instr", "d wall");
        }
        println!("{h}");
    }
    let mut records = Vec::new();
    let mut missing = 0;
    let mut code = 0;
    for spec in &suite.bench {
        let micro = spec.file.extension().is_some_and(|e| e == "ltc");
        if cli
            .filter
            .as_ref()
            .is_some_and(|f| !spec.name.contains(f.as_str()))
            || smoke && !micro
        {
            continue;
        }
        let path = dir.join(&spec.file);
        if cli.list {
            let state = if path.exists() { "" } else { "  (missing)" };
            println!("{}{state}", spec.name);
            continue;
        }
        if !path.exists() {
            missing += 1;
            continue;
        }
        let (reps, warm) = if smoke {
            (1, 0)
        } else {
            (cli.reps.unwrap_or(spec.reps).max(1), 1)
        };
        match run(spec, &path, reps, warm) {
            Ok(r) => {
                if cli.json {
                    println!("{}", serde_json::to_string(&r).unwrap_or_default());
                } else {
                    println!("{}", row(&r, base.get(&r.name)));
                }
                if smoke && r.failed > 0 {
                    eprintln!("{}: {} declarations failed", r.name, r.failed);
                    code = 1;
                }
                records.push(r);
            }
            Err(e) => {
                eprintln!("{}: {e}", spec.name);
                code = 1;
            }
        }
    }
    if missing > 0 && !cli.json {
        eprintln!("{missing} benches skipped for missing inputs, see benches/fixtures.sh");
    }
    if let Some(n) = &cli.save {
        let p = saved(n);
        let written = p
            .parent()
            .map_or(Ok(()), fs::create_dir_all)
            .and_then(|()| fs::write(&p, serde_json::to_vec_pretty(&records).unwrap_or_default()));
        match written {
            Ok(()) => eprintln!("saved {}", p.display()),
            Err(e) => {
                eprintln!("{}: {e}", p.display());
                code = 2;
            }
        }
    }
    code
}
