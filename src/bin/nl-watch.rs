use clap::Parser;
use libmimalloc_sys::{mi_collect, mi_option_set, mi_option_t};
use nano_lean::fast::{Checks, Config};
use nano_lean::import;
use nano_lean::term::arena::Arena;
use notify::{Event, RecursiveMode, Watcher};
use olean_export::Env;
use std::io::{self, Read, Write};
use std::os::unix::process::CommandExt;
use std::path::{Component, Path, PathBuf};
use std::process::{self, Child, Command, ExitStatus, Stdio};
use std::sync::atomic::{AtomicBool, Ordering::Relaxed};
use std::sync::mpsc::{self, Receiver, RecvTimeoutError};
use std::thread::{self, JoinHandle};
use std::time::{Duration, Instant};

const POLL: Duration = Duration::from_millis(50);
const DEBOUNCE: Duration = Duration::from_millis(100);
const GRACE: Duration = Duration::from_secs(3);
const CACHE: &str = ".lake/nano-lean.accepted";
const MI_OPTION_PURGE_DELAY: mi_option_t = 15;

#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

/// Rebuild a Lake project on every `.lean` change and recheck it in place, reloading only the
/// modules that changed and skipping declarations the cache records as accepted.
#[derive(Parser)]
#[command(name = "nl-watch")]
struct Cli {
    /// Root modules to build and check
    #[arg(required = true)]
    modules: Vec<String>,
    #[arg(short = 'j', long, value_parser = clap::value_parser!(u16).range(1..=nano_lean::fast::MAX_THREADS))]
    threads: Option<u16>,
    /// Shell command run before each check, `lake build MODULES` by default
    #[arg(long, value_name = "CMD")]
    build: Option<String>,
}

static QUIT: AtomicBool = AtomicBool::new(false);

extern "C" fn quit(_: libc::c_int) {
    QUIT.store(true, Relaxed);
}

fn die(e: impl std::fmt::Display) -> ! {
    eprintln!("nl-watch: {e}");
    process::exit(2)
}

fn relevant(p: &Path) -> bool {
    let hidden = p.components().any(
        |c| matches!(c, Component::Normal(s) if s.to_str().is_some_and(|s| s.starts_with('.'))),
    );
    let name = p.file_name().and_then(|n| n.to_str()).unwrap_or("");
    !hidden
        && (p.extension().is_some_and(|e| e == "lean")
            || matches!(name, "lakefile.toml" | "lake-manifest.json"))
}

/// A child in its own process group, so a change can stop everything it started.
struct Job {
    child: Child,
    out: JoinHandle<Vec<u8>>,
    err: JoinHandle<Vec<u8>>,
}

fn drain(mut r: impl Read + Send + 'static) -> JoinHandle<Vec<u8>> {
    thread::spawn(move || {
        let mut b = Vec::new();
        r.read_to_end(&mut b).ok();
        b
    })
}

impl Job {
    fn spawn(cmd: &mut Command) -> Self {
        let mut child = cmd
            .process_group(0)
            .stdin(Stdio::null())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap_or_else(|e| die(e));
        let out = drain(child.stdout.take().expect("piped stdout"));
        let err = drain(child.stderr.take().expect("piped stderr"));
        Job { child, out, err }
    }

    fn signal(&self, sig: libc::c_int) {
        // SAFETY: plain kill on the group this job leads.
        unsafe { libc::kill(-(self.child.id() as libc::pid_t), sig) };
    }

    /// Waits for the job, or stops it and returns `None` once a file changes.
    fn wait(mut self, rx: &Receiver<()>) -> Option<(ExitStatus, Vec<u8>)> {
        loop {
            if let Some(status) = self.child.try_wait().unwrap_or_else(|e| die(e)) {
                let mut out = self.out.join().unwrap_or_default();
                out.extend(self.err.join().unwrap_or_default());
                return Some((status, out));
            }
            if QUIT.load(Relaxed) || rx.recv_timeout(POLL).is_ok() {
                // Give the build a moment to stop cleanly.
                self.signal(libc::SIGTERM);
                let t = Instant::now();
                while self.child.try_wait().ok().flatten().is_none() && t.elapsed() < GRACE {
                    thread::sleep(POLL);
                }
                self.signal(libc::SIGKILL);
                self.child.wait().ok();
                return None;
            }
        }
    }
}

fn show(status: &str, out: &[u8]) {
    let mut o = io::stdout().lock();
    write!(o, "\x1b[2J\x1b[H").ok();
    o.write_all(out).ok();
    writeln!(o, "{status}").ok();
    o.flush().ok();
}

/// Waits for a change, then for the burst of events around it to settle.
fn settle(rx: &Receiver<()>) {
    loop {
        if QUIT.load(Relaxed) {
            return;
        }
        match rx.recv_timeout(POLL) {
            Ok(()) => break,
            Err(RecvTimeoutError::Timeout) => {}
            Err(RecvTimeoutError::Disconnected) => die("watcher stopped"),
        }
    }
    while rx.recv_timeout(DEBOUNCE).is_ok() {}
}

/// What stays loaded between cycles.
struct Watch {
    cli: Cli,
    config: Config,
    checks: Checks,
    search: Vec<PathBuf>,
    env: Option<Env>,
}

impl Watch {
    /// Builds and checks once, returning `false` when a change cut it short.
    fn cycle(&mut self, rx: &Receiver<()>) -> bool {
        let t = Instant::now();
        show("building...", b"");
        let build = self
            .cli
            .build
            .clone()
            .unwrap_or_else(|| format!("lake build {}", self.cli.modules.join(" ")));
        let Some((status, out)) = Job::spawn(Command::new("sh").args(["-c", &build])).wait(rx)
        else {
            return false;
        };
        if !status.success() {
            show(&format!("build failed in {:.1?}", t.elapsed()), &out);
            return true;
        }
        show("checking...", b"");
        let done = match self.check(rx) {
            Ok(done) => done,
            Err(e) => {
                println!("{e}");
                true
            }
        };
        if done {
            println!("total {:.1?}", t.elapsed());
        }
        done
    }

    fn check(&mut self, rx: &Receiver<()>) -> Result<bool, String> {
        let olean = |e: olean_export::Error| format!("olean: {e}");
        let env = match &mut self.env {
            Some(env) => {
                env.reload().map_err(olean)?;
                env
            }
            None => {
                let roots: Vec<&str> = self.cli.modules.iter().map(String::as_str).collect();
                let env = Env::open(&self.search, &roots, self.checks.threads).map_err(olean)?;
                self.env.insert(env)
            }
        };
        let arena = Arena::new();
        let store = import::from_env(&arena, env).map_err(|e| e.to_string())?;
        // SAFETY: plain mimalloc calls, as in nl-fast.
        unsafe {
            mi_collect(true);
            mi_option_set(MI_OPTION_PURGE_DELAY, -1);
        }
        if let Some(p) = &self.config.prelude {
            let arena = Arena::new();
            let reference = import::import(&arena, p).map_err(|e| e.to_string())?;
            import::check_prelude(&store, &reference).map_err(|e| e.to_string())?;
        }
        if let Some(a) = &self.config.axioms {
            import::check_axioms(&store, a).map_err(|e| e.to_string())?;
        }
        let path = self.config.cache.as_deref().unwrap_or(Path::new(CACHE));
        let cache = self
            .checks
            .open_cache(&store, path)
            .map_err(|e| format!("{}: {e}", path.display()))?;
        let indices: Vec<u32> = (0..store.declars.len() as u32).collect();
        let stop = AtomicBool::new(false);
        thread::scope(|sc| {
            let run = sc.spawn(|| self.checks.run(&store, &indices, cache.as_ref(), &stop));
            while !run.is_finished() {
                if QUIT.load(Relaxed) || rx.recv_timeout(POLL).is_ok() {
                    stop.store(true, Relaxed);
                }
            }
            run.join().unwrap_or_else(|p| std::panic::resume_unwind(p));
        });
        let stopped = stop.load(Relaxed);
        if let Some(c) = &cache {
            c.save(path, stopped)
                .map_err(|e| format!("{}: {e}", path.display()))?;
        }
        Ok(!stopped)
    }
}

/// The search path Lake gives its tools, read once since each `lake` call costs seconds.
fn lake_path() -> Vec<PathBuf> {
    let out = Command::new("lake")
        .args(["env", "printenv"])
        .output()
        .unwrap_or_else(|e| die(format!("lake: {e}")));
    let text = String::from_utf8_lossy(&out.stdout);
    let var = |k: &str| {
        text.lines()
            .find_map(|l| l.strip_prefix(k)?.strip_prefix('='))
    };
    let mut dirs: Vec<PathBuf> = var("LEAN_PATH")
        .map(|p| std::env::split_paths(p).collect())
        .unwrap_or_default();
    dirs.extend(var("LEAN_SYSROOT").map(|r| Path::new(r).join("lib").join("lean")));
    dirs
}

fn main() {
    let cli = Cli::parse();
    let config = Config::load(None).unwrap_or_else(|e| die(e));
    let checks = Checks {
        threads: cli.threads.or(config.threads).map_or_else(
            || thread::available_parallelism().map_or(1, usize::from),
            usize::from,
        ),
        trace: false,
        quiet: true,
        native_only: config.fallback != Some(true),
        cache_audit: config.cache_audit == Some(true),
        core: config.core(),
        limits: config.limits(),
    };
    for sig in [libc::SIGINT, libc::SIGTERM] {
        // SAFETY: the handler only stores to an atomic.
        unsafe { libc::signal(sig, quit as *const () as libc::sighandler_t) };
    }
    let search = lake_path();
    let mut w = Watch {
        cli,
        config,
        checks,
        search,
        env: None,
    };
    let (tx, rx) = mpsc::channel();
    let mut watcher = notify::recommended_watcher(move |e: notify::Result<Event>| {
        if e.is_ok_and(|e| e.paths.iter().any(|p| relevant(p))) {
            tx.send(()).ok();
        }
    })
    .unwrap_or_else(|e| die(e));
    watcher
        .watch(Path::new("."), RecursiveMode::Recursive)
        .unwrap_or_else(|e| die(e));
    while !QUIT.load(Relaxed) {
        if w.cycle(&rx) {
            settle(&rx);
        } else {
            while rx.recv_timeout(DEBOUNCE).is_ok() {}
        }
    }
}
