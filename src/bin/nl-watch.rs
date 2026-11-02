use clap::Parser;
use nano_lean::fast::{self, Checks, Config};
use nano_lean::import;
use nano_lean::term::arena::Arena;
use notify::{Event, RecursiveMode, Watcher};
use olean_export::Env;
use std::collections::VecDeque;
use std::io::{self, ErrorKind, Read, Write};
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
const TAIL: usize = 64 << 10;

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
    #[arg(short = 'j', long, value_parser = clap::value_parser!(u16).range(1..=fast::MAX_THREADS))]
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

/// Whether a file changed within `POLL`. A dead watcher still waits, so callers cannot spin.
fn changed(rx: &Receiver<()>) -> bool {
    match rx.recv_timeout(POLL) {
        Ok(()) => true,
        Err(RecvTimeoutError::Timeout) => false,
        Err(RecvTimeoutError::Disconnected) => {
            thread::sleep(POLL);
            false
        }
    }
}

fn interrupted(rx: &Receiver<()>) -> bool {
    QUIT.load(Relaxed) || changed(rx)
}

/// The last `cap` bytes of `r`, noting what was dropped and any read error.
fn tail(mut r: impl Read, cap: usize) -> Vec<u8> {
    let mut buf = VecDeque::<u8>::new();
    let mut chunk = [0; 8192];
    let mut dropped = 0;
    let err = loop {
        match r.read(&mut chunk) {
            Ok(0) => break None,
            Ok(n) => {
                buf.extend(&chunk[..n]);
                let over = buf.len().saturating_sub(cap);
                buf.drain(..over);
                dropped += over;
            }
            Err(e) if e.kind() == ErrorKind::Interrupted => {}
            Err(e) => break Some(e),
        }
    };
    let mut out = Vec::new();
    if dropped > 0 {
        out.extend(format!("[{dropped} earlier bytes dropped]\n").bytes());
    }
    out.extend(buf);
    if let Some(e) = err {
        out.extend(format!("\n[read failed: {e}]\n").bytes());
    }
    out
}

fn drain(r: impl Read + Send + 'static) -> JoinHandle<Vec<u8>> {
    thread::spawn(move || tail(r, TAIL))
}

/// A child in its own process group, so a change can stop everything it started.
struct Job {
    child: Child,
    out: JoinHandle<Vec<u8>>,
    err: JoinHandle<Vec<u8>>,
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
            match self.child.try_wait() {
                Ok(Some(status)) => return Some((status, self.output())),
                Ok(None) if !interrupted(rx) => {}
                Ok(None) => {
                    self.stop();
                    return None;
                }
                Err(e) => {
                    self.stop();
                    die(e)
                }
            }
        }
    }

    /// Ends a running job early, stopping its whole group gracefully and then by force.
    fn stop(mut self) {
        self.signal(libc::SIGTERM);
        let t = Instant::now();
        while self.child.try_wait().ok().flatten().is_none() && t.elapsed() < GRACE {
            thread::sleep(POLL);
        }
        self.signal(libc::SIGKILL);
        self.child.wait().ok();
    }

    fn output(self) -> Vec<u8> {
        let mut out = Vec::new();
        for (name, h) in [("stdout", self.out), ("stderr", self.err)] {
            out.extend(
                h.join()
                    .unwrap_or_else(|_| format!("\n[{name} reader panicked]\n").into()),
            );
        }
        out
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

enum Cycle {
    Passed,
    Failed,
    Interrupted,
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
    fn cycle(&mut self, rx: &Receiver<()>) -> Cycle {
        let t = Instant::now();
        show("building...", b"");
        let build = self
            .cli
            .build
            .clone()
            .unwrap_or_else(|| format!("lake build {}", self.cli.modules.join(" ")));
        let Some((status, out)) = Job::spawn(Command::new("sh").args(["-c", &build])).wait(rx)
        else {
            return Cycle::Interrupted;
        };
        if !status.success() {
            show(&format!("build failed in {:.1?}", t.elapsed()), &out);
            return Cycle::Failed;
        }
        show("checking...", b"");
        let cycle = self.check(rx).unwrap_or_else(|e| {
            println!("{e}");
            Cycle::Failed
        });
        match cycle {
            Cycle::Passed => println!("total {:.1?}", t.elapsed()),
            Cycle::Failed => println!("failed, total {:.1?}", t.elapsed()),
            Cycle::Interrupted => {}
        }
        cycle
    }

    fn check(&mut self, rx: &Receiver<()>) -> Result<Cycle, String> {
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
        fast::release_import_memory();
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
        let code = thread::scope(|sc| {
            let run = sc.spawn(|| self.checks.run(&store, &indices, cache.as_ref(), &stop));
            while !run.is_finished() {
                if interrupted(rx) {
                    stop.store(true, Relaxed);
                    break;
                }
            }
            run.join().unwrap_or_else(|p| std::panic::resume_unwind(p))
        });
        let stopped = stop.load(Relaxed);
        if let Some(c) = &cache {
            c.save(path, stopped)
                .map_err(|e| format!("{}: {e}", path.display()))?;
        }
        Ok(match (stopped, code) {
            (true, _) => Cycle::Interrupted,
            (false, 0) => Cycle::Passed,
            (false, _) => Cycle::Failed,
        })
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
    let threads = cli.threads.or(config.threads).map_or_else(
        || thread::available_parallelism().map_or(1, usize::from),
        usize::from,
    );
    let checks = config.checks(threads, false, true);
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
        match w.cycle(&rx) {
            Cycle::Passed | Cycle::Failed => settle(&rx),
            Cycle::Interrupted => while rx.recv_timeout(DEBOUNCE).is_ok() {},
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    struct Breaks(io::Cursor<Vec<u8>>);

    impl Read for Breaks {
        fn read(&mut self, b: &mut [u8]) -> io::Result<usize> {
            match self.0.read(b)? {
                0 => Err(io::Error::other("pipe broke")),
                n => Ok(n),
            }
        }
    }

    #[test]
    fn tail_keeps_the_end_and_reports_errors() {
        let input: Vec<u8> = (0..3 * TAIL as u32).map(|i| (i % 251) as u8).collect();
        let out = tail(Breaks(io::Cursor::new(input.clone())), TAIL);
        let head = format!("[{} earlier bytes dropped]\n", 2 * TAIL);
        let end = "\n[read failed: pipe broke]\n";
        assert!(out.starts_with(head.as_bytes()));
        assert!(out.ends_with(end.as_bytes()));
        assert_eq!(&out[head.len()..out.len() - end.len()], &input[2 * TAIL..]);
    }

    #[test]
    fn dead_watcher_does_not_spin() {
        let (tx, rx) = mpsc::channel();
        drop(tx);
        let t = Instant::now();
        assert!(!changed(&rx));
        assert!(t.elapsed() >= POLL);
    }
}
