use clap::Parser;
use notify::{Event, RecursiveMode, Watcher};
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

/// Rebuild a Lake project on every `.lean` change and recheck it with `nl-fast` and a cache.
#[derive(Parser)]
#[command(name = "nl-watch")]
struct Cli {
    /// Root modules to build and check
    #[arg(required = true)]
    modules: Vec<String>,
    #[arg(short = 'j', long)]
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
                // nl-fast saves the cache on SIGTERM, so give it a moment first.
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

/// Builds and checks once, returning `false` when a change cut it short.
fn cycle(cli: &Cli, fast: &Path, env: &[(String, String)], rx: &Receiver<()>) -> bool {
    let t = Instant::now();
    show("building...", b"");
    let build = cli
        .build
        .clone()
        .unwrap_or_else(|| format!("lake build {}", cli.modules.join(" ")));
    let Some((status, out)) = Job::spawn(Command::new("sh").args(["-c", &build])).wait(rx) else {
        return false;
    };
    if !status.success() {
        show(&format!("build failed in {:.1?}", t.elapsed()), &out);
        return true;
    }
    show("checking...", b"");
    let mut check = Command::new(fast);
    check
        .envs(env.iter().cloned())
        .args(["--quiet", "--cache", CACHE, "--olean"])
        .arg(cli.modules.join(","));
    let threads = cli.threads.map_or_else(
        || thread::available_parallelism().map_or(1, usize::from),
        usize::from,
    );
    check.arg("-j").arg(threads.to_string());
    let Some((_, out)) = Job::spawn(&mut check).wait(rx) else {
        return false;
    };
    show(&format!("total {:.1?}", t.elapsed()), &out);
    true
}

/// The search path Lake gives its tools, read once since each `lake` call costs seconds.
fn lake_env() -> Vec<(String, String)> {
    let out = Command::new("lake")
        .args(["env", "printenv"])
        .output()
        .unwrap_or_else(|e| die(format!("lake: {e}")));
    String::from_utf8_lossy(&out.stdout)
        .lines()
        .filter_map(|l| l.split_once('='))
        .filter(|(k, _)| matches!(*k, "LEAN_PATH" | "LEAN_SYSROOT"))
        .map(|(k, v)| (k.to_owned(), v.to_owned()))
        .collect()
}

fn main() {
    let cli = Cli::parse();
    let fast = std::env::current_exe()
        .ok()
        .map(|p| p.with_file_name("nl-fast"))
        .filter(|p| p.exists())
        .unwrap_or_else(|| PathBuf::from("nl-fast"));
    for sig in [libc::SIGINT, libc::SIGTERM] {
        // SAFETY: the handler only stores to an atomic.
        unsafe { libc::signal(sig, quit as *const () as libc::sighandler_t) };
    }
    let env = lake_env();
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
        if cycle(&cli, &fast, &env, &rx) {
            settle(&rx);
        } else {
            while rx.recv_timeout(DEBOUNCE).is_ok() {}
        }
    }
}
