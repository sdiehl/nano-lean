use nano_lean::export::{ExportReport, Report, ShardReport, TRACE_VAR, Trace};
use serde_json::Value;
use std::{
    env,
    io::{self, BufRead, BufReader, Read},
    path::Path,
    process::{self, Child, Command, Stdio},
    sync::{Arc, Mutex, PoisonError},
    thread,
    time::{Duration, Instant},
};

const PROGRESS_VAR: &str = "NANO_LEAN_PROGRESS";
const MAX_JOBS: usize = 64;
const MIB: usize = 1024 * 1024;
const BRIEF_CHARS: usize = 200;
const OUTPUT_LIMIT: u64 = 1024 * 1024;
const PROGRESS_INTERVAL: Duration = Duration::from_secs(10);
const POLL_INTERVAL: Duration = Duration::from_millis(20);

type Output = thread::JoinHandle<io::Result<Vec<u8>>>;
#[derive(Clone, Default)]
struct Snapshot {
    imported: u64,
    assigned: u64,
    name: String,
}
struct Worker {
    index: usize,
    child: Child,
    output: Output,
    stderr: thread::JoinHandle<io::Result<()>>,
    progress: Arc<Mutex<Option<Snapshot>>>,
}
struct Workers(Vec<Worker>);
impl Drop for Workers {
    fn drop(&mut self) {
        for worker in &mut self.0 {
            worker.child.kill().ok();
            worker.child.wait().ok();
        }
    }
}

pub fn run(path: &str, jobs: usize, memory_mib: usize) -> Result<Report, String> {
    let progress = match env::var(PROGRESS_VAR).as_deref() {
        Ok("0") => false,
        Ok(_) => true,
        Err(_) => env::var("GITHUB_ACTIONS").as_deref() == Ok("true"),
    };
    let start = Instant::now();
    let result = run_workers(path, jobs, memory_mib, progress);
    if progress {
        match &result {
            Ok((report, _)) => eprintln!(
                "[progress] complete: {} declarations checked in {}s",
                report.declarations,
                start.elapsed().as_secs()
            ),
            Err(reason) => eprintln!(
                "[progress] stopped after {}s: {}",
                start.elapsed().as_secs(),
                brief(reason)
            ),
        }
    }
    result.map(|(report, sha256)| Report::Checked {
        report,
        workers: Some(jobs),
        sha256: Some(sha256),
    })
}

fn brief(text: &str) -> String {
    text.chars()
        .take(BRIEF_CHARS)
        .map(|c| if c.is_control() { ' ' } else { c })
        .collect()
}

fn status(index: usize, jobs: usize, snapshot: Option<&Snapshot>) -> String {
    match snapshot {
        None => format!("worker {}/{}: scanning export", index + 1, jobs),
        Some(s) if jobs == 1 => format!(
            "worker 1/1: {} declarations checked; checking {}",
            s.imported,
            brief(&s.name)
        ),
        Some(s) => format!(
            "worker {}/{}: {} assigned declarations checked, {} imported; checking {}",
            index + 1,
            jobs,
            s.assigned,
            s.imported,
            brief(&s.name)
        ),
    }
}

fn run_workers(
    path: &str,
    jobs: usize,
    memory_mib: usize,
    progress: bool,
) -> Result<(ExportReport, String), String> {
    if !(1..=MAX_JOBS).contains(&jobs) {
        return Err(format!("worker count must be between 1 and {MAX_JOBS}"));
    }
    let budget = memory_mib
        .checked_mul(MIB)
        .filter(|&n| n > 0)
        .ok_or("memory budget must be a positive number of MiB")? as u64;
    memory_bytes(process::id()).map_err(|e| format!("cannot monitor memory: {e}"))?;
    let started = Instant::now();
    let mut last_progress = Instant::now();
    if progress {
        eprintln!(
            "[progress] starting {jobs} worker(s), {memory_mib} MiB total budget; scanning export"
        );
    }
    let trace_requested = env::var_os(TRACE_VAR).is_some();
    let executable = env::current_exe().map_err(|e| e.to_string())?;
    let mut workers = Workers(Vec::new());
    for index in 0..jobs {
        let worker = spawn(&executable, path, index, jobs, progress, trace_requested)?;
        workers.0.push(worker);
    }
    let mut reports = vec![None; jobs];
    while !workers.0.is_empty() {
        let mut total = memory_bytes(process::id()).map_err(|e| e.to_string())?;
        for worker in &mut workers.0 {
            let child = &mut worker.child;
            if child.try_wait().map_err(|e| e.to_string())?.is_none() {
                match memory_bytes(child.id()) {
                    Ok(bytes) => total = total.saturating_add(bytes),
                    // A worker may exit between try_wait and the memory query.
                    Err(_) if child.try_wait().map_err(|e| e.to_string())?.is_some() => {}
                    Err(e) => return Err(format!("cannot monitor worker memory: {e}")),
                }
            }
        }
        if total > budget {
            return Err(format!(
                "memory budget exceeded: {} MiB used, {memory_mib} MiB limit; workers stopped",
                total / MIB as u64
            ));
        }
        if progress && last_progress.elapsed() >= PROGRESS_INTERVAL {
            eprintln!(
                "[progress] elapsed {}s | memory {} / {memory_mib} MiB | {} / {jobs} workers finished",
                started.elapsed().as_secs(),
                total / MIB as u64,
                jobs - workers.0.len()
            );
            for worker in &workers.0 {
                let snapshot = worker
                    .progress
                    .lock()
                    .unwrap_or_else(PoisonError::into_inner);
                eprintln!(
                    "[progress] {}",
                    status(worker.index, jobs, snapshot.as_ref())
                );
            }
            last_progress = Instant::now();
        }
        let mut i = 0;
        while i < workers.0.len() {
            if workers.0[i]
                .child
                .try_wait()
                .map_err(|e| e.to_string())?
                .is_none()
            {
                i += 1;
                continue;
            }
            let (index, report) = finish(workers.0.swap_remove(i))?;
            if progress {
                eprintln!(
                    "[progress] worker {}/{} finished its partition in {}s; awaiting all workers",
                    index + 1,
                    jobs,
                    started.elapsed().as_secs()
                );
            }
            reports[index] = Some(report);
        }
        if !workers.0.is_empty() {
            thread::sleep(POLL_INTERVAL);
        }
    }
    let reports: Option<Vec<_>> = reports.into_iter().collect();
    combine(&reports.ok_or("missing worker result")?)
}

fn finish(worker: Worker) -> Result<(usize, ShardReport), String> {
    let Worker {
        index,
        mut child,
        output,
        stderr,
        ..
    } = worker;
    let status = child.wait().map_err(|e| e.to_string())?;
    let output = output
        .join()
        .map_err(|_| "worker output reader panicked")?
        .map_err(|e| e.to_string())?;
    stderr
        .join()
        .map_err(|_| "worker stderr reader panicked")?
        .map_err(|e| e.to_string())?;
    if !status.success() {
        return Err(format!(
            "worker {index} failed ({status}): {}",
            String::from_utf8_lossy(&output).trim()
        ));
    }
    match serde_json::from_slice(&output) {
        Ok(Report::ShardChecked(report)) => Ok((index, report)),
        Ok(_) => Err(format!("unexpected result from worker {index}")),
        Err(e) => Err(format!("invalid result from worker {index}: {e}")),
    }
}

fn spawn(
    executable: &Path,
    path: &str,
    index: usize,
    jobs: usize,
    progress: bool,
    trace_requested: bool,
) -> Result<Worker, String> {
    let mut command = Command::new(executable);
    if progress {
        command.env(TRACE_VAR, "1");
    }
    let mut child = command
        .args([
            "--export-shard",
            path,
            &index.to_string(),
            &jobs.to_string(),
        ])
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|e| format!("cannot start worker {index}: {e}"))?;
    let mut stdout = child.stdout.take().expect("piped worker output");
    let output = thread::spawn(move || {
        let mut bytes = Vec::new();
        // Drain concurrently so children never block on a full stdout pipe.
        stdout.by_ref().take(OUTPUT_LIMIT).read_to_end(&mut bytes)?;
        io::copy(&mut stdout, &mut io::sink())?;
        Ok(bytes)
    });
    let stderr = child.stderr.take().expect("piped worker stderr");
    let snapshot = Arc::new(Mutex::new(None));
    let snapshot_writer = snapshot.clone();
    let stderr = thread::spawn(move || {
        for line in BufReader::new(stderr).lines() {
            let line = line?;
            let update = if progress {
                snapshot_from_trace(&line)
            } else {
                None
            };
            let is_trace = update.is_some();
            if let Some(update) = update {
                *snapshot_writer
                    .lock()
                    .unwrap_or_else(PoisonError::into_inner) = Some(update);
            }
            if !progress || trace_requested || !is_trace {
                eprintln!("{line}");
            }
        }
        Ok(())
    });
    Ok(Worker {
        index,
        child,
        output,
        stderr,
        progress: snapshot,
    })
}

fn snapshot_from_trace(line: &str) -> Option<Snapshot> {
    let event: Trace = serde_json::from_str(line).ok()?;
    let name = event.name.as_deref()?;
    let name = serde_json::from_str::<Vec<Value>>(name)
        .ok()
        .map(|parts| {
            parts
                .iter()
                .map(|p| {
                    p.as_str()
                        .map(str::to_owned)
                        .unwrap_or_else(|| p.to_string())
                })
                .collect::<Vec<_>>()
                .join(".")
        })
        .unwrap_or_else(|| name.to_owned());
    Some(Snapshot {
        imported: event.imported as u64,
        assigned: event.assigned_checked as u64,
        name,
    })
}

#[cfg(target_os = "macos")]
fn memory_bytes(pid: u32) -> io::Result<u64> {
    let mut usage = std::mem::MaybeUninit::<libc::rusage_info_v0>::uninit();
    // SAFETY: the buffer has the size/layout required by RUSAGE_INFO_V0 and
    // is read only after libproc reports that it initialized it successfully.
    let result = unsafe {
        libc::proc_pid_rusage(
            pid as libc::c_int,
            libc::RUSAGE_INFO_V0,
            usage.as_mut_ptr().cast(),
        )
    };
    if result != 0 {
        return Err(io::Error::last_os_error());
    }
    Ok(unsafe { usage.assume_init() }.ri_phys_footprint)
}

#[cfg(target_os = "linux")]
fn memory_bytes(pid: u32) -> io::Result<u64> {
    let status = std::fs::read_to_string(format!("/proc/{pid}/status"))?;
    let mut total = 0;
    for line in status.lines() {
        if line.starts_with("VmRSS:") || line.starts_with("VmSwap:") {
            let kib = line
                .split_whitespace()
                .nth(1)
                .and_then(|n| n.parse::<u64>().ok())
                .ok_or_else(|| io::Error::other("invalid process memory counter"))?;
            total += kib * 1024;
        }
    }
    Ok(total)
}

#[cfg(not(any(target_os = "macos", target_os = "linux")))]
fn memory_bytes(_: u32) -> io::Result<u64> {
    Err(io::Error::other(
        "parallel memory monitoring requires macOS or Linux",
    ))
}

fn combine(reports: &[ShardReport]) -> Result<(ExportReport, String), String> {
    let first = reports.first().ok_or("no worker results")?;
    let digest = &first.sha256;
    if digest.len() != 64 || !digest.bytes().all(|c| c.is_ascii_hexdigit()) {
        return Err("invalid input digest".into());
    }
    let (jobs, ordinary) = (reports.len(), first.ordinary);
    for (index, report) in reports.iter().enumerate() {
        let expected = ordinary / jobs + usize::from(index < ordinary % jobs);
        if report.shard != index
            || report.workers != jobs
            || report.ordinary != ordinary
            || report.assigned != expected
            || report.sha256 != first.sha256
            || report.report != first.report
        {
            return Err(format!(
                "incomplete or inconsistent result from worker {index}"
            ));
        }
    }
    Ok((first.report.clone(), first.sha256.clone()))
}

#[cfg(test)]
mod tests {
    use super::*;
    fn reports() -> Vec<ShardReport> {
        (0..2)
            .map(|shard| ShardReport {
                shard,
                workers: 2,
                assigned: 2 - shard,
                ordinary: 3,
                sha256: "a".repeat(64),
                report: ExportReport {
                    declarations: 3,
                    expressions: 4,
                    names: 5,
                    levels: 1,
                },
            })
            .collect()
    }
    #[test]
    fn progress_distinguishes_imports_from_checked_partitions() {
        let event = r#"{"line":1,"checked":null,"imported":200,"shard":1,"assigned_checked":75,"kind":"def","name":"[\"Nat\",\"add\"]"}"#;
        let snapshot = snapshot_from_trace(event).unwrap();
        assert_eq!(snapshot.name, "Nat.add");
        assert!(status(0, 1, Some(&snapshot)).contains("200 declarations checked"));
        assert!(
            status(1, 2, Some(&snapshot))
                .contains("75 assigned declarations checked, 200 imported")
        );
        assert!(status(0, 2, None).contains("scanning export"));
        assert!(snapshot_from_trace("not a trace").is_none());
        assert_eq!(brief("x\n::error::y"), "x ::error::y");
    }

    #[test]
    fn accepts_only_complete_matching_partitions() {
        assert!(combine(&reports()).is_ok());
        assert!(combine(&reports()[..1]).is_err());
        let corruptions: [fn(&mut ShardReport); 6] = [
            |r| r.shard = 0,
            |r| r.workers = 3,
            |r| r.ordinary = 4,
            |r| r.assigned = 2,
            |r| r.sha256 = "b".repeat(64),
            |r| r.report.levels = 2,
        ];
        for corrupt in corruptions {
            let mut data = reports();
            corrupt(&mut data[1]);
            assert!(combine(&data).is_err());
        }
    }
}
