//! Process workers keep the Rc-based kernel local to each process. A worker's
//! assumptions are discharged only when all partitions accept the same export.
use serde_json::{Value, json};
use std::{
    io::{self, Read},
    process::{Child, Command, Stdio},
    thread,
    time::Duration,
};

type Output = thread::JoinHandle<io::Result<Vec<u8>>>;
struct Workers(Vec<(usize, Child, Output)>);
impl Drop for Workers {
    fn drop(&mut self) {
        for (_, child, _) in &mut self.0 {
            let _ = child.kill();
            let _ = child.wait();
        }
    }
}

pub fn run(path: &str, jobs: usize, memory_mib: usize) -> Result<Value, String> {
    if !(1..=64).contains(&jobs) {
        return Err("worker count must be between 1 and 64".into());
    }
    let budget = memory_mib
        .checked_mul(1024 * 1024)
        .filter(|&n| n > 0)
        .ok_or("memory budget must be a positive number of MiB")? as u64;
    // Refuse to start unmonitored workers on unsupported platforms.
    memory_bytes(std::process::id()).map_err(|e| format!("cannot monitor memory: {e}"))?;
    let executable = std::env::current_exe().map_err(|e| e.to_string())?;
    let mut workers = Workers(Vec::new());
    for index in 0..jobs {
        let mut child = Command::new(&executable)
            .args([
                "--export-shard",
                path,
                &index.to_string(),
                &jobs.to_string(),
            ])
            .stdin(Stdio::null())
            .stdout(Stdio::piped())
            .stderr(Stdio::inherit())
            .spawn()
            .map_err(|e| format!("cannot start worker {index}: {e}"))?;
        let mut stdout = child.stdout.take().expect("piped worker output");
        let output = thread::spawn(move || {
            let mut bytes = Vec::new();
            // Drain concurrently, including long diagnostic output, so children
            // cannot block on a full stdout pipe while the parent polls exit.
            stdout.by_ref().take(1024 * 1024).read_to_end(&mut bytes)?;
            io::copy(&mut stdout, &mut io::sink())?;
            Ok(bytes)
        });
        workers.0.push((index, child, output));
    }
    let mut reports = vec![Value::Null; jobs];
    while !workers.0.is_empty() {
        let mut total = memory_bytes(std::process::id()).map_err(|e| e.to_string())?;
        for (_, child, _) in &mut workers.0 {
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
                total / (1024 * 1024)
            ));
        }
        let mut i = 0;
        while i < workers.0.len() {
            if workers.0[i]
                .1
                .try_wait()
                .map_err(|e| e.to_string())?
                .is_none()
            {
                i += 1;
                continue;
            }
            let (index, mut child, output) = workers.0.swap_remove(i);
            let status = child.wait().map_err(|e| e.to_string())?;
            let output = output
                .join()
                .map_err(|_| "worker output reader panicked")?
                .map_err(|e| e.to_string())?;
            if !status.success() {
                return Err(format!(
                    "worker {index} failed ({status}): {}",
                    String::from_utf8_lossy(&output).trim()
                ));
            }
            let report: Value = serde_json::from_slice(&output)
                .map_err(|e| format!("invalid result from worker {index}: {e}"))?;
            reports[index] = report;
        }
        if !workers.0.is_empty() {
            thread::sleep(Duration::from_millis(20));
        }
    }
    combine(&reports)
}

#[cfg(target_os = "macos")]
fn memory_bytes(pid: u32) -> std::io::Result<u64> {
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
        return Err(std::io::Error::last_os_error());
    }
    Ok(unsafe { usage.assume_init() }.ri_phys_footprint)
}

#[cfg(target_os = "linux")]
fn memory_bytes(pid: u32) -> std::io::Result<u64> {
    let status = std::fs::read_to_string(format!("/proc/{pid}/status"))?;
    let mut total = 0;
    for line in status.lines() {
        if line.starts_with("VmRSS:") || line.starts_with("VmSwap:") {
            let kib = line
                .split_whitespace()
                .nth(1)
                .and_then(|n| n.parse::<u64>().ok())
                .ok_or_else(|| std::io::Error::other("invalid process memory counter"))?;
            total += kib * 1024;
        }
    }
    Ok(total)
}

#[cfg(not(any(target_os = "macos", target_os = "linux")))]
fn memory_bytes(_: u32) -> std::io::Result<u64> {
    Err(std::io::Error::other(
        "parallel memory monitoring requires macOS or Linux",
    ))
}

fn combine(reports: &[Value]) -> Result<Value, String> {
    let first = reports.first().ok_or("no worker results")?;
    let ordinary = first["ordinary"]
        .as_u64()
        .ok_or("missing declaration count")?;
    let digest = first["sha256"].as_str().ok_or("missing input digest")?;
    if digest.len() != 64 || !digest.bytes().all(|c| c.is_ascii_hexdigit()) {
        return Err("invalid input digest".into());
    }
    let jobs = reports.len() as u64;
    for (index, report) in reports.iter().enumerate() {
        let expected = ordinary / jobs + u64::from((index as u64) < ordinary % jobs);
        if report["status"] != "shard_checked"
            || report["shard"].as_u64() != Some(index as u64)
            || report["workers"].as_u64() != Some(jobs)
            || report["ordinary"].as_u64() != Some(ordinary)
            || report["assigned"].as_u64() != Some(expected)
            || report["sha256"] != first["sha256"]
            || report["report"] != first["report"]
        {
            return Err(format!(
                "incomplete or inconsistent result from worker {index}"
            ));
        }
    }
    let mut result = first["report"]
        .as_object()
        .ok_or("missing export report")?
        .clone();
    for field in ["declarations", "expressions", "names", "levels"] {
        if result.get(field).and_then(Value::as_u64).is_none() {
            return Err(format!("missing report field: {field}"));
        }
    }
    result.insert("status".into(), json!("checked"));
    result.insert("workers".into(), json!(jobs));
    result.insert("sha256".into(), json!(digest));
    Ok(Value::Object(result))
}

#[cfg(test)]
mod tests {
    use super::*;
    fn reports() -> Vec<Value> {
        (0..2)
            .map(|i| {
                json!({"status":"shard_checked", "shard":i, "workers":2,
            "ordinary":3, "assigned":if i == 0 {2} else {1}, "sha256":"a".repeat(64),
            "report":{"declarations":3,"expressions":4,"names":5,"levels":1}})
            })
            .collect()
    }
    #[test]
    fn accepts_only_complete_matching_partitions() {
        assert_eq!(combine(&reports()).unwrap()["status"], "checked");
        assert!(combine(&reports()[..1]).is_err());
        for field in [
            "shard", "workers", "ordinary", "assigned", "sha256", "report", "status",
        ] {
            let mut data = reports();
            data[1][field] = Value::Null;
            assert!(combine(&data).is_err(), "{field}");
        }
    }
}
