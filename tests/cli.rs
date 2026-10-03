use std::{
    io::Write,
    process::{Command, Stdio},
};

#[test]
fn example_runs_from_file() {
    let result = Command::new(env!("CARGO_BIN_EXE_nano-lean"))
        .arg(concat!(env!("CARGO_MANIFEST_DIR"), "/examples/core.ltc"))
        .output()
        .unwrap();
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
    assert!(String::from_utf8_lossy(&result.stdout).contains("equal"));
}

#[test]
fn bad_stdin_exits_nonzero_with_diagnostic() {
    let mut child = Command::new(env!("CARGO_BIN_EXE_nano-lean"))
        .arg("-")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    child
        .stdin
        .take()
        .unwrap()
        .write_all(b"check Type : Type")
        .unwrap();
    let result = child.wait_with_output().unwrap();
    assert!(!result.status.success());
    assert!(String::from_utf8_lossy(&result.stderr).contains("command 1: type mismatch"));
}

fn export_command(args: &[&str]) -> (bool, serde_json::Value) {
    let output = Command::new(env!("CARGO_BIN_EXE_nano-lean"))
        .args(args)
        .output()
        .unwrap();
    (
        output.status.success(),
        serde_json::from_slice(&output.stdout).unwrap(),
    )
}

#[test]
fn parallel_export_matches_serial_and_workers_are_partial() {
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/fixtures/theorem-reduction.ndjson"
    );
    use sha2::{Digest, Sha256};
    let digest = format!("{:x}", Sha256::digest(std::fs::read(path).unwrap()));
    let (ok, serial) = export_command(&["--export", path]);
    assert!(ok);
    for workers in ["1", "2", "3"] {
        let (ok, parallel) = export_command(&["--export-parallel", workers, path]);
        assert!(ok, "{parallel}");
        assert_eq!(parallel["status"], "checked");
        assert_eq!(parallel["sha256"], digest);
        for field in ["declarations", "expressions", "names", "levels"] {
            assert_eq!(parallel[field], serial[field]);
        }
    }
    let (ok, partial) = export_command(&["--export-shard", path, "0", "2"]);
    assert!(ok);
    assert_eq!(partial["status"], "shard_checked");
    assert!(partial["report"].get("status").is_none());
    for args in [
        vec!["--export-parallel", "0", path],
        vec!["--export-shard", path, "2", "2"],
        vec!["--export-parallel", "2", "/missing/nano-export.ndjson"],
    ] {
        assert!(!export_command(&args).0);
    }
}

#[test]
fn parallel_export_rejects_invalid_declarations_in_each_partition() {
    use serde_json::Value;
    let items: Vec<Value> = include_str!("fixtures/smoke.ndjson")
        .lines()
        .map(|line| serde_json::from_str(line).unwrap())
        .collect();
    let path = std::env::temp_dir().join(format!(
        "nano-parallel-invalid-{}.ndjson",
        std::process::id()
    ));
    let mut corrupted = 0;
    for index in 0..items.len() {
        if items[index].get("def").is_none() {
            continue;
        }
        let mut data = items.clone();
        data[index]["def"]["value"] = data[index]["def"]["type"].clone();
        std::fs::write(
            &path,
            data.iter()
                .map(Value::to_string)
                .collect::<Vec<_>>()
                .join("\n"),
        )
        .unwrap();
        assert!(!export_command(&["--export", path.to_str().unwrap()]).0);
        let (ok, result) = export_command(&["--export-parallel", "2", path.to_str().unwrap()]);
        assert!(!ok, "{result}");
        assert_eq!(result["status"], "rejected");
        corrupted += 1;
    }
    assert!(corrupted >= 2);
    std::fs::remove_file(path).unwrap();
}

#[test]
fn parallel_memory_budget_stops_workers() {
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/fixtures/smoke.ndjson");
    let (ok, result) = export_command(&["--export-parallel", "2", "--memory-mib", "1", path]);
    assert!(!ok);
    assert!(
        result["reason"]
            .as_str()
            .unwrap()
            .contains("memory budget exceeded"),
        "{result}"
    );
    assert!(!export_command(&["--export-parallel", "2", "--memory-mib", "0", path]).0);
}
