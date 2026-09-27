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
