//! Run with `BLESS=1` to regenerate the `.out` files.

#![allow(clippy::unwrap_used, clippy::panic)]

use nano_lean::{
    Environment,
    parser::{run, session},
};
use std::{fs, path::Path};

fn transcript(source: &str) -> String {
    match session(source, &mut Environment::new()) {
        Ok(results) => results
            .into_iter()
            .map(|r| r.unwrap_or_else(|e| format!("error: {e}")) + "\n")
            .collect(),
        Err(e) => format!("parse error: {e}\n"),
    }
}

#[test]
fn fixtures() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/core");
    let bless = std::env::var_os("BLESS").is_some();
    let mut scripts: Vec<_> = fs::read_dir(&dir)
        .unwrap()
        .map(|e| e.unwrap().path())
        .filter(|p| p.extension().is_some_and(|x| x == "ltc"))
        .collect();
    scripts.sort();
    assert!(!scripts.is_empty());
    let mut failed = Vec::new();
    for script in scripts {
        let source = fs::read_to_string(&script).unwrap();
        let actual = transcript(&source);
        assert_eq!(
            transcript(&source.replace('\n', "\r\n")),
            actual,
            "{} differs under CRLF",
            script.display()
        );
        let golden = script.with_extension("out");
        if bless {
            fs::write(&golden, &actual).unwrap();
        } else if fs::read_to_string(&golden).ok().as_deref() != Some(&actual) {
            eprintln!("--- {}\n{actual}", golden.display());
            failed.push(golden);
        }
    }
    assert!(
        failed.is_empty(),
        "golden mismatch (BLESS=1 to update): {failed:?}"
    );
}

#[test]
fn example_checks_cleanly() {
    run(
        include_str!("../examples/core.ltc"),
        &mut Environment::new(),
    )
    .unwrap();
}
