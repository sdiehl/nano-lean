#![allow(clippy::unwrap_used, clippy::panic)]

use nano_lean::cache::Cache;
use nano_lean::import;
use nano_lean::term::arena::Arena;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

const FIXTURES: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/fixtures");

const BASE: &str = "\
inductive Nat : Type
  | Nat.zero : Nat
  | Nat.succ : Nat -> Nat
def a : Nat := Nat.zero
def b : Nat := Nat.succ a
def c : Nat := Nat.zero
def d : Nat := Nat.succ b
";

fn nl_fast(cache: &Path, args: &[&str], export: &Path) -> Output {
    Command::new(env!("CARGO_BIN_EXE_nl-fast"))
        .arg("--cache")
        .arg(cache)
        .args(args)
        .arg(export)
        .output()
        .unwrap()
}

fn hits(out: &Output) -> usize {
    let err = String::from_utf8_lossy(&out.stderr);
    let line = err.lines().find(|l| l.ends_with("recorded")).unwrap();
    line.split(' ').nth(1).unwrap().parse().unwrap()
}

fn emit(dir: &Path, name: &str, source: &str) -> PathBuf {
    let ltc = dir.join(format!("{name}.ltc"));
    std::fs::write(&ltc, source).unwrap();
    let out = Command::new(env!("CARGO_BIN_EXE_nl-ref"))
        .arg("--emit")
        .arg(&ltc)
        .output()
        .unwrap();
    assert!(out.status.success(), "{out:?}");
    let path = dir.join(format!("{name}.ndjson"));
    std::fs::write(&path, out.stdout).unwrap();
    path
}

#[test]
fn rerun_hits_and_edits_invalidate_dependents_only() {
    let dir = tempfile::tempdir().unwrap();
    let cache = dir.path().join("accepted.bin");
    let base = emit(dir.path(), "base", BASE);
    let cold = nl_fast(&cache, &[], &base);
    assert!(cold.status.success(), "{cold:?}");
    assert_eq!(hits(&cold), 0);
    let warm = nl_fast(&cache, &[], &base);
    assert_eq!(hits(&warm), 4);
    assert_eq!(cold.stdout, warm.stdout);
    let edited = emit(
        dir.path(),
        "edited",
        &BASE.replace(
            "def a : Nat := Nat.zero",
            "def a : Nat := Nat.succ Nat.zero",
        ),
    );
    assert_eq!(hits(&nl_fast(&cache, &[], &edited)), 1);
}

#[test]
fn keys_match_across_ndjson_and_blean() {
    let dir = tempfile::tempdir().unwrap();
    let cache = dir.path().join("accepted.bin");
    nl_fast(&cache, &[], Path::new(&format!("{FIXTURES}/nested.ndjson")));
    let blean = nl_fast(
        &cache,
        &[],
        Path::new(&format!("{FIXTURES}/blean/nested.blean")),
    );
    assert!(blean.status.success(), "{blean:?}");
    assert_eq!(hits(&blean), 17);
}

#[test]
fn forged_primitive_misses_the_honest_cache() {
    let dir = tempfile::tempdir().unwrap();
    let cache = dir.path().join("accepted.bin");
    let honest = PathBuf::from(format!("{FIXTURES}/prelude/nat-add.ndjson"));
    nl_fast(&cache, &[], &honest);
    assert!(hits(&nl_fast(&cache, &[], &honest)) > 0);
    let forged = nl_fast(
        &cache,
        &[],
        Path::new(&format!("{FIXTURES}/forged-nat-add.ndjson")),
    );
    assert_eq!(hits(&forged), 0);
}

#[test]
fn corrupt_cache_is_ignored_and_rewritten() {
    let dir = tempfile::tempdir().unwrap();
    let cache = dir.path().join("accepted.bin");
    let base = emit(dir.path(), "base", BASE);
    std::fs::write(&cache, b"NLCACHE1 not a cache").unwrap();
    let out = nl_fast(&cache, &[], &base);
    assert!(out.status.success(), "{out:?}");
    assert_eq!(hits(&out), 0);
    assert_eq!(hits(&nl_fast(&cache, &[], &base)), 4);
}

/// A recorded key is trusted, so only an audit catches one for a rejected declaration.
#[test]
fn audit_catches_a_recorded_rejection() {
    let dir = tempfile::tempdir().unwrap();
    let cache = dir.path().join("accepted.bin");
    let bad = emit(
        dir.path(),
        "bad",
        &format!("{BASE}def bad : Nat := Nat.succ\n"),
    );
    {
        let arena = Arena::new();
        let store = import::import(&arena, &bad).unwrap();
        let idx = (0..store.declars.len() as u32)
            .find(|&i| store.declars[i as usize].name().to_string() == "bad")
            .unwrap();
        let c = Cache::open(&store, &cache, "value", false)
            .unwrap()
            .unwrap();
        c.record(&[c.lookup(idx).0.unwrap()]);
        c.save(&cache, true).unwrap();
    }
    assert!(nl_fast(&cache, &[], &bad).status.success());
    let audit = nl_fast(&cache, &["--cache-audit"], &bad);
    assert_eq!(audit.status.code(), Some(1), "{audit:?}");
    assert!(
        String::from_utf8_lossy(&audit.stdout).contains("cache audit: bad is recorded as accepted")
    );
}

#[test]
fn config_enables_and_no_cache_overrides() {
    let dir = tempfile::tempdir().unwrap();
    let config = dir.path().join("nano-lean.toml");
    std::fs::write(&config, "cache = \"accepted.bin\"\n").unwrap();
    let base = emit(dir.path(), "base", BASE);
    let run = |extra: &[&str]| {
        Command::new(env!("CARGO_BIN_EXE_nl-fast"))
            .arg("--config")
            .arg(&config)
            .args(extra)
            .arg(&base)
            .output()
            .unwrap()
    };
    run(&[]);
    assert_eq!(hits(&run(&[])), 4);
    let off = run(&["--no-cache"]);
    assert!(off.status.success(), "{off:?}");
    assert!(!String::from_utf8_lossy(&off.stderr).contains("recorded"));
}
