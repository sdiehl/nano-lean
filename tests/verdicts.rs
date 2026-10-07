//! Every export fixture, and every core script emitted as an export, must
//! get the same verdict from all checkers, matching its `.verdict` file. Run
//! with `BLESS=1` to regenerate.

use nano_lean::{checker::Limits, emit, parser, verdict};
use std::{
    fs,
    path::{Path, PathBuf},
};

fn sources(dir: &str, extension: &str) -> Vec<PathBuf> {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join(dir);
    let mut paths: Vec<_> = fs::read_dir(dir)
        .unwrap()
        .map(|e| e.unwrap().path())
        .filter(|p| p.extension().is_some_and(|x| x == extension))
        .collect();
    paths.sort();
    assert!(!paths.is_empty());
    paths
}

fn export(path: &Path) -> String {
    let source = fs::read_to_string(path).unwrap();
    if path.extension().is_some_and(|x| x == "ltc") {
        emit::ndjson(&parser::declarations(&source).unwrap()).unwrap()
    } else {
        source
    }
}

#[test]
fn checkers_agree_with_golden_verdicts() {
    let bless = std::env::var_os("BLESS").is_some();
    let mut failed = Vec::new();
    let paths = sources("tests/fixtures", "ndjson")
        .into_iter()
        .chain(sources("tests/fixtures/core", "ltc"));
    for path in paths {
        let verdicts = verdict::check(&export(&path), Limits::default());
        let actual = verdicts.to_string();
        let golden = path.with_extension("verdict");
        if !verdicts.agree() {
            eprintln!("--- {} disagrees\n{actual}", path.display());
            failed.push(path);
        } else if bless {
            fs::write(&golden, &actual).unwrap();
        } else if fs::read_to_string(&golden).ok().as_deref() != Some(&actual) {
            eprintln!("--- {}\n{actual}", golden.display());
            failed.push(golden);
        }
    }
    assert!(
        failed.is_empty(),
        "verdict mismatch (BLESS=1 to update): {failed:?}"
    );
}
