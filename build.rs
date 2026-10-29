fn main() -> Result<(), Box<dyn std::error::Error>> {
    source_hash()?;
    lalrpop::process_root()
}

/// Every source and setting that can change a verdict, so a cache never outlives a checker change.
fn source_hash() -> Result<(), Box<dyn std::error::Error>> {
    use std::path::{Path, PathBuf};
    fn walk(dir: &Path, out: &mut Vec<PathBuf>) -> std::io::Result<()> {
        for e in std::fs::read_dir(dir)? {
            let p = e?.path();
            if p.is_dir() {
                walk(&p, out)?;
            } else {
                out.push(p);
            }
        }
        Ok(())
    }
    let mut files = vec![];
    walk(Path::new("src"), &mut files)?;
    files.sort();
    let mut h = blake3::Hasher::new();
    for f in files
        .iter()
        .map(PathBuf::as_path)
        .chain(["Cargo.toml", "Cargo.lock", "build.rs", ".cargo/config.toml"].map(Path::new))
    {
        println!("cargo:rerun-if-changed={}", f.display());
        h.update(f.to_string_lossy().as_bytes());
        h.update(&std::fs::read(f).unwrap_or_default());
    }
    let rustc = std::env::var("RUSTC").unwrap_or_else(|_| "rustc".into());
    h.update(
        &std::process::Command::new(rustc)
            .arg("-vV")
            .output()?
            .stdout,
    );
    println!("cargo:rerun-if-changed=src");
    println!("cargo:rustc-env=NL_SOURCE_HASH={}", h.finalize().to_hex());
    Ok(())
}
