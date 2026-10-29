pub mod blean;
mod importer;
mod json;
mod prelude;
mod primitives;
mod scan;

use crate::export::ExportError;
use crate::term::arena::Arena;
use crate::term::decl::Declar;
use crate::term::intern::Store;
use importer::Importer;
use std::fs::File;
use std::io::{self, Read};
use std::path::{Path, PathBuf};

type Result<T> = std::result::Result<T, ExportError>;

fn invalid<T>(s: impl Into<String>) -> Result<T> {
    Err(ExportError::Invalid(s.into()))
}

fn unsupported<T>(s: impl Into<String>) -> Result<T> {
    Err(ExportError::Unsupported(s.into()))
}

pub fn import<'a>(arena: &'a Arena, path: impl AsRef<Path>) -> Result<Store<'a>> {
    let file = File::open(path)?;
    let len = file.metadata()?.len() as usize;
    if let Some(map) = blean::map(&file)? {
        let im = blean::read(arena, &map)?;
        // The records are consumed, so unmap before the fill peaks.
        drop(map);
        return im.finish();
    }
    import_reader(arena, file, len)
}

const CHUNK: usize = 16 << 20;

pub fn import_reader<'a>(arena: &'a Arena, mut r: impl Read, len: usize) -> Result<Store<'a>> {
    let mut im = Importer::new(arena, len);
    let mut buf = vec![0u8; CHUNK];
    let (mut filled, mut n) = (0, 0);
    loop {
        if filled == buf.len() {
            buf.resize(2 * buf.len(), 0);
        }
        let k = match r.read(&mut buf[filled..]) {
            Err(e) if e.kind() == io::ErrorKind::Interrupted => continue,
            k => k?,
        };
        filled += k;
        let end = if k == 0 {
            filled
        } else {
            match memchr::memrchr(b'\n', &buf[..filled]) {
                Some(p) => p + 1,
                None => continue,
            }
        };
        im.lines(&buf[..end], &mut n)?;
        buf.copy_within(end..filled, 0);
        filled -= end;
        if k == 0 {
            break;
        }
    }
    im.finish_lines(n)
}

pub fn import_bytes<'a>(arena: &'a Arena, bytes: &[u8]) -> Result<Store<'a>> {
    if blean::sniff(bytes) {
        return blean::import(arena, bytes);
    }
    let mut im = Importer::new(arena, bytes.len());
    let mut n = 0;
    im.lines(bytes, &mut n)?;
    im.finish_lines(n)
}

/// Loads `roots` and their imports from `.olean` files on `search`, as a blean export would.
pub fn olean<'a>(arena: &'a Arena, search: &[PathBuf], roots: &[&str]) -> Result<Store<'a>> {
    use olean_export::{Env, Exporter, blean::Blean};
    let olean = |e: olean_export::Error| ExportError::Invalid(format!("olean: {e}"));
    let env = Env::load(search, roots).map_err(olean)?;
    let mut ex = Exporter::with_sink(&env, Blean::new(Vec::new()));
    ex.meta().map_err(olean)?;
    ex.all().map_err(olean)?;
    let bytes = ex.finish().map_err(olean)?;
    drop(env);
    blean::import(arena, &bytes)
}

/// Rejects `target` unless every declaration the checkers reduce by name matches `reference`.
pub fn check_prelude(target: &Store<'_>, reference: &Store<'_>) -> Result<()> {
    prelude::compare(target, reference)
}

/// Rejects `store` if it declares an axiom outside `permitted`.
pub fn check_axioms(store: &Store<'_>, permitted: &[String]) -> Result<()> {
    for d in &store.declars {
        if let Declar::Axiom(i) = d {
            let name = i.name.to_string();
            if !permitted.contains(&name) {
                return invalid(format!("axiom {name} is not permitted"));
            }
        }
    }
    Ok(())
}
