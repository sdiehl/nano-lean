pub mod blean;
mod importer;
mod json;
mod scan;

use crate::export::ExportError;
use crate::term::arena::Arena;
use crate::term::intern::Store;
use importer::Importer;
use std::fs::File;
use std::io::{self, Read};
use std::path::Path;

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
        return Ok(im.finish());
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
