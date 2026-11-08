//! An opt-in record of accepted declarations, keyed by content, so a rerun skips them. The file
//! is trusted input like the export: a key in it is taken as an accepted declaration.
//!
//! The file is an olean-export accepted store, which other checkers may share. Our section is
//! named `CHECKER` and tagged over the build, core and environment; a section with another
//! tag is ignored, and other checkers' sections are kept.

mod key;

use crate::term::intern::Store;
use key::Keys;
use memmap2::Mmap;
use olean_export::accepted::{self, Section};
use std::fs::{self, File};
use std::io;
use std::ops::Range;
use std::path::Path;
use std::sync::Mutex;
use std::sync::atomic::{AtomicUsize, Ordering::Relaxed};

pub type Key = [u8; 32];

const MAGIC: &[u8; 8] = b"NLCACHE1";
const CHECKER: &str = "nano-lean";
const BUILD: &str = concat!(env!("CARGO_PKG_VERSION"), " ", env!("NL_SOURCE_HASH"));

pub struct Cache<'a> {
    keys: Keys<'a>,
    tag: Key,
    map: Option<(Mmap, Range<usize>)>,
    pub audit: bool,
    pub hits: AtomicUsize,
    accepted: Mutex<Vec<Key>>,
}

impl<'a> Cache<'a> {
    /// `None` when a primitive cannot be keyed, so no declaration can be.
    pub fn open(
        store: &'a Store<'a>,
        path: &Path,
        core: &str,
        audit: bool,
    ) -> io::Result<Option<Self>> {
        let keys = Keys::new(store);
        let Some(env) = keys.environment() else {
            return Ok(None);
        };
        let tag = *blake3::Hasher::new()
            .update(MAGIC)
            .update(BUILD.as_bytes())
            .update(core.as_bytes())
            .update(&env)
            .finalize()
            .as_bytes();
        let map = match File::open(path) {
            Ok(f) => {
                // SAFETY: writers replace the file by rename, so the mapped inode never changes.
                let m = unsafe { Mmap::map(&f)? };
                let keys = ours(&m, &tag).map(|keys| {
                    let start = keys.as_ptr() as usize - m.as_ptr() as usize;
                    start..start + keys.len() * 32
                });
                keys.map(|r| (m, r))
            }
            Err(e) if e.kind() == io::ErrorKind::NotFound => None,
            Err(e) => return Err(e),
        };
        Ok(Some(Cache {
            keys,
            tag,
            map,
            audit,
            hits: AtomicUsize::new(0),
            accepted: Mutex::default(),
        }))
    }

    fn stored(&self) -> &[Key] {
        self.map
            .as_ref()
            .map_or(&[], |(m, r)| m[r.clone()].as_chunks().0)
    }

    /// The declaration's key, and whether the file records it. A key outside the stored ones
    /// never matches, whatever their order.
    pub fn lookup(&self, idx: u32) -> (Option<Key>, bool) {
        let k = self.keys.get(idx);
        let hit = k.is_some_and(|k| self.stored().binary_search(&k).is_ok());
        if hit {
            self.hits.fetch_add(1, Relaxed);
        }
        (k, hit)
    }

    pub fn record(&self, keys: &[Key]) {
        self.accepted
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .extend_from_slice(keys);
    }

    /// Writes the accepted keys, plus every stored key when `keep` is set, as our section, keeps
    /// the other checkers' sections, and replaces the file. Returns how many keys it wrote.
    pub fn save(&self, path: &Path, keep: bool) -> io::Result<usize> {
        let mut accepted = std::mem::take(
            &mut *self
                .accepted
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner),
        );
        if keep {
            accepted.extend_from_slice(self.stored());
        }
        accepted.sort_unstable();
        accepted.dedup();
        let old = match fs::read(path) {
            Ok(b) => b,
            Err(e) if e.kind() == io::ErrorKind::NotFound => Vec::new(),
            Err(e) => return Err(e),
        };
        let mut sections: Vec<Section<'_>> = accepted::parse(&old)
            .unwrap_or_default()
            .into_iter()
            .filter(|s| s.checker != CHECKER)
            .collect();
        sections.push(Section {
            checker: CHECKER,
            tag: self.tag,
            keys: &accepted,
        });
        accepted::save(path, &sections)?;
        Ok(accepted.len())
    }
}

/// Our section's keys, if the file is a store and our section carries `tag`.
fn ours<'m>(bytes: &'m [u8], tag: &Key) -> Option<&'m [Key]> {
    accepted::parse(bytes)
        .ok()?
        .into_iter()
        .find(|s| s.checker == CHECKER && s.tag == *tag)
        .map(|s| s.keys)
}
