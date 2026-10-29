//! An opt-in record of accepted declarations, keyed by content, so a rerun skips them. The file
//! is trusted input like the export: a key in it is taken as an accepted declaration.
//!
//! Layout: `MAGIC`, a 32-byte tag over the checker build, core and environment, then sorted
//! 32-byte keys. A file with another tag is ignored.

mod key;

use crate::term::intern::Store;
use key::Keys;
use memmap2::Mmap;
use std::fs::{self, File};
use std::io::{self, Write};
use std::path::Path;
use std::sync::Mutex;
use std::sync::atomic::{AtomicUsize, Ordering::Relaxed};

pub type Key = [u8; 32];

const MAGIC: &[u8; 8] = b"NLCACHE1";
const HEADER: usize = MAGIC.len() + 32;
const BUILD: &str = concat!(env!("CARGO_PKG_VERSION"), " ", env!("NL_SOURCE_HASH"));

pub struct Cache<'a> {
    keys: Keys<'a>,
    tag: Key,
    map: Option<Mmap>,
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
                let ok = m.len() >= HEADER
                    && (m.len() - HEADER).is_multiple_of(32)
                    && m[..MAGIC.len()] == *MAGIC
                    && m[MAGIC.len()..HEADER] == tag;
                ok.then_some(m)
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
            .as_deref()
            .map_or(&[], |m| m[HEADER..].as_chunks().0)
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

    /// Writes the accepted keys, plus every stored key when `keep` is set, and replaces the file.
    /// Returns how many it wrote.
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
        if let Some(dir) = path.parent().filter(|d| !d.as_os_str().is_empty()) {
            fs::create_dir_all(dir)?;
        }
        let tmp = path.with_extension(format!("tmp.{}", std::process::id()));
        let mut f = io::BufWriter::new(File::create(&tmp)?);
        f.write_all(MAGIC)?;
        f.write_all(&self.tag)?;
        for k in &accepted {
            f.write_all(k)?;
        }
        f.into_inner()
            .map_err(io::IntoInnerError::into_error)?
            .sync_all()?;
        fs::rename(&tmp, path)?;
        Ok(accepted.len())
    }
}
