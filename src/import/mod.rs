pub mod blean;
mod importer;
mod json;
mod prelude;
mod primitives;
mod scan;

use crate::export::ExportError;
use crate::term::FxHashMap;
use crate::term::arena::Arena;
use crate::term::decl::Declar;
use crate::term::intern::Store;
use importer::Importer;
use scan::Batch;
use std::fs::File;
use std::io::{self, Read};
use std::os::unix::fs::FileExt;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering::Relaxed};
use std::sync::{Condvar, Mutex, PoisonError};
use std::thread;

type Result<T> = std::result::Result<T, ExportError>;

fn invalid<T>(s: impl Into<String>) -> Result<T> {
    Err(ExportError::Invalid(s.into()))
}

fn unsupported<T>(s: impl Into<String>) -> Result<T> {
    Err(ExportError::Unsupported(s.into()))
}

pub fn import<'a>(arena: &'a Arena, path: impl AsRef<Path>) -> Result<Store<'a>> {
    import_with(arena, path, 1)
}

/// Like `import`, but an ndjson file is scanned by `threads - 1` helpers while this thread builds.
pub fn import_with<'a>(
    arena: &'a Arena,
    path: impl AsRef<Path>,
    threads: usize,
) -> Result<Store<'a>> {
    let file = File::open(path)?;
    let len = file.metadata()?.len() as usize;
    if let Some(map) = blean::map(&file)? {
        let im = blean::read(arena, &map)?;
        // The records are consumed, so unmap before the fill peaks.
        drop(map);
        return im.finish();
    }
    if threads > 1 && len > 2 * PAR_CHUNK {
        return import_lines(arena, &file, len, threads - 1, PAR_CHUNK);
    }
    import_reader(arena, file, len)
}

const PAR_CHUNK: usize = 4 << 20;

struct Ready {
    batches: FxHashMap<usize, Batch>,
    spent: Vec<Batch>,
    consumed: usize,
    closed: bool,
}

/// Scanners take chunks in any order and park them, at most `ahead` past the builder.
struct Pipe {
    ready: Mutex<Ready>,
    filled: Condvar,
    drained: Condvar,
    ahead: usize,
}

impl Pipe {
    fn put(&self, k: usize, b: Batch) -> bool {
        let mut r = self.ready.lock().unwrap_or_else(PoisonError::into_inner);
        while k >= r.consumed + self.ahead && !r.closed {
            r = self.drained.wait(r).unwrap_or_else(PoisonError::into_inner);
        }
        r.batches.insert(k, b);
        self.filled.notify_one();
        !r.closed
    }

    fn take(&self, k: usize) -> Batch {
        let mut r = self.ready.lock().unwrap_or_else(PoisonError::into_inner);
        let b = loop {
            match r.batches.remove(&k) {
                Some(b) => break b,
                None => r = self.filled.wait(r).unwrap_or_else(PoisonError::into_inner),
            }
        };
        r.consumed = k + 1;
        self.drained.notify_all();
        b
    }

    fn spare(&self) -> Batch {
        let mut r = self.ready.lock().unwrap_or_else(PoisonError::into_inner);
        r.spent.pop().unwrap_or_default()
    }

    fn give(&self, b: Batch) {
        let mut r = self.ready.lock().unwrap_or_else(PoisonError::into_inner);
        r.spent.push(b);
    }

    fn close(&self) {
        self.ready
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .closed = true;
        self.drained.notify_all();
    }
}

/// Scanners read and scan fixed chunks with positioned reads, this thread builds in order.
fn import_lines<'a>(
    arena: &'a Arena,
    file: &File,
    len: usize,
    scanners: usize,
    chunk: usize,
) -> Result<Store<'a>> {
    let chunks = len.div_ceil(chunk);
    let pipe = Pipe {
        ready: Mutex::new(Ready {
            batches: FxHashMap::default(),
            spent: Vec::new(),
            consumed: 0,
            closed: false,
        }),
        filled: Condvar::new(),
        drained: Condvar::new(),
        ahead: 4 * scanners,
    };
    let next = AtomicUsize::new(0);
    let failed = Mutex::new(None);
    let mut im = Importer::new(arena, len);
    let mut carry = Vec::new();
    let n = thread::scope(|s| {
        for _ in 0..scanners {
            s.spawn(|| {
                loop {
                    let k = next.fetch_add(1, Relaxed);
                    if k >= chunks {
                        break;
                    }
                    let at = k * chunk;
                    let mut b = pipe.spare();
                    b.buf.resize(chunk.min(len - at), 0);
                    if let Err(e) = file.read_exact_at(&mut b.buf, at as u64) {
                        *failed.lock().unwrap_or_else(PoisonError::into_inner) = Some(e);
                        b.buf.clear();
                    }
                    b.scan();
                    if !pipe.put(k, b) {
                        break;
                    }
                }
            });
        }
        let mut n = 0;
        let r = (0..chunks).try_for_each(|k| {
            let b = pipe.take(k);
            if let Some(e) = failed.lock().unwrap_or_else(PoisonError::into_inner).take() {
                return Err(e.into());
            }
            im.batch(&b, &mut carry, &mut n)?;
            pipe.give(b);
            Ok(())
        });
        pipe.close();
        r.and_then(|()| im.raw_line(&carry, carry.len(), &mut n))
            .map(|()| n)
    })?;
    im.finish_lines(n)
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
    let env = olean_export::Env::load(search, roots)
        .map_err(|e| ExportError::Invalid(format!("olean: {e}")))?;
    from_env(arena, &env)
}

/// Exports every constant of `env` straight into a store.
pub fn from_env<'a>(arena: &'a Arena, env: &olean_export::Env) -> Result<Store<'a>> {
    let mut sink = blean::Records::new(arena, env.names.len() + env.levels.len() + env.exprs.len());
    let mut ex = olean_export::Exporter::with_sink(env, &mut sink);
    let out = ex.meta().and_then(|()| ex.all()).and_then(|()| ex.finish());
    if let Err(e) = out {
        sink.fail(ExportError::Invalid(format!("olean: {e}")));
    }
    sink.finish()
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::term::expr::Expr;
    use crate::term::level::Level;
    use crate::term::ptr::{ExprPtr, LevelPtr};
    use std::hash::{Hash, Hasher};
    use std::io::Write;

    fn level(l: LevelPtr<'_>) -> String {
        match *l.as_ref() {
            Level::Zero => "0".into(),
            Level::Succ(a, _) => format!("s({})", level(a)),
            Level::Max(a, b, _) => format!("max({},{})", level(a), level(b)),
            Level::IMax(a, b, _) => format!("imax({},{})", level(a), level(b)),
            Level::Param(n, _) => n.to_string(),
        }
    }

    /// A structural fingerprint, since stored hashes depend on addresses.
    fn shape<'a>(e: ExprPtr<'a>, memo: &mut FxHashMap<ExprPtr<'a>, u64>) -> u64 {
        if let Some(&h) = memo.get(&e) {
            return h;
        }
        let mut s = std::hash::DefaultHasher::new();
        match *e.as_ref() {
            Expr::Var { idx, .. } => (0, idx).hash(&mut s),
            Expr::Sort { level: l, .. } => (1, level(l)).hash(&mut s),
            Expr::Const { name, levels, .. } => {
                let ls: Vec<_> = levels.iter().map(|&l| level(l)).collect();
                (2, name.to_string(), ls).hash(&mut s);
            }
            Expr::App { fun, arg, .. } => (3, shape(fun, memo), shape(arg, memo)).hash(&mut s),
            Expr::Lam { ty, body, .. } => (4, shape(ty, memo), shape(body, memo)).hash(&mut s),
            Expr::Pi { ty, body, .. } => (5, shape(ty, memo), shape(body, memo)).hash(&mut s),
            Expr::Let { data: d, .. } => {
                let parts = [d.ty, d.val, d.body].map(|x| shape(x, memo));
                (6, parts, d.nondep).hash(&mut s);
            }
            Expr::Proj { name, idx, e, .. } => {
                (7, name.to_string(), idx, shape(e, memo)).hash(&mut s);
            }
            Expr::NatLit { n, .. } => (8, n.as_ref().to_string()).hash(&mut s),
            Expr::StrLit { s: x, .. } => (9, x.as_ref().s).hash(&mut s),
            Expr::Local { .. } => unreachable!("exports have no locals"),
        }
        let h = s.finish();
        memo.insert(e, h);
        h
    }

    fn summary(r: Result<Store<'_>>) -> String {
        let mut memo = FxHashMap::default();
        match r {
            Ok(s) => {
                let decls: Vec<_> = s
                    .declars
                    .iter()
                    .map(|d| (d.name().to_string(), shape(d.ty(), &mut memo)))
                    .collect();
                format!("{:?} {decls:?}", s.stats)
            }
            Err(e) => e.to_string(),
        }
    }

    fn agree(bytes: &[u8], chunks: &[usize]) {
        let mut f = tempfile::NamedTempFile::new().unwrap();
        f.write_all(bytes).unwrap();
        let arena = Arena::new();
        let want = summary(import_reader(&arena, bytes, bytes.len()));
        for &chunk in chunks {
            for scanners in 1..=3 {
                let (arena, file) = (Arena::new(), File::open(f.path()).unwrap());
                let got = import_lines(&arena, &file, bytes.len(), scanners, chunk);
                assert_eq!(summary(got), want, "chunk {chunk} scanners {scanners}");
            }
        }
    }

    #[test]
    fn chunked_scan_matches_sequential_reader() {
        let large = include_bytes!("../../tests/fixtures/let/nat-let-fold.ndjson");
        agree(large, &[4096, 65536]);
        let small = include_bytes!("../../tests/fixtures/neutral.ndjson");
        agree(small, &[1, 7, 100, 1 << 20]);
        let mut cut = small.to_vec();
        let mid = cut.len() / 2;
        cut[mid..].iter_mut().take(40).for_each(|b| *b = b'x');
        agree(&cut, &[7, 100]);
        agree(&small[..small.len() - 1], &[13]);
    }
}
