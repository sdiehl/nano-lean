//! Blean reader. Rare metadata and declaration records are rendered as NDJSON to share its validation.

use super::importer::{BYTES_PER_LINE, Importer};
use super::{ExportError, Result, invalid};
use crate::term::arena::Arena;
use crate::term::intern::Store;
use memmap2::{Advice, Mmap};
use olean_export::{Counts, Record, Sink, blean, ndjson::Ndjson};
use serde_json::Value;
use std::fmt::Display;
use std::fs::File;
use std::io::{self, Read, Seek};

pub use olean_export::blean::{MAGIC, sniff};

/// `Record` variant indices, which postcard writes as the tag.
mod tag {
    pub const META: u32 = 0;
    pub const NAME_STR: u32 = 1;
    pub const NAME_NUM: u32 = 2;
    pub const SUCC: u32 = 3;
    pub const MAX: u32 = 4;
    pub const IMAX: u32 = 5;
    pub const PARAM: u32 = 6;
    pub const BVAR: u32 = 7;
    pub const SORT: u32 = 8;
    pub const CONST: u32 = 9;
    pub const APP: u32 = 10;
    pub const LAM: u32 = 11;
    pub const PI: u32 = 12;
    pub const LET: u32 = 13;
    pub const NAT: u32 = 14;
    pub const STR: u32 = 15;
    pub const PROJ: u32 = 16;
    pub const MDATA: u32 = 17;
    pub const DECL: u32 = 18;
    pub const END: u32 = 19;
}

const BINDERS: u32 = 4;
const INFO_HASH_BYTES: usize = 8;
const END_BYTES: usize = 12;
const VARINT_MORE: u8 = 0x80;
const VARINT_BITS: u8 = 0x7f;
const U32_BYTES: usize = 5;
const U32_LAST: u8 = 0x0f;
const U64_BYTES: usize = 10;
const U64_LAST: u8 = 0x01;

fn corrupt(e: impl Display) -> ExportError {
    ExportError::Invalid(format!("blean: {e}"))
}

fn truncated<T>() -> Result<T> {
    invalid("blean: truncated record")
}

fn line(r: &Record<'_>, buf: &mut Vec<u8>) -> Result<Value> {
    buf.clear();
    Ndjson::new(&mut *buf).record(r).map_err(corrupt)?;
    Ok(serde_json::from_slice(buf)?)
}

struct Cur<'b> {
    b: &'b [u8],
    at: usize,
}

impl<'b> Cur<'b> {
    #[inline(always)]
    fn byte(&mut self) -> Result<u8> {
        let Some(&x) = self.b.get(self.at) else {
            return truncated();
        };
        self.at += 1;
        Ok(x)
    }

    #[inline(always)]
    fn varint(&mut self, max: usize, last: u8) -> Result<u64> {
        let x = self.byte()?;
        if x & VARINT_MORE == 0 {
            return Ok(u64::from(x));
        }
        let mut v = u64::from(x & VARINT_BITS);
        for i in 1..max {
            let x = self.byte()?;
            v |= u64::from(x & VARINT_BITS) << (7 * i);
            if x & VARINT_MORE == 0 {
                if i == max - 1 && x > last {
                    break;
                }
                return Ok(v);
            }
        }
        invalid("blean: bad varint")
    }

    #[inline(always)]
    fn u32(&mut self) -> Result<u32> {
        self.varint(U32_BYTES, U32_LAST).map(|v| v as u32)
    }

    #[inline(always)]
    fn u64(&mut self) -> Result<u64> {
        self.varint(U64_BYTES, U64_LAST)
    }

    fn bool(&mut self) -> Result<bool> {
        match self.byte()? {
            0 => Ok(false),
            1 => Ok(true),
            _ => invalid("blean: bad bool"),
        }
    }

    fn take(&mut self, n: usize) -> Result<&'b [u8]> {
        let Some(s) = self.b.get(self.at..self.at.saturating_add(n)) else {
            return truncated();
        };
        self.at += n;
        Ok(s)
    }

    fn str(&mut self) -> Result<&'b str> {
        let n = self.u32()? as usize;
        let s = self.take(n)?;
        str::from_utf8(s).or_else(|_| invalid("blean: bad utf-8"))
    }

    fn binding(&mut self) -> Result<(u32, u32, u32)> {
        if self.u32()? >= BINDERS {
            return invalid("blean: bad binder");
        }
        Ok((self.u32()?, self.u32()?, self.u32()?))
    }

    fn skip_info(&mut self) -> Result<()> {
        self.take(INFO_HASH_BYTES)?;
        self.u32()?;
        self.byte()?;
        Ok(())
    }

    fn record(&mut self, start: usize) -> Result<Record<'b>> {
        let (r, rest) =
            postcard::take_from_bytes::<Record<'b>>(&self.b[start..]).map_err(corrupt)?;
        self.at = self.b.len() - rest.len();
        Ok(r)
    }
}

fn records(c: &Counts) -> usize {
    c.names as usize + c.levels as usize + c.exprs as usize
}

fn take_id(next: &mut u32) -> u32 {
    *next += 1;
    *next - 1
}

pub fn import<'a>(arena: &'a Arena, bytes: &[u8]) -> Result<Store<'a>> {
    read(arena, bytes)?.finish()
}

pub(super) fn read<'a>(arena: &'a Arena, bytes: &[u8]) -> Result<Importer<'a>> {
    let c = blean::counts(bytes).map_err(corrupt)?;
    // Every record takes at least a byte, so a damaged tail cannot ask for more than the file holds.
    let mut im = Importer::new(arena, records(&c).min(bytes.len()) * BYTES_PER_LINE);
    let mut cur = Cur {
        b: &bytes[MAGIC.len()..],
        at: 0,
    };
    let mut next = Counts::default();
    let mut us = Vec::new();
    let mut buf = Vec::new();
    for n in 0usize.. {
        let start = cur.at;
        let t = cur.u32()?;
        if n == 0 && t != tag::META {
            return invalid("missing export metadata");
        }
        let done = match t {
            tag::META if n > 0 => invalid("metadata after the first record"),
            tag::META | tag::DECL => {
                let r = cur.record(start)?;
                line(&r, &mut buf).and_then(|v| im.general(&v, n == 0))
            }
            tag::END => {
                let end: Counts = postcard::from_bytes(cur.take(END_BYTES)?).map_err(corrupt)?;
                if end != next || cur.at != cur.b.len() {
                    return invalid("blean: bad end record");
                }
                return Ok(im);
            }
            tag::NAME_STR => {
                let i = take_id(&mut next.names);
                let pre = cur.u32()?;
                im.do_str(i, pre, cur.str()?)
            }
            tag::NAME_NUM => {
                let i = take_id(&mut next.names);
                let pre = cur.u32()?;
                im.do_num(i, pre, cur.u64()?)
            }
            tag::SUCC => {
                let i = take_id(&mut next.levels);
                im.do_succ(i, cur.u32()?)
            }
            tag::MAX | tag::IMAX => {
                let i = take_id(&mut next.levels);
                let a = cur.u32()?;
                im.do_max(i, a, cur.u32()?, t == tag::IMAX)
            }
            tag::PARAM => {
                let i = take_id(&mut next.levels);
                im.do_param(i, cur.u32()?)
            }
            t => {
                let i = take_id(&mut next.exprs);
                let done = expr(&mut im, &mut cur, &mut us, t, i);
                cur.skip_info()?;
                done
            }
        };
        done.map_err(|e| e.at("record", n))?;
    }
    unreachable!()
}

#[inline(always)]
fn expr(im: &mut Importer<'_>, cur: &mut Cur<'_>, us: &mut Vec<u32>, t: u32, i: u32) -> Result<()> {
    match t {
        tag::BVAR => im.do_bvar(i, cur.u64()?),
        tag::SORT => im.do_sort(i, cur.u32()?),
        tag::CONST => {
            let name = cur.u32()?;
            us.clear();
            for _ in 0..cur.u32()? {
                us.push(cur.u32()?);
            }
            im.do_const(i, name, us)
        }
        tag::APP => {
            let f = cur.u32()?;
            im.do_app(i, f, cur.u32()?)
        }
        tag::LAM | tag::PI => {
            let (name, ty, body) = cur.binding()?;
            im.do_binder(i, name, ty, body, t == tag::LAM)
        }
        tag::LET => {
            let (name, ty, value, body) = (cur.u32()?, cur.u32()?, cur.u32()?, cur.u32()?);
            im.do_let(i, name, ty, value, body, cur.bool()?)
        }
        tag::NAT => im.do_nat(i, cur.str()?),
        tag::STR => im.do_strlit(i, cur.str()?),
        tag::PROJ => {
            let (n, idx) = (cur.u32()?, cur.u64()?);
            im.do_proj(i, n, idx, cur.u32()?)
        }
        tag::MDATA => im.alias(i, cur.u32()?),
        _ => invalid("blean: unknown record"),
    }
}

pub(super) fn map(file: &File) -> io::Result<Option<Mmap>> {
    let mut head = [0; MAGIC.len()];
    if (&*file).read_exact(&mut head).is_err() || head != MAGIC {
        (&*file).rewind()?;
        return Ok(None);
    }
    // SAFETY: the export must not be modified or truncated while mapped (truncation raises SIGBUS).
    let map = unsafe { Mmap::map(file)? };
    map.advise(Advice::Sequential).ok();
    map.advise(Advice::WillNeed).ok();
    Ok(Some(map))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn reference<'a>(arena: &'a Arena, bytes: &[u8]) -> Result<Store<'a>> {
        let c = blean::counts(bytes).map_err(corrupt)?;
        let mut im = Importer::new(arena, records(&c) * BYTES_PER_LINE);
        let mut next = Counts::default();
        let mut buf = Vec::new();
        for (n, e) in blean::entries(bytes).map_err(corrupt)?.enumerate() {
            let (r, _) = e.map_err(corrupt)?;
            if n == 0 && !matches!(r, Record::Meta(_)) {
                return invalid("missing export metadata");
            }
            let i = next.assign(&r).unwrap_or_default();
            match r {
                Record::Meta(_) if n > 0 => invalid("metadata after the first record"),
                Record::Meta(_) | Record::Decl(_) => {
                    line(&r, &mut buf).and_then(|v| im.general(&v, n == 0))
                }
                Record::End(_) => return im.finish(),
                Record::NameStr { pre, str } => im.do_str(i, pre, &str),
                Record::NameNum { pre, i: k } => im.do_num(i, pre, k),
                Record::Succ(l) => im.do_succ(i, l),
                Record::Max(a, b) => im.do_max(i, a, b, false),
                Record::IMax(a, b) => im.do_max(i, a, b, true),
                Record::Param(p) => im.do_param(i, p),
                Record::BVar(v) => im.do_bvar(i, v),
                Record::Sort(l) => im.do_sort(i, l),
                Record::Const { name, us } => im.do_const(i, name, &us),
                Record::App { fun, arg } => im.do_app(i, fun, arg),
                Record::Lam(b) => im.do_binder(i, b.name, b.ty, b.body, true),
                Record::Pi(b) => im.do_binder(i, b.name, b.ty, b.body, false),
                Record::Let {
                    name,
                    ty,
                    value,
                    body,
                    nondep,
                } => im.do_let(i, name, ty, value, body, nondep),
                Record::Nat(d) => im.do_nat(i, &d),
                Record::Str(s) => im.do_strlit(i, &s),
                Record::Proj {
                    type_name,
                    idx,
                    struct_,
                } => im.do_proj(i, type_name, idx, struct_),
                Record::MData(e) => im.alias(i, e),
            }?;
        }
        invalid("blean ended without an end record")
    }

    use crate::term::expr::Expr;
    use crate::term::level::Level;
    use crate::term::ptr::{ExprPtr, LevelPtr};
    use std::collections::HashMap;
    use std::hash::{BuildHasher, Hash, RandomState};

    /// Structural fingerprints, since interned hashes mix in arena addresses.
    struct Fp(RandomState, HashMap<*const Expr<'static>, u64>);

    impl Fp {
        fn h(&self, x: impl Hash) -> u64 {
            self.0.hash_one(x)
        }

        fn level(&self, l: LevelPtr<'_>) -> u64 {
            match *l {
                Level::Zero => self.h(0),
                Level::Succ(a, _) => self.h((1, self.level(a))),
                Level::Max(a, b, _) => self.h((2, self.level(a), self.level(b))),
                Level::IMax(a, b, _) => self.h((3, self.level(a), self.level(b))),
                Level::Param(n, _) => self.h((4, n.to_string())),
            }
        }

        fn expr(&mut self, e: ExprPtr<'_>) -> u64 {
            let key = (e.as_ref() as *const Expr<'_>).cast::<Expr<'static>>();
            if let Some(&f) = self.1.get(&key) {
                return f;
            }
            let f = match *e {
                Expr::Var { idx, .. } => self.h((0, idx)),
                Expr::Sort { level, .. } => self.h((1, self.level(level))),
                Expr::Const { name, levels, .. } => {
                    let ls: Vec<u64> = levels.iter().map(|&l| self.level(l)).collect();
                    self.h((2, name.to_string(), ls))
                }
                Expr::App { fun, arg, .. } => {
                    let x = (3, self.expr(fun), self.expr(arg));
                    self.h(x)
                }
                Expr::Lam { ty, body, .. } => {
                    let x = (4, self.expr(ty), self.expr(body));
                    self.h(x)
                }
                Expr::Pi { ty, body, .. } => {
                    let x = (5, self.expr(ty), self.expr(body));
                    self.h(x)
                }
                Expr::Let { data, .. } => {
                    let x = (
                        6,
                        self.expr(data.ty),
                        self.expr(data.val),
                        self.expr(data.body),
                        data.nondep,
                    );
                    self.h(x)
                }
                Expr::Proj { name, idx, e, .. } => {
                    let x = (7, name.to_string(), idx, self.expr(e));
                    self.h(x)
                }
                Expr::NatLit { n, .. } => self.h((8, n.to_string())),
                Expr::StrLit { s, .. } => self.h((9, s.s)),
                Expr::Local { id, ty, .. } => {
                    let x = (10, id, self.expr(ty));
                    self.h(x)
                }
            };
            self.1.insert(key, f);
            f
        }
    }

    type Summary = ([usize; 4], Vec<(String, u64, Option<u64>)>);

    fn summary(fp: &mut Fp, r: Result<Store<'_>>) -> Option<Summary> {
        let s = r.ok()?;
        let st = &s.stats;
        fp.1.clear();
        let decls = s
            .declars
            .iter()
            .map(|d| {
                let value = d.unfoldable().map(|(v, _)| fp.expr(v));
                (d.name().to_string(), fp.expr(d.ty()), value)
            })
            .collect();
        Some((
            [st.names, st.levels, st.expressions, st.declarations],
            decls,
        ))
    }

    const FIXTURES: [&[u8]; 5] = [
        include_bytes!("../../tests/fixtures/blean/invalid-nested-parameter.blean"),
        include_bytes!("../../tests/fixtures/blean/mutual.blean"),
        include_bytes!("../../tests/fixtures/blean/nested.blean"),
        include_bytes!("../../tests/fixtures/blean/primitives.blean"),
        include_bytes!("../../tests/fixtures/blean/theorem-reduction.blean"),
    ];

    const FLIPS: [u8; 2] = [0x01, 0x80];
    /// Coprime to the common record lengths.
    const STRIDE: usize = 7;

    #[test]
    fn hand_reader_agrees_with_decoder_on_damaged_files() {
        let fp = &mut Fp(RandomState::new(), HashMap::new());
        for bytes in FIXTURES {
            let arena = Arena::new();
            let want = summary(fp, reference(&arena, bytes));
            assert_eq!(summary(fp, import(&arena, bytes)), want);
            for at in (MAGIC.len()..bytes.len() - END_BYTES).step_by(STRIDE) {
                for flip in FLIPS {
                    let mut b = bytes.to_vec();
                    b[at] ^= flip;
                    let arena = Arena::new();
                    let (want, got) = (reference(&arena, &b), import(&arena, &b));
                    let (got, want) = (summary(fp, got), summary(fp, want));
                    assert_eq!(got, want, "byte {at} ^ {flip:#x}");
                }
            }
        }
    }
}
