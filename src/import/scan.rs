use crate::term::decl::Hint;

/// A scanned line. A string name holds the byte range of its text within the line.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Line {
    Str(u32, u32, u32, u32),
    Num(u32, u32, u64),
    Succ(u32, u32),
    Max(u32, u32, u32, bool),
    Param(u32, u32),
    App(u32, u32, u32),
    Bvar(u32, u64),
    Sort(u32, u32),
    Const(u32, u32),
    Binder(u32, u32, u32, u32, bool),
    Let(u32, u32, u32, u32, u32, bool),
    Proj(u32, u32, u64, u32),
    Thm(u32, u32, u32),
    Def(u32, u32, u32, Hint),
}

impl Line {
    /// Lines whose universe list rides separately, in the scratch vector.
    pub fn listed(&self) -> bool {
        matches!(self, Line::Const(..) | Line::Thm(..) | Line::Def(..))
    }
}

/// Value and length of a leading run of at most 15 digits, read eight bytes at
/// a time. None when the run is longer or too near the end to load a word.
#[inline(always)]
fn digits(b: &[u8]) -> Option<(u64, usize)> {
    let x = word(b)?;
    let n = run(x);
    if n < 8 {
        return Some((packed(x, n), n));
    }
    let hi = packed(x, 8);
    if !b.get(8)?.is_ascii_digit() {
        return Some((hi, 8));
    }
    let y = word(&b[8..])?;
    let m = run(y);
    (m < 8).then(|| (hi * POW10[m] + packed(y, m), 8 + m))
}

const POW10: [u64; 8] = [1, 10, 100, 1_000, 10_000, 100_000, 1_000_000, 10_000_000];

/// Multiplying by this broadcasts a byte to all lanes.
const LANES: u64 = 0x0101_0101_0101_0101;

/// Eight bytes with ASCII digits mapped to their values.
#[inline(always)]
fn word(b: &[u8]) -> Option<u64> {
    Some(u64::from_le_bytes(*b.first_chunk::<8>()?) ^ (0x30 * LANES))
}

/// Leading lanes below ten.
#[inline(always)]
fn run(x: u64) -> usize {
    (above(x).trailing_zeros() / 8).min(8) as usize
}

/// The first `n` lanes as a decimal number, folding digit pairs then halves.
#[inline(always)]
fn packed(x: u64, n: usize) -> u64 {
    const PAIRS: u64 = 0x0000_00ff_0000_00ff;
    const HIGH: u64 = 0x000f_4240_0000_0064;
    const LOW: u64 = 0x0000_2710_0000_0001;
    if n == 0 {
        return 0;
    }
    let v = x << (64 - 8 * n);
    let y = v.wrapping_mul(10).wrapping_add(v >> 8);
    ((y & PAIRS)
        .wrapping_mul(HIGH)
        .wrapping_add(((y >> 16) & PAIRS).wrapping_mul(LOW)))
        >> 32
}

/// `b` may run on past the line so word loads near its end stay in bounds, `len`
/// is where the line stops.
struct Cur<'b> {
    b: &'b [u8],
    i: usize,
    len: usize,
}

impl<'b> Cur<'b> {
    #[inline(always)]
    fn lit(&mut self, s: &[u8]) -> Option<()> {
        if self.b.get(self.i..self.i + s.len())? == s {
            self.i += s.len();
            Some(())
        } else {
            None
        }
    }

    #[inline(always)]
    fn u64(&mut self) -> Option<u64> {
        let start = self.i;
        let n = match digits(&self.b[start..]) {
            Some((n, len)) => {
                self.i += len;
                n
            }
            None => self.u64_slow()?,
        };
        (self.i > start && (self.i - start == 1 || self.b[start] != b'0')).then_some(n)
    }

    fn u64_slow(&mut self) -> Option<u64> {
        let mut n: u64 = 0;
        while let Some(&c) = self.b.get(self.i) {
            if !c.is_ascii_digit() {
                break;
            }
            n = n.checked_mul(10)?.checked_add(u64::from(c - b'0'))?;
            self.i += 1;
        }
        Some(n)
    }

    #[inline(always)]
    fn u32(&mut self) -> Option<u32> {
        u32::try_from(self.u64()?).ok()
    }

    #[inline]
    fn quoted(&mut self) -> Option<&'b str> {
        self.lit(b"\"")?;
        let start = self.i;
        let mut ascii = true;
        loop {
            match *self.b.get(self.i)? {
                b'"' => break,
                b'\\' => return None,
                c if c < b' ' => return None,
                c => {
                    ascii &= c.is_ascii();
                    self.i += 1;
                }
            }
        }
        let bytes = &self.b[start..self.i];
        let s = if ascii {
            // SAFETY: every byte was checked to be ASCII above.
            unsafe { std::str::from_utf8_unchecked(bytes) }
        } else {
            std::str::from_utf8(bytes).ok()?
        };
        self.i += 1;
        Some(s)
    }

    fn bool(&mut self) -> Option<bool> {
        if self.lit(b"true").is_some() {
            Some(true)
        } else {
            self.lit(b"false").map(|()| false)
        }
    }

    fn u32s(&mut self, out: &mut Vec<u32>) -> Option<()> {
        out.clear();
        self.lit(b"[")?;
        if self.lit(b"]").is_some() {
            return Some(());
        }
        loop {
            out.push(self.u32()?);
            if self.lit(b"]").is_some() {
                return Some(());
            }
            self.lit(b",")?;
        }
    }

    /// Where the line stops: `len`, or a newline after an optional carriage return.
    fn end(&self) -> Option<usize> {
        let j = self.i + usize::from(self.b.get(self.i) == Some(&b'\r'));
        (j == self.len || self.b.get(j) == Some(&b'\n')).then_some(j)
    }
}

/// The whole lines of one chunk, scanned off the importing thread. The bytes before
/// the first and after the last newline belong to lines split across chunks. Universe
/// lists of constants follow each other in `us`, each prefixed by its length.
#[derive(Default)]
pub struct Batch {
    pub buf: Vec<u8>,
    pub body: Option<(usize, usize)>,
    pub lines: Vec<(u32, u32, Option<Line>)>,
    pub us: Vec<u32>,
}

impl Batch {
    /// Scans `buf`, reusing the line and universe vectors of an earlier batch.
    pub fn scan(&mut self) {
        let Self {
            buf,
            body,
            lines,
            us,
        } = self;
        lines.clear();
        lines.reserve(buf.len() / 56);
        us.clear();
        let mut scratch = Vec::new();
        *body = memchr::memchr(b'\n', buf).zip(memchr::memrchr(b'\n', buf));
        if let Some((first, last)) = *body {
            let mut s = first + 1;
            while s <= last {
                let (l, e) = match fast(&buf[s..], usize::MAX, &mut scratch) {
                    Some((l, e)) => (Some(l), s + e),
                    None => (
                        None,
                        memchr::memchr(b'\n', &buf[s..=last]).map_or(last, |k| s + k),
                    ),
                };
                if e > s {
                    if l.as_ref().is_some_and(Line::listed) {
                        us.push(scratch.len() as u32);
                        us.extend_from_slice(&scratch);
                    }
                    lines.push((s as u32, e as u32, l));
                }
                s = e + 1;
            }
        }
    }
}

/// The rest of a declaration whose group is just itself, with its universe list
/// in `scratch`. Definitions read their hint and must be safe.
#[inline]
fn decl(
    c: &mut Cur<'_>,
    scratch: &mut Vec<u32>,
    hint: Option<&mut Hint>,
) -> Option<(u32, u32, u32)> {
    let all = c.u32()?;
    c.lit(b"]")?;
    let def = hint.is_some();
    if let Some(h) = hint {
        c.lit(b",\"hints\":")?;
        *h = if c.lit(b"\"abbrev\"").is_some() {
            Hint::Abbrev
        } else if c.lit(b"\"opaque\"").is_some() {
            Hint::Opaque
        } else {
            c.lit(b"{\"regular\":")?;
            let r = c.u32()?;
            c.lit(b"}")?;
            Hint::Regular(r)
        };
    }
    c.lit(b",\"levelParams\":")?;
    c.u32s(scratch)?;
    c.lit(b",\"name\":")?;
    let n = c.u32()?;
    if def {
        c.lit(b",\"safety\":\"safe\"")?;
    }
    c.lit(b",\"type\":")?;
    let ty = c.u32()?;
    c.lit(b",\"value\":")?;
    let val = c.u32()?;
    c.lit(b"}}")?;
    (n == all).then_some((n, ty, val))
}

/// The line and where it stops. Pass `usize::MAX` as `len` to stop at the next newline.
#[inline(always)]
pub fn fast(b: &[u8], len: usize, scratch: &mut Vec<u32>) -> Option<(Line, usize)> {
    if let Some(w) = b.first_chunk::<WIN>()
        && let Some(r) = match w[2] {
            b'a' => app(w, len).map(|(e, f, a, j)| (Line::App(e, f, a), j)),
            b'f' => forall(w, len),
            b'i' => lam(w, len),
            _ => None,
        }
    {
        return Some(r);
    }
    other(b, len, scratch)
}

#[inline(never)]
fn other(b: &[u8], len: usize, scratch: &mut Vec<u32>) -> Option<(Line, usize)> {
    let mut c = Cur { b, i: 0, len };
    let r = match (b.get(2)?, b.get(3)?) {
        (b't', _) => {
            c.lit(b"{\"thm\":{\"all\":[")?;
            let (n, ty, val) = decl(&mut c, scratch, None)?;
            Line::Thm(n, ty, val)
        }
        (b'd', _) => {
            c.lit(b"{\"def\":{\"all\":[")?;
            let mut h = Hint::Opaque;
            let (n, ty, val) = decl(&mut c, scratch, Some(&mut h))?;
            Line::Def(n, ty, val, h)
        }
        (b'a', _) => {
            c.lit(b"{\"app\":{\"arg\":")?;
            let a = c.u32()?;
            c.lit(b",\"fn\":")?;
            let f = c.u32()?;
            c.lit(b"},\"ie\":")?;
            let i = c.u32()?;
            c.lit(b"}")?;
            Line::App(i, f, a)
        }
        (b'b', _) => {
            c.lit(b"{\"bvar\":")?;
            let v = c.u64()?;
            c.lit(b",\"ie\":")?;
            let i = c.u32()?;
            c.lit(b"}")?;
            Line::Bvar(i, v)
        }
        (b'c', _) => {
            c.lit(b"{\"const\":{\"name\":")?;
            let n = c.u32()?;
            c.lit(b",\"us\":")?;
            c.u32s(scratch)?;
            c.lit(b"},\"ie\":")?;
            let i = c.u32()?;
            c.lit(b"}")?;
            Line::Const(i, n)
        }
        (b'f', _) => {
            c.lit(b"{\"forallE\":")?;
            let (name, ty, body) = binder(&mut c)?;
            c.lit(b",\"ie\":")?;
            let i = c.u32()?;
            c.lit(b"}")?;
            Line::Binder(i, name, ty, body, false)
        }
        (b'i', b'e') => {
            c.lit(b"{\"ie\":")?;
            let i = c.u32()?;
            c.lit(b",\"")?;
            match c.b.get(c.i)? {
                b'l' if c.lit(b"lam\":").is_some() => {
                    let (name, ty, body) = binder(&mut c)?;
                    c.lit(b"}")?;
                    Line::Binder(i, name, ty, body, true)
                }
                b'l' => {
                    c.lit(b"letE\":{\"body\":")?;
                    let body = c.u32()?;
                    c.lit(b",\"name\":")?;
                    let name = c.u32()?;
                    c.lit(b",\"nondep\":")?;
                    let nondep = c.bool()?;
                    c.lit(b",\"type\":")?;
                    let ty = c.u32()?;
                    c.lit(b",\"value\":")?;
                    let val = c.u32()?;
                    c.lit(b"}}")?;
                    Line::Let(i, name, ty, val, body, nondep)
                }
                b's' => {
                    c.lit(b"sort\":")?;
                    let l = c.u32()?;
                    c.lit(b"}")?;
                    Line::Sort(i, l)
                }
                b'p' => {
                    c.lit(b"proj\":{\"idx\":")?;
                    let k = c.u64()?;
                    c.lit(b",\"struct\":")?;
                    let e = c.u32()?;
                    c.lit(b",\"typeName\":")?;
                    let n = c.u32()?;
                    c.lit(b"}}")?;
                    Line::Proj(i, n, k, e)
                }
                _ => return None,
            }
        }
        (b'i', b'n') => {
            c.lit(b"{\"in\":")?;
            let i = c.u32()?;
            if c.lit(b",\"str\":{\"pre\":").is_some() {
                let pre = c.u32()?;
                c.lit(b",\"str\":")?;
                let s = c.quoted()?;
                let at = s.as_ptr() as usize - b.as_ptr() as usize;
                c.lit(b"}}")?;
                Line::Str(i, pre, at as u32, (at + s.len()) as u32)
            } else {
                c.lit(b",\"num\":{\"i\":")?;
                let n = c.u64()?;
                c.lit(b",\"pre\":")?;
                let pre = c.u32()?;
                c.lit(b"}}")?;
                Line::Num(i, pre, n)
            }
        }
        (b'i', b'l') => {
            c.lit(b"{\"il\":")?;
            let i = c.u32()?;
            c.lit(b",\"")?;
            let r = match c.b.get(c.i)? {
                b's' => {
                    c.lit(b"succ\":")?;
                    Line::Succ(i, c.u32()?)
                }
                b'p' => {
                    c.lit(b"param\":")?;
                    Line::Param(i, c.u32()?)
                }
                b'm' | b'i' => {
                    let imax = c.lit(b"imax\":[").is_some();
                    if !imax {
                        c.lit(b"max\":[")?;
                    }
                    let a = c.u32()?;
                    c.lit(b",")?;
                    let d = c.u32()?;
                    c.lit(b"]")?;
                    Line::Max(i, a, d, imax)
                }
                _ => return None,
            };
            c.lit(b"}")?;
            r
        }
        _ => return None,
    };
    c.end().map(|e| (r, e))
}

/// Application and binder lines are most of an export, so they are read from a fixed
/// window with word compares. The longest such line ends before byte 120.
pub const WIN: usize = 128;

/// The bytes of `s` as a little endian word, with the mask covering them.
const fn tag(s: &[u8]) -> (u64, u64) {
    let mut w = 0u64;
    let mut k = 0;
    while k < s.len() {
        w |= (s[k] as u64) << (8 * k);
        k += 1;
    }
    (w, u64::MAX >> (64 - 8 * s.len()))
}

#[inline(always)]
fn ld(w: &[u8; WIN], i: usize) -> u64 {
    let mut a = [0; 8];
    a.copy_from_slice(&w[i..i + 8]);
    u64::from_le_bytes(a)
}

#[inline(always)]
fn has(w: &[u8; WIN], i: &mut usize, s: &[u8]) -> bool {
    let mut ok = true;
    for c in s.chunks(8) {
        let (t, m) = tag(c);
        ok &= ld(w, *i) & m == t;
        *i += c.len();
    }
    ok
}

/// The binder info and the body key after it.
#[inline(always)]
fn info(w: &[u8; WIN], i: &mut usize) -> bool {
    match (w[*i], w[*i + 2]) {
        (b'd', _) => has(w, i, b"default\",\"body\":"),
        (b'i', b'p') => has(w, i, b"implicit\",\"body\":"),
        (b'i', _) => has(w, i, b"instImplicit\",\"body\":"),
        _ => has(w, i, b"strictImplicit\",\"body\":"),
    }
}

/// The body, name and type ids of a binder whose info starts at `i`.
#[inline(always)]
fn parts(w: &[u8; WIN], i: &mut usize) -> Option<(u32, u32, u32)> {
    if !info(w, i) {
        return None;
    }
    let body = id(w, i)?;
    if !has(w, i, b",\"name\":") {
        return None;
    }
    let name = id(w, i)?;
    if !has(w, i, b",\"type\":") {
        return None;
    }
    let ty = id(w, i)?;
    Some((name, ty, body))
}

#[inline(always)]
fn end(w: &[u8; WIN], i: usize, len: usize, s: &[u8]) -> Option<usize> {
    let mut k = i;
    if !has(w, &mut k, s) {
        return None;
    }
    let j = k + usize::from(w[k] == b'\r');
    (j == len || w[j] == b'\n').then_some(j)
}

#[inline(always)]
fn forall(w: &[u8; WIN], len: usize) -> Option<(Line, usize)> {
    let mut i = 0;
    if !has(w, &mut i, b"{\"forallE\":{\"binderInfo\":\"") {
        return None;
    }
    let (name, ty, body) = parts(w, &mut i)?;
    if !has(w, &mut i, b"},\"ie\":") {
        return None;
    }
    let e = id(w, &mut i)?;
    let j = end(w, i, len, b"}")?;
    Some((Line::Binder(e, name, ty, body, false), j))
}

#[inline(always)]
fn lam(w: &[u8; WIN], len: usize) -> Option<(Line, usize)> {
    let mut i = 6;
    if ld(w, 0) & tag(b"{\"ie\":").1 != tag(b"{\"ie\":").0 {
        return None;
    }
    let e = id(w, &mut i)?;
    if !has(w, &mut i, b",\"lam\":{\"binderInfo\":\"") {
        return None;
    }
    let (name, ty, body) = parts(w, &mut i)?;
    let j = end(w, i, len, b"}}")?;
    Some((Line::Binder(e, name, ty, body, true), j))
}

/// Lanes at or above ten as their top bits. A carry out of a lane only disturbs the
/// lanes above it.
#[inline(always)]
fn above(x: u64) -> u64 {
    (x.wrapping_add(0x76 * LANES) | x) & (0x80 * LANES)
}

/// Eight left aligned digit lanes as a number, leading zero lanes included.
#[inline(always)]
fn fold(v: u64) -> u64 {
    const PAIRS: u64 = 0x0000_00ff_0000_00ff;
    const HIGH: u64 = 0x000f_4240_0000_0064;
    const LOW: u64 = 0x0000_2710_0000_0001;
    let y = v.wrapping_mul(10).wrapping_add(v >> 8);
    ((y & PAIRS)
        .wrapping_mul(HIGH)
        .wrapping_add(((y >> 16) & PAIRS).wrapping_mul(LOW)))
        >> 32
}

/// A canonical decimal of at most ten digits that fits a u32. The top bit of the first
/// lane that is not a digit sits at `8 * n + 7`.
#[inline(always)]
fn id(w: &[u8; WIN], i: &mut usize) -> Option<u32> {
    let x = ld(w, *i) ^ (0x30 * LANES);
    let ax = above(x);
    if ax != 0 {
        let t = ax.trailing_zeros();
        if t == 7 || (x & 0xff == 0 && t > 15) {
            return None;
        }
        *i += (t >> 3) as usize;
        return Some(fold(x << (71 - t)) as u32);
    }
    let y = ld(w, *i + 8) ^ (0x30 * LANES);
    let t = above(y).trailing_zeros();
    if x & 0xff == 0 || t > 23 {
        return None;
    }
    let hi = fold(x);
    if t == 7 {
        *i += 8;
        return Some(hi as u32);
    }
    *i += 8 + (t >> 3) as usize;
    let m = (t >> 3) as usize;
    u32::try_from(hi * POW10[m] + fold(y << (71 - t))).ok()
}

/// The ids of an application line and where it stops.
#[inline(always)]
pub fn app(w: &[u8; WIN], len: usize) -> Option<(u32, u32, u32, usize)> {
    let mut i = 6;
    if ld(w, 0) != tag(b"{\"app\":{").0 || !has(w, &mut i, b":{\"arg\":") {
        return None;
    }
    let a = id(w, &mut i)?;
    if !has(w, &mut i, b",\"fn\":") {
        return None;
    }
    let f = id(w, &mut i)?;
    if !has(w, &mut i, b"},\"ie\":") {
        return None;
    }
    let e = id(w, &mut i)?;
    let j = end(w, i, len, b"}")?;
    Some((e, f, a, j))
}

fn binder(c: &mut Cur<'_>) -> Option<(u32, u32, u32)> {
    c.lit(b"{\"binderInfo\":")?;
    c.quoted()?;
    c.lit(b",\"body\":")?;
    let body = c.u32()?;
    c.lit(b",\"name\":")?;
    let name = c.u32()?;
    c.lit(b",\"type\":")?;
    let ty = c.u32()?;
    c.lit(b"}")?;
    Some((name, ty, body))
}

#[cfg(test)]
mod tests {
    use super::{Cur, WIN, other};

    fn slow(b: &[u8]) -> Option<(u64, usize)> {
        let mut c = Cur {
            b,
            i: 0,
            len: b.len(),
        };
        let n = c.u64_slow()?;
        (c.i > 0 && (c.i == 1 || b[0] != b'0')).then_some((n, c.i))
    }

    fn fast(b: &[u8]) -> Option<(u64, usize)> {
        let mut c = Cur {
            b,
            i: 0,
            len: b.len(),
        };
        c.u64().map(|n| (n, c.i))
    }

    #[test]
    fn word_digits_agree_with_checked_loop() {
        let mut cases: Vec<Vec<u8>> = [
            "0",
            "00",
            "7",
            "4294967295",
            "4294967296",
            "18446744073709551615",
            "18446744073709551616",
            "99999999999999999999",
            "12345678",
            "123456789",
            "1234567890123456",
            "123456789012345",
            "x",
            "",
        ]
        .iter()
        .flat_map(|d| {
            [
                d.to_string(),
                format!("{d},\"fn\":12345678}}"),
                format!("{d}}}"),
            ]
        })
        .map(String::into_bytes)
        .collect();
        let mut seed = 0x9e37_79b9_7f4a_7c15u64;
        for _ in 0..20000 {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            let len = (seed % 24) as usize;
            let tail = b"0123456789/:,}\x00\xff";
            cases.push(
                (0..len + 4)
                    .map(|k| {
                        let r = (seed >> (k % 60)) as usize;
                        if k < len {
                            b'0' + (r % 10) as u8
                        } else {
                            tail[r % tail.len()]
                        }
                    })
                    .collect(),
            );
        }
        for b in &cases {
            assert_eq!(fast(b), slow(b), "{:?}", String::from_utf8_lossy(b));
        }
    }

    #[test]
    fn window_lines_agree_with_cursor() {
        let ids = [
            "0",
            "7",
            "12345678",
            "123456789",
            "4294967295",
            "4294967296",
            "012",
            "",
            "x",
        ];
        let infos = [
            "default",
            "implicit",
            "instImplicit",
            "strictImplicit",
            "other",
        ];
        let mut lines = Vec::new();
        for (a, b) in ids.iter().zip(ids.iter().rev()) {
            lines.push(format!("{{\"app\":{{\"arg\":{a},\"fn\":{b}}},\"ie\":{a}}}"));
            for k in infos {
                let p =
                    format!("{{\"binderInfo\":\"{k}\",\"body\":{a},\"name\":{b},\"type\":{a}}}");
                lines.push(format!("{{\"forallE\":{p},\"ie\":{b}}}"));
                lines.push(format!("{{\"ie\":{b},\"lam\":{p}}}"));
            }
        }
        let mut cases = Vec::new();
        for l in &lines {
            for tail in ["", "\r", "x", "}", " "] {
                cases.push(format!("{l}{tail}"));
            }
            cases.push(l[..l.len() - 1].to_string());
        }
        for c in cases {
            let mut b = c.clone().into_bytes();
            b.push(b'\n');
            b.resize(b.len() + WIN, b'9');
            let (mut x, mut y) = (Vec::new(), Vec::new());
            for len in [usize::MAX, c.len()] {
                assert_eq!(super::fast(&b, len, &mut x), other(&b, len, &mut y), "{c}");
            }
        }
    }
}
