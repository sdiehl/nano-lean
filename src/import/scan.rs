use crate::term::decl::Hint;

/// A scanned line. A string name holds the byte range of its text within the line.
#[derive(Clone, Copy)]
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

/// Leading lanes below ten. A lane at or above ten sets its top bit, and carries
/// out of a lane only disturb the lanes above it.
#[inline(always)]
fn run(x: u64) -> usize {
    let above = (x.wrapping_add(0x76 * LANES) | x) & (0x80 * LANES);
    if above == 0 {
        8
    } else {
        (above.trailing_zeros() / 8) as usize
    }
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
pub fn fast(b: &[u8], len: usize, scratch: &mut Vec<u32>) -> Option<(Line, usize)> {
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
    use super::Cur;

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
}
