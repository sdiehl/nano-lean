pub enum Line<'b> {
    Str(u32, u32, &'b str),
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
}

/// Value and length of a leading run of at most 15 digits, read eight bytes at
/// a time. None when the run is longer or too near the end to load a word.
#[inline]
fn digits(b: &[u8]) -> Option<(u64, usize)> {
    let (hi, n) = chunk(b)?;
    if n < 8 {
        return Some((hi, n));
    }
    let (lo, m) = chunk(&b[8..])?;
    (m < 8).then(|| (hi * 10u64.pow(m as u32) + lo, 8 + m))
}

/// Multiplying by this broadcasts a byte to all lanes.
const LANES: u64 = 0x0101_0101_0101_0101;
const LOW_NIBBLES: u64 = 0x0f * LANES;
const HIGH_NIBBLES: u64 = 0xf0 * LANES;
/// High nibble of every ASCII digit, `b'0' & 0xf0`.
const DIGIT_HIGH: u64 = 0x30 * LANES;
/// Added to a low nibble, carries into the high nibble exactly when it exceeds 9.
const ABOVE_NINE: u64 = 0x06 * LANES;
const LOW_SEVEN_BITS: u64 = 0x7f * LANES;
const TOP_BITS: u64 = 0x80 * LANES;
const BYTE_PAIRS: u64 = 0x00ff_00ff_00ff_00ff;
const HALF_WORDS: u64 = 0x0000_ffff_0000_ffff;
const LOW_WORD: u64 = 0x0000_0000_ffff_ffff;

#[inline]
fn chunk(b: &[u8]) -> Option<(u64, usize)> {
    let word = u64::from_le_bytes(*b.first_chunk::<8>()?);
    let values = word & LOW_NIBBLES;
    let wrong_high = (word & HIGH_NIBBLES) ^ DIGIT_HIGH;
    let too_big = (values + ABOVE_NINE) & HIGH_NIBBLES;
    let not_digit = wrong_high | too_big;
    let nonzero_lanes = (((not_digit & LOW_SEVEN_BITS) + LOW_SEVEN_BITS) | not_digit) & TOP_BITS;
    let len = (nonzero_lanes.trailing_zeros() / 8) as usize;
    if len == 0 {
        return Some((0, 0));
    }
    // Left-align the digits so the first is most significant, then fold
    // adjacent lanes: pairs of digits, then groups of four, then all eight.
    let mut x = values << (64 - 8 * len);
    x = (x * 10 + (x >> 8)) & BYTE_PAIRS;
    x = (x * 100 + (x >> 16)) & HALF_WORDS;
    x = (x * 10_000 + (x >> 32)) & LOW_WORD;
    Some((x, len))
}

struct Cur<'b> {
    b: &'b [u8],
    i: usize,
}

impl<'b> Cur<'b> {
    #[inline]
    fn lit(&mut self, s: &[u8]) -> Option<()> {
        if self.b.get(self.i..self.i + s.len())? == s {
            self.i += s.len();
            Some(())
        } else {
            None
        }
    }

    #[inline]
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

    #[inline]
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

    fn end(&self) -> Option<()> {
        let rest = &self.b[self.i..];
        (rest.is_empty() || rest == b"\r").then_some(())
    }
}

pub fn fast<'b>(b: &'b [u8], scratch: &mut Vec<u32>) -> Option<Line<'b>> {
    let mut c = Cur { b, i: 0 };
    let r = match (b.get(2)?, b.get(3)?) {
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
                c.lit(b"}}")?;
                Line::Str(i, pre, s)
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
    c.end()?;
    Some(r)
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
        let mut c = Cur { b, i: 0 };
        let n = c.u64_slow()?;
        (c.i > 0 && (c.i == 1 || b[0] != b'0')).then_some((n, c.i))
    }

    fn fast(b: &[u8]) -> Option<(u64, usize)> {
        let mut c = Cur { b, i: 0 };
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
