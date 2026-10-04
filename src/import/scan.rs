//! Hand scanner for the hot export line shapes. Returns None on anything it does
//! not recognise exactly; the caller then falls back to serde_json.

pub enum Line<'b> {
    Str(u32, u32, &'b str),
    Num(u32, u32, u64),
    Succ(u32, u32),
    Max(u32, u32, u32, bool),
    Param(u32, u32),
    App(u32, u32, u32),
    Bvar(u32, u64),
    Sort(u32, u32),
    /// Universe arguments are left in the caller's scratch buffer.
    Const(u32, u32),
    Binder(u32, u32, u32, u32, bool),
    Let(u32, u32, u32, u32, u32, bool),
    Proj(u32, u32, u64, u32),
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
        let mut n: u64 = 0;
        while let Some(&c) = self.b.get(self.i) {
            if !c.is_ascii_digit() {
                break;
            }
            n = n.checked_mul(10)?.checked_add(u64::from(c - b'0'))?;
            self.i += 1;
        }
        (self.i > start && (self.i - start == 1 || self.b[start] != b'0')).then_some(n)
    }

    #[inline]
    fn u32(&mut self) -> Option<u32> {
        u32::try_from(self.u64()?).ok()
    }

    #[inline]
    fn quoted(&mut self) -> Option<&'b str> {
        self.lit(b"\"")?;
        let start = self.i;
        loop {
            match *self.b.get(self.i)? {
                b'"' => break,
                b'\\' => return None,
                c if c < 0x20 => return None,
                _ => self.i += 1,
            }
        }
        let s = std::str::from_utf8(&self.b[start..self.i]).ok()?;
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
