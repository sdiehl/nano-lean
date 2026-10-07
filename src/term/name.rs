use super::ptr::{NamePtr, StringPtr};
use std::fmt;
use std::sync::atomic::{AtomicU8, AtomicU32, Ordering::Relaxed};

pub const ANON_HASH: u64 = 43;
pub const STR_HASH: u64 = 911;
pub const NUM_HASH: u64 = 103;
const NO_DECL: u32 = u32::MAX;
const NO_NAT_RED: u8 = u8::MAX;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Name<'a> {
    Anon,
    Str(NamePtr<'a>, StringPtr<'a>, u64),
    Num(NamePtr<'a>, u64, u64),
}

impl Name<'_> {
    #[inline]
    pub fn get_hash(&self) -> u64 {
        match self {
            Name::Anon => ANON_HASH,
            Name::Str(.., h) | Name::Num(.., h) => *h,
        }
    }
}

pub struct StrNode<'a> {
    pub s: &'a str,
    pub hash: u64,
}

impl fmt::Debug for StrNode<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self.s, f)
    }
}

#[repr(u8)]
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum NatRed {
    Succ,
    Add,
    Sub,
    Mul,
    Pow,
    Mod,
    Div,
    Gcd,
    Beq,
    Ble,
    Land,
    Lor,
    Xor,
    Shl,
    Shr,
    Log2,
}

const NAT_REDS: [NatRed; 16] = [
    NatRed::Succ,
    NatRed::Add,
    NatRed::Sub,
    NatRed::Mul,
    NatRed::Pow,
    NatRed::Mod,
    NatRed::Div,
    NatRed::Gcd,
    NatRed::Beq,
    NatRed::Ble,
    NatRed::Land,
    NatRed::Lor,
    NatRed::Xor,
    NatRed::Shl,
    NatRed::Shr,
    NatRed::Log2,
];

/// Carries its declaration index and Nat primitive tag so the checker never hashes a name.
pub struct NameNode<'a> {
    pub kind: Name<'a>,
    decl: AtomicU32,
    nat: AtomicU8,
}

impl<'a> NameNode<'a> {
    pub fn new(kind: Name<'a>) -> Self {
        Self {
            kind,
            decl: AtomicU32::new(NO_DECL),
            nat: AtomicU8::new(NO_NAT_RED),
        }
    }

    #[inline]
    pub fn decl_idx(&self) -> Option<u32> {
        let d = self.decl.load(Relaxed);
        (d != NO_DECL).then_some(d)
    }

    pub fn set_decl_idx(&self, idx: u32) {
        self.decl.store(idx, Relaxed);
    }

    #[inline]
    pub fn nat_red(&self) -> Option<NatRed> {
        NAT_REDS.get(self.nat.load(Relaxed) as usize).copied()
    }

    pub fn set_nat_red(&self, k: NatRed) {
        self.nat.store(k as u8, Relaxed);
    }

    pub fn is_anon(&self) -> bool {
        matches!(self.kind, Name::Anon)
    }
}

impl PartialEq for NameNode<'_> {
    fn eq(&self, o: &Self) -> bool {
        self.kind == o.kind
    }
}

impl Eq for NameNode<'_> {}

impl fmt::Display for NameNode<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.kind {
            Name::Anon => Ok(()),
            Name::Str(p, s, _) => {
                if !p.is_anon() {
                    write!(f, "{}.", p.as_ref())?;
                }
                f.write_str(s.s)
            }
            Name::Num(p, n, _) => {
                if !p.is_anon() {
                    write!(f, "{}.", p.as_ref())?;
                }
                write!(f, "{n}")
            }
        }
    }
}

impl fmt::Debug for NameNode<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}
