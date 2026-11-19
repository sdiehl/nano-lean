use crate::term::name::NatRed;
use num_bigint::BigUint;
use num_integer::Integer;
use num_traits::{ToPrimitive, Zero};
use std::hash::{Hash, Hasher};

const BIG_EXP: u64 = 1 << 24;
const MAX_RESULT_BITS: u64 = 1 << 26;

pub(crate) static ZERO: BigUint = BigUint::ZERO;

pub(crate) enum NatValue {
    Nat(BigUint),
    Bool(bool),
}

#[inline]
pub(crate) fn is_unary(op: NatRed) -> bool {
    matches!(op, NatRed::Succ | NatRed::Log2)
}

#[inline]
pub(crate) fn unary(op: NatRed, x: &BigUint) -> Option<BigUint> {
    match op {
        NatRed::Succ => Some(x + 1u32),
        NatRed::Log2 => Some(BigUint::from(x.bits().saturating_sub(1))),
        _ => None,
    }
}

#[inline]
pub(crate) fn binary(op: NatRed, x: &BigUint, y: &BigUint) -> Option<NatValue> {
    let r = match op {
        NatRed::Add => x + y,
        NatRed::Sub => {
            if x > y {
                x - y
            } else {
                BigUint::zero()
            }
        }
        NatRed::Mul => mul(x, y),
        NatRed::Div => {
            if y.is_zero() {
                BigUint::zero()
            } else {
                x / y
            }
        }
        NatRed::Mod => {
            if y.is_zero() {
                x.clone()
            } else {
                x % y
            }
        }
        NatRed::Gcd => x.gcd(y),
        NatRed::Beq => return Some(NatValue::Bool(x == y)),
        NatRed::Ble => return Some(NatValue::Bool(x <= y)),
        NatRed::Land => x & y,
        NatRed::Lor => x | y,
        NatRed::Xor => x ^ y,
        NatRed::Shl => x << y.to_u64().filter(|&k| k <= BIG_EXP)?,
        NatRed::Shr => match y.to_u64() {
            Some(k) => x >> k,
            None => BigUint::zero(),
        },
        NatRed::Pow => {
            let k = y.to_u64().filter(|&k| k <= BIG_EXP)?;
            if x.bits().saturating_mul(k) > MAX_RESULT_BITS {
                return None;
            }
            x.pow(k as u32)
        }
        NatRed::Succ | NatRed::Log2 => return None,
    };
    Some(NatValue::Nat(r))
}

const SHORT_LIMBS: usize = 32;
const LONG_LIMBS: usize = 256;

/// Schoolbook over the long operand's limbs, skipping the zero ones, when the other is short.
fn mul(x: &BigUint, y: &BigUint) -> BigUint {
    let (l, s) = if x.bits() >= y.bits() { (x, y) } else { (y, x) };
    let (ln, sn) = (l.iter_u64_digits().len(), s.iter_u64_digits().len());
    if sn == 0 || sn > SHORT_LIMBS || ln < LONG_LIMBS {
        return x * y;
    }
    let mut short = [0u64; SHORT_LIMBS];
    for (d, v) in short.iter_mut().zip(s.iter_u64_digits()) {
        *d = v;
    }
    let short = &short[..sn];
    let mut out = vec![0u32; 2 * (ln + sn)];
    for (i, xi) in l.iter_u64_digits().enumerate() {
        if xi != 0 {
            mac(&mut out[2 * i..], xi, short);
        }
    }
    BigUint::new(out)
}

/// Adds `xi * short` into the base 2^32 digits of `out`.
fn mac(out: &mut [u32], xi: u64, short: &[u64]) {
    let mut carry = 0u128;
    let mut pairs = out.chunks_exact_mut(2);
    for (&sj, p) in short.iter().zip(pairs.by_ref()) {
        let a = u64::from(p[0]) | u64::from(p[1]) << 32;
        let t = u128::from(a) + u128::from(xi) * u128::from(sj) + carry;
        (p[0], p[1]) = (t as u32, (t >> 32) as u32);
        carry = t >> 64;
    }
    let mut c = carry as u64;
    for p in pairs {
        if c == 0 {
            break;
        }
        let (v, o) = (u64::from(p[0]) | u64::from(p[1]) << 32).overflowing_add(c);
        (p[0], p[1]) = (v as u32, (v >> 32) as u32);
        c = u64::from(o);
    }
}

const K: u64 = 0x9e37_79b9_7f4a_7c15;

#[inline]
pub(crate) fn hash(n: &BigUint) -> u64 {
    let mut it = n.iter_u64_digits();
    if it.len() > 1 {
        return hash_wide(n);
    }
    let r = (it.next().unwrap_or(0) ^ K).wrapping_mul(K);
    r ^ (r >> 29)
}

/// `BigUint` hashes its limbs with one `write` of their bytes, which this hasher mixes in
/// eight independent lanes.
#[inline(never)]
fn hash_wide(n: &BigUint) -> u64 {
    struct Wide(u64);
    impl Hasher for Wide {
        fn write(&mut self, b: &[u8]) {
            let mut acc: [u64; 8] = std::array::from_fn(|i| K.rotate_left(8 * i as u32));
            let mut mix = |i: usize, d: &[u8; 8]| {
                acc[i] = (acc[i].rotate_left(29) ^ u64::from_le_bytes(*d)).wrapping_mul(K);
            };
            let (limbs, _) = b.as_chunks::<8>();
            let (blocks, rest) = limbs.as_chunks::<8>();
            for block in blocks {
                for (i, d) in block.iter().enumerate() {
                    mix(i, d);
                }
            }
            for (i, d) in rest.iter().enumerate() {
                mix(i, d);
            }
            let h = acc.iter().fold(b.len() as u64, |h, &a| {
                (h ^ a).wrapping_mul(K).rotate_left(31)
            });
            self.0 = (self.0.rotate_left(23) ^ h).wrapping_mul(K);
        }
        fn write_usize(&mut self, _: usize) {}
        fn finish(&self) -> u64 {
            let r = (self.0 ^ (self.0 >> 32)).wrapping_mul(K);
            r ^ (r >> 29)
        }
    }
    let mut w = Wide(K);
    n.hash(&mut w);
    w.finish()
}
