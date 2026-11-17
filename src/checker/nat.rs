use crate::term::name::NatRed;
use num_bigint::BigUint;
use num_integer::Integer;
use num_traits::{ToPrimitive, Zero};

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
    let mut acc = vec![0u64; ln + sn];
    for (i, xi) in l.iter_u64_digits().enumerate() {
        if xi == 0 {
            continue;
        }
        let mut carry = 0u128;
        for (a, &sj) in acc[i..i + sn].iter_mut().zip(short) {
            let t = u128::from(*a) + u128::from(xi) * u128::from(sj) + carry;
            *a = t as u64;
            carry = t >> 64;
        }
        let mut k = i + sn;
        let mut c = carry as u64;
        while c != 0 {
            let (v, o) = acc[k].overflowing_add(c);
            acc[k] = v;
            c = u64::from(o);
            k += 1;
        }
    }
    BigUint::new(
        acc.iter()
            .flat_map(|&d| [d as u32, (d >> 32) as u32])
            .collect(),
    )
}

/// One pass over the limbs, four lanes wide.
#[inline]
pub(crate) fn hash(n: &BigUint) -> u64 {
    const K: u64 = 0x9e37_79b9_7f4a_7c15;
    let mut h = [K, !K, K.rotate_left(17), K.rotate_left(41)];
    let mut len = 0u64;
    let mut it = n.iter_u64_digits();
    loop {
        let mut any = false;
        for lane in &mut h {
            if let Some(d) = it.next() {
                *lane = (lane.rotate_left(5) ^ d).wrapping_mul(K);
                len += 1;
                any = true;
            }
        }
        if !any {
            break;
        }
    }
    let mut r = len;
    for lane in h {
        r = (r.rotate_left(23) ^ lane).wrapping_mul(K);
    }
    r ^ (r >> 29)
}
