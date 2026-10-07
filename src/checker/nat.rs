use crate::term::name::NatRed;
use num_bigint::BigUint;
use num_integer::Integer;
use num_traits::{ToPrimitive, Zero};

const BIG_EXP: u64 = 1 << 24;

pub(crate) enum NatValue {
    Nat(BigUint),
    Bool(bool),
}

#[inline]
pub(crate) fn is_unary(op: NatRed) -> bool {
    matches!(op, NatRed::Succ | NatRed::Log2)
}

#[inline]
pub(crate) fn unary(op: NatRed, x: BigUint) -> Option<BigUint> {
    match op {
        NatRed::Succ => Some(x + 1u32),
        NatRed::Log2 => Some(BigUint::from(x.bits().saturating_sub(1))),
        _ => None,
    }
}

#[inline]
pub(crate) fn binary(op: NatRed, x: BigUint, y: BigUint) -> Option<NatValue> {
    let r = match op {
        NatRed::Add => x + y,
        NatRed::Sub => {
            if x > y {
                x - y
            } else {
                BigUint::zero()
            }
        }
        NatRed::Mul => x * y,
        NatRed::Div => {
            if y.is_zero() {
                y
            } else {
                x / y
            }
        }
        NatRed::Mod => {
            if y.is_zero() {
                x
            } else {
                x % y
            }
        }
        NatRed::Gcd => x.gcd(&y),
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
        NatRed::Pow => x.pow(u32::try_from(y.to_u64().filter(|&k| k <= BIG_EXP)?).ok()?),
        NatRed::Succ | NatRed::Log2 => return None,
    };
    Some(NatValue::Nat(r))
}
