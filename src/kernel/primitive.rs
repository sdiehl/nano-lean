use super::inductive::spine;
use super::prelude::*;
use super::{Expr, Level};
use crate::term::names::{
    BOOL_FALSE, BOOL_TRUE, CHAR, CHAR_OF_NAT, LIST_CONS, LIST_NIL, NAT_SUCC, NAT_ZERO,
    STRING_OF_LIST,
};
use num_bigint::BigUint;
use num_integer::Integer;
use num_traits::{ToPrimitive, Zero};

// Past these caps the primitive declines and the definition unfolds, as in Lean.
const BIG_EXP: u64 = 1 << 24;
const MAX_RESULT_BITS: u64 = 1 << 26;

pub(super) fn symbol(path: &str, encoded: bool) -> String {
    if encoded {
        serde_json::to_string(&path.split('.').collect::<Vec<_>>())
            .expect("serializing strings cannot fail")
    } else {
        path.into()
    }
}

#[derive(Clone, Copy)]
pub(super) enum NatOp {
    Succ,
    Log2,
    Add,
    Sub,
    Mul,
    Pow,
    Div,
    Mod,
    Gcd,
    Beq,
    Ble,
    Land,
    Lor,
    Xor,
    ShiftLeft,
    ShiftRight,
}

const NAT_OPS: [(&str, NatOp, usize); 16] = [
    ("succ", NatOp::Succ, 1),
    ("log2", NatOp::Log2, 1),
    ("add", NatOp::Add, 2),
    ("sub", NatOp::Sub, 2),
    ("mul", NatOp::Mul, 2),
    ("pow", NatOp::Pow, 2),
    ("div", NatOp::Div, 2),
    ("mod", NatOp::Mod, 2),
    ("gcd", NatOp::Gcd, 2),
    ("beq", NatOp::Beq, 2),
    ("ble", NatOp::Ble, 2),
    ("land", NatOp::Land, 2),
    ("lor", NatOp::Lor, 2),
    ("xor", NatOp::Xor, 2),
    ("shiftLeft", NatOp::ShiftLeft, 2),
    ("shiftRight", NatOp::ShiftRight, 2),
];

impl NatOp {
    pub(super) fn parse(name: &str) -> Option<(Self, usize)> {
        let op = name.strip_prefix("Nat.").or_else(|| {
            name.strip_prefix("[\"Nat\",\"")
                .and_then(|n| n.strip_suffix("\"]"))
        })?;
        NAT_OPS
            .iter()
            .find(|(n, ..)| *n == op)
            .map(|&(_, op, arity)| (op, arity))
    }

    fn apply(self, a: BigUint, b: BigUint) -> Option<BigUint> {
        Some(match self {
            Self::Add => a + b,
            Self::Sub if a >= b => a - b,
            Self::Sub => BigUint::ZERO,
            Self::Mul => a * b,
            Self::Div if b.is_zero() => BigUint::ZERO,
            Self::Div => a / b,
            Self::Mod if b.is_zero() => a,
            Self::Mod => a % b,
            Self::Gcd => a.gcd(&b),
            Self::Land => a & b,
            Self::Lor => a | b,
            Self::Xor => a ^ b,
            Self::Pow => {
                let exp = b.to_u64().filter(|&e| e <= BIG_EXP)?;
                if a.bits().saturating_mul(exp) > MAX_RESULT_BITS {
                    return None;
                }
                a.pow(exp as u32)
            }
            Self::ShiftLeft => a << b.to_u64().filter(|&s| s <= BIG_EXP)?,
            Self::ShiftRight => match b.to_u64() {
                Some(s) => a >> s,
                None => BigUint::ZERO,
            },
            Self::Succ | Self::Log2 | Self::Beq | Self::Ble => unreachable!(),
        })
    }
}

impl Checker<'_> {
    pub(super) fn builtin_name(&self, path: &str) -> String {
        let encoded = symbol(path, true);
        if self.env.declarations.contains_key(&encoded) {
            encoded
        } else {
            path.into()
        }
    }

    pub(super) fn builtin(&self, path: &str, levels: Vec<Level>) -> Expr {
        Expr::Const(self.builtin_name(path), levels)
    }

    pub(super) fn literal_type(&mut self, path: &str) -> Result<Expr> {
        let ty = self.builtin(path, vec![]);
        let sort = self.infer(&ty)?;
        if !self.conv(&sort, &Expr::Sort(Level::Nat(1)))? {
            return Err(Error::Rejected(format!("invalid literal type: {path}")));
        }
        Ok(ty)
    }

    pub(super) fn nat_constructor(&self, n: &BigUint) -> Expr {
        if n.is_zero() {
            self.builtin(NAT_ZERO, vec![])
        } else {
            self.builtin(NAT_SUCC, vec![]).app(Expr::nat(n - 1u32))
        }
    }

    pub(super) fn nat_literal_eq(&mut self, n: &BigUint, other: &Expr) -> Result<bool> {
        let (head, args) = spine(other);
        if let Expr::Const(name, levels) = head {
            if !levels.is_empty() {
                return Ok(false);
            }
            if name == self.builtin_name(NAT_ZERO) && args.is_empty() {
                return Ok(n.is_zero());
            }
            if name == self.builtin_name(NAT_SUCC) && args.len() == 1 && !n.is_zero() {
                return self.conv(&Expr::nat(n - 1u32), &args[0]);
            }
        }
        Ok(false)
    }

    pub(super) fn string_constructor(&mut self, s: &str) -> Result<Expr> {
        let char_ty = self.builtin(CHAR, vec![]);
        let mut list = self
            .builtin(LIST_NIL, vec![Level::Nat(0)])
            .app(char_ty.clone());
        let cons = self.builtin(LIST_CONS, vec![Level::Nat(0)]).app(char_ty);
        for ch in s.chars().rev() {
            self.tick()?;
            let value = self.builtin(CHAR_OF_NAT, vec![]).app(Expr::nat(ch as u32));
            list = cons.clone().app(value).app(list);
        }
        Ok(self.builtin(STRING_OF_LIST, vec![]).app(list))
    }

    fn natural_value(&mut self, e: &Expr) -> Result<Option<BigUint>> {
        Ok(match self.whnf(e)? {
            Expr::Nat(n) => Some(n.0),
            Expr::Const(n, us) if us.is_empty() && n == self.builtin_name(NAT_ZERO) => {
                Some(BigUint::ZERO)
            }
            _ => None,
        })
    }

    pub(super) fn reduce_primitive(&mut self, head: &Expr, args: &[Expr]) -> Result<Option<Expr>> {
        let Expr::Const(name, levels) = head else {
            return Ok(None);
        };
        let Some((op, _)) =
            NatOp::parse(name).filter(|&(_, arity)| levels.is_empty() && arity == args.len())
        else {
            return Ok(None);
        };
        match op {
            NatOp::Succ => return Ok(self.natural_value(&args[0])?.map(|n| Expr::nat(n + 1u32))),
            NatOp::Log2 => {
                return Ok(self
                    .natural_value(&args[0])?
                    .map(|n| Expr::nat(BigUint::from(n.bits().saturating_sub(1)))));
            }
            _ => {}
        }
        let Some(a) = self.natural_value(&args[0])? else {
            return Ok(None);
        };
        let Some(b) = self.natural_value(&args[1])? else {
            return Ok(None);
        };
        let value = match op {
            NatOp::Beq => a == b,
            NatOp::Ble => a <= b,
            op => return Ok(op.apply(a, b).map(Expr::nat)),
        };
        Ok(Some(self.builtin(
            if value { BOOL_TRUE } else { BOOL_FALSE },
            vec![],
        )))
    }
}
