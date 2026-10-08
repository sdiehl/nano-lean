use super::{Checker, Error, Result, inductive::spine};
use crate::term::names::*;
use crate::{Expr, Level};
use num_bigint::BigUint;
use num_integer::Integer;
use num_traits::{ToPrimitive, Zero};

// Exceeding this cap is an error, never a skipped reduction.
const MAX_RESULT_BITS: u64 = 1 << 26;

pub(super) fn symbol(path: &str, encoded: bool) -> String {
    if encoded {
        serde_json::to_string(&path.split('.').collect::<Vec<_>>()).unwrap()
    } else {
        path.into()
    }
}

#[derive(Clone, Copy)]
pub(super) enum NatOp {
    Succ,
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

impl NatOp {
    pub(super) fn parse(name: &str) -> Option<Self> {
        let op = name.strip_prefix("Nat.").or_else(|| {
            name.strip_prefix("[\"Nat\",\"")
                .and_then(|n| n.strip_suffix("\"]"))
        })?;
        Some(match op {
            "succ" => Self::Succ,
            "add" => Self::Add,
            "sub" => Self::Sub,
            "mul" => Self::Mul,
            "pow" => Self::Pow,
            "div" => Self::Div,
            "mod" => Self::Mod,
            "gcd" => Self::Gcd,
            "beq" => Self::Beq,
            "ble" => Self::Ble,
            "land" => Self::Land,
            "lor" => Self::Lor,
            "xor" => Self::Xor,
            "shiftLeft" => Self::ShiftLeft,
            "shiftRight" => Self::ShiftRight,
            _ => return None,
        })
    }

    pub(super) fn arity(self) -> usize {
        if matches!(self, Self::Succ) { 1 } else { 2 }
    }

    fn apply(self, a: BigUint, b: BigUint) -> Result<BigUint> {
        let resource_limit =
            || Error::Unsupported("natural operation result exceeds resource limit".into());
        Ok(match self {
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
            Self::Pow if b.is_zero() || a == BigUint::from(1u32) => BigUint::from(1u32),
            Self::Pow if a.is_zero() => BigUint::ZERO,
            Self::Pow => {
                let exp = b.to_u32().ok_or_else(resource_limit)?;
                if a.bits().saturating_mul(u64::from(exp)) > MAX_RESULT_BITS {
                    return Err(resource_limit());
                }
                a.pow(exp)
            }
            Self::ShiftLeft if a.is_zero() => BigUint::ZERO,
            Self::ShiftLeft => {
                let shift = b.to_u64().ok_or_else(resource_limit)?;
                if a.bits().saturating_add(shift) > MAX_RESULT_BITS {
                    return Err(resource_limit());
                }
                a << usize::try_from(shift).map_err(|_| resource_limit())?
            }
            Self::ShiftRight if b >= BigUint::from(a.bits()) => BigUint::ZERO,
            Self::ShiftRight => a >> b.to_usize().ok_or_else(resource_limit)?,
            Self::Succ | Self::Beq | Self::Ble => unreachable!(),
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
        let Some(op) =
            NatOp::parse(name).filter(|op| levels.is_empty() && op.arity() == args.len())
        else {
            return Ok(None);
        };
        if let NatOp::Succ = op {
            return Ok(self.natural_value(&args[0])?.map(|n| Expr::nat(n + 1u32)));
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
            op => return Ok(Some(Expr::nat(op.apply(a, b)?))),
        };
        Ok(Some(self.builtin(
            if value { BOOL_TRUE } else { BOOL_FALSE },
            vec![],
        )))
    }
}
