use super::{Checker, Error, Result, inductive::spine};
use crate::{Expr, Level};
use num_bigint::BigUint;
use num_integer::Integer;
use num_traits::{ToPrimitive, Zero};

impl Checker<'_> {
    // Export names preserve segment boundaries. The text frontend uses dotted names.
    pub(super) fn builtin_name(&self, path: &str) -> String {
        let encoded = serde_json::to_string(&path.split('.').collect::<Vec<_>>()).unwrap();
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
            return Err(Error(format!("invalid literal type: {path}")));
        }
        Ok(ty)
    }

    pub(super) fn nat_constructor(&self, n: &BigUint) -> Expr {
        if n.is_zero() {
            self.builtin("Nat.zero", vec![])
        } else {
            self.builtin("Nat.succ", vec![]).app(Expr::nat(n - 1u32))
        }
    }

    pub(super) fn nat_literal_eq(&mut self, n: &BigUint, other: &Expr) -> Result<bool> {
        let (head, args) = spine(other);
        if let Expr::Const(name, levels) = head {
            if !levels.is_empty() {
                return Ok(false);
            }
            if name == self.builtin_name("Nat.zero") && args.is_empty() {
                return Ok(n.is_zero());
            }
            if name == self.builtin_name("Nat.succ") && args.len() == 1 && !n.is_zero() {
                return self.conv(&Expr::nat(n - 1u32), &args[0]);
            }
        }
        Ok(false)
    }

    pub(super) fn string_constructor(&mut self, s: &str) -> Result<Expr> {
        let char_ty = self.builtin("Char", vec![]);
        let mut list = self
            .builtin("List.nil", vec![Level::Nat(0)])
            .app(char_ty.clone());
        let cons = self.builtin("List.cons", vec![Level::Nat(0)]).app(char_ty);
        for ch in s.chars().rev() {
            self.tick()?;
            let value = self.builtin("Char.ofNat", vec![]).app(Expr::nat(ch as u32));
            list = cons.clone().app(value).app(list);
        }
        Ok(self.builtin("String.ofList", vec![]).app(list))
    }

    fn natural_value(&mut self, e: &Expr) -> Result<Option<BigUint>> {
        Ok(match self.whnf(e)? {
            Expr::Nat(n) => Some(n.0),
            Expr::Const(n, us) if us.is_empty() && n == self.builtin_name("Nat.zero") => {
                Some(BigUint::ZERO)
            }
            _ => None,
        })
    }

    pub(super) fn reduce_primitive(&mut self, head: &Expr, args: &[Expr]) -> Result<Option<Expr>> {
        let Expr::Const(name, levels) = head else {
            return Ok(None);
        };
        if !levels.is_empty() {
            return Ok(None);
        }
        if args.len() == 1 && matches!(name.as_str(), "Nat.succ" | "[\"Nat\",\"succ\"]") {
            return Ok(self.natural_value(&args[0])?.map(|n| Expr::nat(n + 1u32)));
        }
        if args.len() != 2 {
            return Ok(None);
        }
        let op = match name.as_str() {
            "Nat.add" | "[\"Nat\",\"add\"]" => "add",
            "Nat.sub" | "[\"Nat\",\"sub\"]" => "sub",
            "Nat.mul" | "[\"Nat\",\"mul\"]" => "mul",
            "Nat.pow" | "[\"Nat\",\"pow\"]" => "pow",
            "Nat.div" | "[\"Nat\",\"div\"]" => "div",
            "Nat.mod" | "[\"Nat\",\"mod\"]" => "mod",
            "Nat.gcd" | "[\"Nat\",\"gcd\"]" => "gcd",
            "Nat.beq" | "[\"Nat\",\"beq\"]" => "beq",
            "Nat.ble" | "[\"Nat\",\"ble\"]" => "ble",
            "Nat.land" | "[\"Nat\",\"land\"]" => "land",
            "Nat.lor" | "[\"Nat\",\"lor\"]" => "lor",
            "Nat.xor" | "[\"Nat\",\"xor\"]" => "xor",
            "Nat.shiftLeft" | "[\"Nat\",\"shiftLeft\"]" => "shiftLeft",
            "Nat.shiftRight" | "[\"Nat\",\"shiftRight\"]" => "shiftRight",
            _ => return Ok(None),
        };
        let Some(a) = self.natural_value(&args[0])? else {
            return Ok(None);
        };
        let Some(b) = self.natural_value(&args[1])? else {
            return Ok(None);
        };
        let resource_limit =
            || Error("unsupported: natural operation result exceeds resource limit".into());
        // Bound allocations from a tiny exponent/shift expression; never accept a skipped reduction.
        const MAX_RESULT_BITS: u64 = 1 << 26;
        let result = match op {
            "add" => a + b,
            "sub" => {
                if a >= b {
                    a - b
                } else {
                    BigUint::ZERO
                }
            }
            "mul" => a * b,
            "div" => {
                if b.is_zero() {
                    BigUint::ZERO
                } else {
                    a / b
                }
            }
            "mod" => {
                if b.is_zero() {
                    a
                } else {
                    a % b
                }
            }
            "gcd" => a.gcd(&b),
            "land" => a & b,
            "lor" => a | b,
            "xor" => a ^ b,
            "beq" | "ble" => {
                let value = if op == "beq" { a == b } else { a <= b };
                return Ok(Some(
                    self.builtin(if value { "Bool.true" } else { "Bool.false" }, vec![]),
                ));
            }
            "pow" => {
                if b.is_zero() || a == BigUint::from(1u32) {
                    BigUint::from(1u32)
                } else if a.is_zero() {
                    BigUint::ZERO
                } else {
                    let exp = b.to_u32().ok_or_else(resource_limit)?;
                    if a.bits().saturating_mul(u64::from(exp)) > MAX_RESULT_BITS {
                        return Err(resource_limit());
                    }
                    a.pow(exp)
                }
            }
            "shiftLeft" => {
                if a.is_zero() {
                    BigUint::ZERO
                } else {
                    let shift = b.to_u64().ok_or_else(resource_limit)?;
                    if a.bits().saturating_add(shift) > MAX_RESULT_BITS {
                        return Err(resource_limit());
                    }
                    a << usize::try_from(shift).map_err(|_| resource_limit())?
                }
            }
            "shiftRight" => {
                if b >= BigUint::from(a.bits()) {
                    BigUint::ZERO
                } else {
                    a >> b.to_usize().ok_or_else(resource_limit)?
                }
            }
            _ => unreachable!(),
        };
        Ok(Some(Expr::nat(result)))
    }
}
