//! The checkers reduce `Nat` and `String` primitives by name, as Lean's kernel does, so the
//! declarations behind those names must have the types the reductions assume. Bodies are
//! trusted, exactly as in Lean.

use crate::error::{Result, invalid};
use crate::term::expr::Expr;
use crate::term::intern::{Names, Store};
use crate::term::level::Level;
use crate::term::ptr::{ExprPtr, LevelPtr, NamePtr};

#[derive(Clone, Copy)]
enum L {
    Zero,
    U,
}

enum P {
    Sort(L),
    Var(u16),
    Nat,
    Bool,
    Char,
    Str,
    List(L, Box<P>),
    Pi(Box<P>, Box<P>),
}

fn arrow(a: P, b: P) -> P {
    P::Pi(Box::new(a), Box::new(b))
}

fn list(l: L, a: P) -> P {
    P::List(l, Box::new(a))
}

struct Cx<'a> {
    names: &'a Names<'a>,
    zero: LevelPtr<'a>,
    u: Option<LevelPtr<'a>>,
}

impl<'a> Cx<'a> {
    fn level(&self, l: L) -> Option<LevelPtr<'a>> {
        match l {
            L::Zero => Some(self.zero),
            L::U => self.u,
        }
    }

    fn konst(&self, e: ExprPtr<'a>, n: Option<NamePtr<'a>>, l: Option<L>) -> bool {
        match *e {
            Expr::Const { name, levels, .. } if Some(name) == n => match l {
                None => levels.is_empty(),
                Some(l) => levels.len() == 1 && Some(levels[0]) == self.level(l),
            },
            _ => false,
        }
    }

    fn fits(&self, e: ExprPtr<'a>, p: &P) -> bool {
        match p {
            P::Sort(l) => matches!(*e, Expr::Sort { level, .. }
                if matches!(*level, Level::Succ(x, _) if Some(x) == self.level(*l))),
            P::Var(i) => matches!(*e, Expr::Var { idx, .. } if idx == *i),
            P::Nat => self.konst(e, self.names.nat, None),
            P::Bool => self.konst(e, self.names.bool, None),
            P::Char => self.konst(e, self.names.char, None),
            P::Str => self.konst(e, self.names.string, None),
            P::List(l, a) => matches!(*e, Expr::App { fun, arg, .. }
                if self.konst(fun, self.names.list, Some(*l)) && self.fits(arg, a)),
            P::Pi(a, b) => matches!(*e, Expr::Pi { ty, body, .. }
                if self.fits(ty, a) && self.fits(body, b)),
        }
    }
}

pub(super) fn check(store: &Store<'_>) -> Result<()> {
    use L::{U, Zero};
    use P::{Bool, Char, Nat, Sort, Str, Var};
    let n = &store.names;
    let binary = || arrow(Nat, arrow(Nat, Nat));
    let table = [
        (n.nat, 0, Sort(Zero)),
        (n.nat_zero, 0, Nat),
        (n.nat_succ, 0, arrow(Nat, Nat)),
        (n.nat_add, 0, binary()),
        (n.nat_sub, 0, binary()),
        (n.nat_mul, 0, binary()),
        (n.nat_pow, 0, binary()),
        (n.nat_mod, 0, binary()),
        (n.nat_div, 0, binary()),
        (n.nat_gcd, 0, binary()),
        (n.nat_land, 0, binary()),
        (n.nat_lor, 0, binary()),
        (n.nat_xor, 0, binary()),
        (n.nat_shl, 0, binary()),
        (n.nat_shr, 0, binary()),
        (n.nat_beq, 0, arrow(Nat, arrow(Nat, Bool))),
        (n.nat_ble, 0, arrow(Nat, arrow(Nat, Bool))),
        (n.bool, 0, Sort(Zero)),
        (n.bool_true, 0, Bool),
        (n.bool_false, 0, Bool),
        (n.char, 0, Sort(Zero)),
        (n.char_of_nat, 0, arrow(Nat, Char)),
        (n.string, 0, Sort(Zero)),
        (n.string_of_list, 0, arrow(list(Zero, Char), Str)),
        (n.list, 1, arrow(Sort(U), Sort(U))),
        (n.list_nil, 1, arrow(Sort(U), list(U, Var(0)))),
        (
            n.list_cons,
            1,
            arrow(
                Sort(U),
                arrow(Var(0), arrow(list(U, Var(1)), list(U, Var(2)))),
            ),
        ),
    ];
    for (name, params, shape) in table {
        let Some(i) = name.and_then(|n| n.decl_idx()) else {
            continue;
        };
        let d = &store.declars[i as usize];
        let uparams = d.uparams();
        let cx = Cx {
            names: n,
            zero: store.zero,
            u: uparams.first().copied(),
        };
        if uparams.len() != params || !cx.fits(d.ty(), &shape) {
            return Err(invalid(format!("reserved primitive name {}", d.name())));
        }
    }
    Ok(())
}
