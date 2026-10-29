//! Compares the declarations the checkers reduce by name, and the closure of their types and
//! definition bodies, with a trusted export, as Lean's comparator does. Theorem and opaque
//! values are checked, never unfolded, so only their types are compared.

use super::{Result, invalid};
use crate::term::FxHashSet;
use crate::term::decl::{Declar, Info};
use crate::term::expr::Expr;
use crate::term::intern::Store;
use crate::term::level::Level;
use crate::term::name::Name;
use crate::term::ptr::{ExprPtr, LevelPtr, LevelsPtr, NamePtr};

struct Cmp<'a, 'b> {
    target: &'a Store<'a>,
    reference: &'b Store<'b>,
    names: FxHashSet<(NamePtr<'a>, NamePtr<'b>)>,
    exprs: FxHashSet<(ExprPtr<'a>, ExprPtr<'b>)>,
    queued: FxHashSet<(NamePtr<'a>, NamePtr<'b>)>,
    todo: Vec<(NamePtr<'a>, NamePtr<'b>)>,
}

impl<'a, 'b> Cmp<'a, 'b> {
    fn name(&mut self, a: NamePtr<'a>, b: NamePtr<'b>) -> bool {
        if self.names.contains(&(a, b)) {
            return true;
        }
        let ok = match (a.kind, b.kind) {
            (Name::Anon, Name::Anon) => true,
            (Name::Str(p, s, _), Name::Str(q, t, _)) => s.s == t.s && self.name(p, q),
            (Name::Num(p, n, _), Name::Num(q, m, _)) => n == m && self.name(p, q),
            _ => false,
        };
        if ok {
            self.names.insert((a, b));
        }
        ok
    }

    fn konst(&mut self, a: NamePtr<'a>, b: NamePtr<'b>) -> bool {
        if !self.name(a, b) {
            return false;
        }
        if self.queued.insert((a, b)) {
            self.todo.push((a, b));
        }
        true
    }

    fn konsts(&mut self, a: &[NamePtr<'a>], b: &[NamePtr<'b>]) -> bool {
        a.len() == b.len() && a.iter().zip(b).all(|(&x, &y)| self.konst(x, y))
    }

    fn level(&mut self, a: LevelPtr<'a>, b: LevelPtr<'b>) -> bool {
        match (*a, *b) {
            (Level::Zero, Level::Zero) => true,
            (Level::Succ(x, _), Level::Succ(y, _)) => self.level(x, y),
            (Level::Max(x, y, _), Level::Max(z, w, _))
            | (Level::IMax(x, y, _), Level::IMax(z, w, _)) => self.level(x, z) && self.level(y, w),
            (Level::Param(n, _), Level::Param(m, _)) => self.name(n, m),
            _ => false,
        }
    }

    fn levels(&mut self, a: LevelsPtr<'a>, b: LevelsPtr<'b>) -> bool {
        a.len() == b.len() && a.iter().zip(b.iter()).all(|(&x, &y)| self.level(x, y))
    }

    fn expr(&mut self, a: ExprPtr<'a>, b: ExprPtr<'b>) -> bool {
        if self.exprs.contains(&(a, b)) {
            return true;
        }
        let ok = match (*a, *b) {
            (Expr::Var { idx: i, .. }, Expr::Var { idx: j, .. }) => i == j,
            (Expr::Sort { level: l, .. }, Expr::Sort { level: m, .. }) => self.level(l, m),
            (
                Expr::Const {
                    name: n, levels: l, ..
                },
                Expr::Const {
                    name: m, levels: k, ..
                },
            ) => self.konst(n, m) && self.levels(l, k),
            (Expr::App { fun: f, arg: x, .. }, Expr::App { fun: g, arg: y, .. })
            | (Expr::Lam { ty: f, body: x, .. }, Expr::Lam { ty: g, body: y, .. })
            | (Expr::Pi { ty: f, body: x, .. }, Expr::Pi { ty: g, body: y, .. }) => {
                self.expr(f, g) && self.expr(x, y)
            }
            (Expr::Let { data: d, .. }, Expr::Let { data: e, .. }) => {
                self.expr(d.ty, e.ty) && self.expr(d.val, e.val) && self.expr(d.body, e.body)
            }
            (
                Expr::Proj {
                    name: n, idx: i, e, ..
                },
                Expr::Proj {
                    name: m,
                    idx: j,
                    e: f,
                    ..
                },
            ) => i == j && self.konst(n, m) && self.expr(e, f),
            (Expr::NatLit { n, .. }, Expr::NatLit { n: m, .. }) => *n == *m,
            (Expr::StrLit { s, .. }, Expr::StrLit { s: t, .. }) => s.s == t.s,
            _ => false,
        };
        if ok {
            self.exprs.insert((a, b));
        }
        ok
    }

    fn info(&mut self, a: &Info<'a>, b: &Info<'b>) -> bool {
        a.uparams.len() == b.uparams.len()
            && a.uparams
                .iter()
                .zip(b.uparams.iter())
                .all(|(&x, &y)| self.level(x, y))
            && self.expr(a.ty, b.ty)
    }

    fn declar(&mut self, a: Declar<'a>, b: Declar<'b>) -> bool {
        use Declar::{Axiom, Ctor, Def, Ind, Opaque, Quot, Rec, Thm};
        self.info(a.info(), b.info())
            && match (a, b) {
                (Axiom(_), Axiom(_))
                | (Quot(_), Quot(_))
                | (Thm(..), Thm(..))
                | (Opaque(..), Opaque(..)) => true,
                (Def(_, v, _), Def(_, w, _)) => self.expr(v, w),
                (Ind(x), Ind(y)) => {
                    (x.num_params, x.num_indices, x.is_rec, x.is_reflexive)
                        == (y.num_params, y.num_indices, y.is_rec, y.is_reflexive)
                        && self.konsts(x.all, y.all)
                        && self.konsts(x.ctors, y.ctors)
                }
                (Ctor(x), Ctor(y)) => {
                    (x.cidx, x.num_params, x.num_fields) == (y.cidx, y.num_params, y.num_fields)
                        && self.konst(x.induct, y.induct)
                }
                (Rec(x), Rec(y)) => {
                    (
                        x.num_params,
                        x.num_indices,
                        x.num_motives,
                        x.num_minors,
                        x.is_k,
                    ) == (
                        y.num_params,
                        y.num_indices,
                        y.num_motives,
                        y.num_minors,
                        y.is_k,
                    ) && self.konsts(x.all, y.all)
                        && x.rules.len() == y.rules.len()
                        && x.rules.iter().zip(y.rules).all(|(r, s)| {
                            r.nfields == s.nfields
                                && self.konst(r.ctor, s.ctor)
                                && self.expr(r.rhs, s.rhs)
                        })
                }
                _ => false,
            }
    }
}

pub(super) fn compare(target: &Store<'_>, reference: &Store<'_>) -> Result<()> {
    let mut c = Cmp {
        target,
        reference,
        names: FxHashSet::default(),
        exprs: FxHashSet::default(),
        queued: FxHashSet::default(),
        todo: Vec::new(),
    };
    for ((path, a), (_, b)) in target.names.all().into_iter().zip(reference.names.all()) {
        let Some(a) = a.filter(|a| a.decl_idx().is_some()) else {
            continue;
        };
        let Some(b) = b else {
            return invalid(format!("{path} is not in the trusted prelude"));
        };
        c.konst(a, b);
    }
    while let Some((a, b)) = c.todo.pop() {
        // An undeclared name fails wherever the target uses it.
        let Some(i) = a.decl_idx() else {
            continue;
        };
        let Some(j) = b.decl_idx() else {
            return invalid(format!("{a} is not in the trusted prelude"));
        };
        let (x, y) = (
            c.target.declars[i as usize],
            c.reference.declars[j as usize],
        );
        if !c.declar(x, y) {
            return invalid(format!("{a} differs from the trusted prelude"));
        }
    }
    Ok(())
}
