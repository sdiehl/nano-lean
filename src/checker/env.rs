use crate::term::decl::{Constructor, Declar, Hint, Inductive, Recursor};
use crate::term::expr::Expr;
use crate::term::intern::Names;
use crate::term::level::Level;
use crate::term::names::{QUOT_IND_MAJOR, QUOT_LIFT_MAJOR};
use crate::term::ptr::{ExprPtr, LevelPtr, LevelsPtr, NamePtr};
use std::cmp::Ordering;

pub(crate) trait Decls<'t> {
    fn declar(&self, n: NamePtr<'t>) -> Option<Declar<'t>>;

    fn names(&self) -> &Names<'t>;

    #[inline]
    fn ctor(&self, n: NamePtr<'t>) -> Option<Constructor<'t>> {
        match self.declar(n)? {
            Declar::Ctor(c) => Some(c),
            _ => None,
        }
    }

    #[inline]
    fn recursor(&self, n: NamePtr<'t>) -> Option<Recursor<'t>> {
        match self.declar(n)? {
            Declar::Rec(r) => Some(r),
            _ => None,
        }
    }

    #[inline]
    fn hint(&self, n: NamePtr<'t>, ls: LevelsPtr<'t>) -> Option<Hint> {
        let d = self.declar(n)?;
        let (_, h) = d.unfoldable()?;
        (ls.len() == d.uparams().len()).then_some(h)
    }

    fn single_ctor(&self, n: NamePtr<'t>) -> Option<(Inductive<'t>, Constructor<'t>)> {
        let Some(Declar::Ind(i)) = self.declar(n) else {
            return None;
        };
        if i.ctors.len() != 1 || i.num_indices != 0 {
            return None;
        }
        Some((i, self.ctor(i.ctors[0])?))
    }

    #[inline]
    fn structure_like(&self, n: NamePtr<'t>) -> Option<(Inductive<'t>, Constructor<'t>)> {
        self.single_ctor(n).filter(|(i, _)| !i.is_rec)
    }

    #[inline]
    fn struct_ctor(&self, n: NamePtr<'t>, nargs: usize) -> Option<Constructor<'t>> {
        let c = self.ctor(n)?;
        (nargs == usize::from(c.num_params) + usize::from(c.num_fields)
            && self.structure_like(c.induct).is_some())
        .then_some(c)
    }

    #[inline]
    fn unit_struct(&self, n: NamePtr<'t>) -> bool {
        self.structure_like(n)
            .is_some_and(|(_, c)| c.num_fields == 0)
    }

    #[inline]
    fn rec_induct(&self, rec: &Recursor<'t>) -> Option<NamePtr<'t>> {
        match self.declar(rec.rules.first()?.ctor)? {
            Declar::Ctor(c) => Some(c.induct),
            _ => None,
        }
    }

    #[inline]
    fn quot_major(&self, n: NamePtr<'t>) -> Option<usize> {
        let names = self.names();
        let major = if Some(n) == names.quot_lift {
            QUOT_LIFT_MAJOR
        } else if Some(n) == names.quot_ind {
            QUOT_IND_MAJOR
        } else {
            return None;
        };
        matches!(self.declar(n)?, Declar::Quot(_)).then_some(major)
    }
}

/// Which side lazy delta unfolds first: `Less` unfolds the left.
#[inline]
pub(crate) fn unfold_order(t: Hint, s: Hint) -> Ordering {
    match (t, s) {
        (Hint::Regular(a), Hint::Regular(b)) => b.cmp(&a),
        (Hint::Opaque, Hint::Opaque) | (Hint::Abbrev, Hint::Abbrev) => Ordering::Equal,
        (Hint::Opaque, _) | (_, Hint::Abbrev) => Ordering::Greater,
        (_, Hint::Opaque) | (Hint::Abbrev, _) => Ordering::Less,
    }
}

pub(crate) fn positive(l: LevelPtr<'_>) -> bool {
    match *l {
        Level::Succ(..) => true,
        Level::Max(a, b, _) => positive(a) || positive(b),
        Level::IMax(_, b, _) => positive(b),
        _ => false,
    }
}

#[inline]
pub(crate) fn strip_pis(mut ty: ExprPtr<'_>, n: usize) -> Option<ExprPtr<'_>> {
    for _ in 0..n {
        let Expr::Pi { body, .. } = *ty else {
            return None;
        };
        ty = body;
    }
    Some(ty)
}
