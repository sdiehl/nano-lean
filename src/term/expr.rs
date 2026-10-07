use super::ptr::{BigUintPtr, ExprPtr, LevelPtr, LevelsPtr, NamePtr, StringPtr};

pub const VAR_HASH: u64 = 281;
pub const SORT_HASH: u64 = 563;
pub const CONST_HASH: u64 = 1129;
pub const PROJ_HASH: u64 = 17;
pub const LAM_HASH: u64 = 431;
pub const LET_HASH: u64 = 241;
pub const PI_HASH: u64 = 719;
pub const APP_HASH: u64 = 233;
pub const STR_HASH: u64 = 1493;
pub const NAT_HASH: u64 = 1583;
pub const LOCAL_HASH: u64 = 1201;

/// A term node. Children are pointers into the same or an enclosing arena, so
/// structural equality of hash-consed nodes is pointer equality of children.
/// Loose bound variable count and a has-locals flag live in the pointer.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Expr<'a> {
    Var {
        idx: u16,
        hash: u64,
    },
    Sort {
        level: LevelPtr<'a>,
        hash: u64,
    },
    Const {
        name: NamePtr<'a>,
        levels: LevelsPtr<'a>,
        hash: u64,
    },
    App {
        fun: ExprPtr<'a>,
        arg: ExprPtr<'a>,
        hash: u64,
        sup: u32,
    },
    Lam {
        ty: ExprPtr<'a>,
        body: ExprPtr<'a>,
        hash: u64,
        sup: u32,
    },
    Pi {
        ty: ExprPtr<'a>,
        body: ExprPtr<'a>,
        hash: u64,
        sup: u32,
    },
    Let {
        data: &'a LetData<'a>,
        hash: u64,
        sup: u32,
    },
    Proj {
        name: NamePtr<'a>,
        idx: u16,
        e: ExprPtr<'a>,
        hash: u64,
        sup: u32,
    },
    NatLit {
        n: BigUintPtr<'a>,
        hash: u64,
    },
    StrLit {
        s: StringPtr<'a>,
        hash: u64,
    },
    /// A free variable introduced by the checker when it goes under a binder.
    Local {
        id: u32,
        ty: ExprPtr<'a>,
        hash: u64,
    },
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct LetData<'a> {
    pub ty: ExprPtr<'a>,
    pub val: ExprPtr<'a>,
    pub body: ExprPtr<'a>,
    pub nondep: bool,
}

impl Expr<'_> {
    #[inline]
    pub fn get_hash(&self) -> u64 {
        match self {
            Expr::Var { hash, .. }
            | Expr::Sort { hash, .. }
            | Expr::Const { hash, .. }
            | Expr::App { hash, .. }
            | Expr::Lam { hash, .. }
            | Expr::Pi { hash, .. }
            | Expr::Let { hash, .. }
            | Expr::Proj { hash, .. }
            | Expr::NatLit { hash, .. }
            | Expr::StrLit { hash, .. }
            | Expr::Local { hash, .. } => *hash,
        }
    }
}

impl<'a> ExprPtr<'a> {
    pub fn is_lambda(self) -> bool {
        matches!(*self, Expr::Lam { .. })
    }

    pub fn is_pi(self) -> bool {
        matches!(*self, Expr::Pi { .. })
    }

    pub fn const_name(self) -> Option<NamePtr<'a>> {
        match *self {
            Expr::Const { name, .. } => Some(name),
            _ => None,
        }
    }

    /// Head of an application spine.
    pub fn head(mut self) -> ExprPtr<'a> {
        while let Expr::App { fun, .. } = *self {
            self = fun;
        }
        self
    }

    pub fn num_args(mut self) -> usize {
        let mut n = 0;
        while let Expr::App { fun, .. } = *self {
            self = fun;
            n += 1;
        }
        n
    }
}

const _: () = assert!(std::mem::size_of::<Expr<'_>>() == 32);

/// Loose bound variables below 32 as a bitmask, or `WIDE` when unknown.
pub const WIDE: u32 = u32::MAX;

impl ExprPtr<'_> {
    #[inline]
    pub fn sup(self) -> u32 {
        if self.closed() {
            return 0;
        }
        match *self {
            Expr::Var { idx, .. } if idx < 32 => 1 << idx,
            Expr::App { sup, .. }
            | Expr::Lam { sup, .. }
            | Expr::Pi { sup, .. }
            | Expr::Let { sup, .. }
            | Expr::Proj { sup, .. } => sup,
            _ => WIDE,
        }
    }
}

#[inline]
fn sup_join(parts: &[u32], nlb: u16) -> u32 {
    if nlb > 32 || parts.contains(&WIDE) {
        WIDE
    } else {
        parts.iter().fold(0, |a, &b| a | b)
    }
}

#[inline]
fn sup_under(body: ExprPtr<'_>) -> u32 {
    match body.sup() {
        WIDE => WIDE,
        s => s >> 1,
    }
}

/// Pointer metadata: loose bound variable count in the low 15 bits, has-locals on top.
pub type Meta = u16;
pub const HAS_LOCAL: Meta = 1 << 15;

#[inline]
fn join(a: ExprPtr<'_>, b: ExprPtr<'_>) -> Meta {
    a.nlb().max(b.nlb()) | ((a.meta() | b.meta()) & HAS_LOCAL)
}

#[inline]
fn under(ty: ExprPtr<'_>, body: ExprPtr<'_>) -> Meta {
    ty.nlb().max(body.nlb().saturating_sub(1)) | ((ty.meta() | body.meta()) & HAS_LOCAL)
}

/// Pure node builders: the node plus its pointer metadata.
pub mod mk {
    use super::*;
    use crate::hash64;

    pub fn var<'a>(idx: u16) -> (Expr<'a>, Meta) {
        debug_assert!(idx < HAS_LOCAL - 1);
        (
            Expr::Var {
                idx,
                hash: hash64!(VAR_HASH, idx),
            },
            idx + 1,
        )
    }

    pub fn sort(level: LevelPtr<'_>) -> (Expr<'_>, Meta) {
        (
            Expr::Sort {
                level,
                hash: hash64!(SORT_HASH, level),
            },
            0,
        )
    }

    pub fn konst<'a>(name: NamePtr<'a>, levels: LevelsPtr<'a>) -> (Expr<'a>, Meta) {
        (
            Expr::Const {
                name,
                levels,
                hash: hash64!(CONST_HASH, name, levels),
            },
            0,
        )
    }

    pub fn app<'a>(fun: ExprPtr<'a>, arg: ExprPtr<'a>) -> (Expr<'a>, Meta) {
        (
            Expr::App {
                fun,
                arg,
                hash: hash64!(APP_HASH, fun, arg),
                sup: sup_join(&[fun.sup(), arg.sup()], join(fun, arg) & 0x7fff),
            },
            join(fun, arg),
        )
    }

    pub fn lam<'a>(ty: ExprPtr<'a>, body: ExprPtr<'a>) -> (Expr<'a>, Meta) {
        (
            Expr::Lam {
                ty,
                body,
                hash: hash64!(LAM_HASH, ty, body),
                sup: sup_join(&[ty.sup(), sup_under(body)], under(ty, body) & 0x7fff),
            },
            under(ty, body),
        )
    }

    pub fn pi<'a>(ty: ExprPtr<'a>, body: ExprPtr<'a>) -> (Expr<'a>, Meta) {
        (
            Expr::Pi {
                ty,
                body,
                hash: hash64!(PI_HASH, ty, body),
                sup: sup_join(&[ty.sup(), sup_under(body)], under(ty, body) & 0x7fff),
            },
            under(ty, body),
        )
    }

    /// Hash, support and metadata of a let node; the caller allocates the payload on a miss.
    pub fn let_(d: LetData<'_>) -> (u64, u32, Meta) {
        let hash = hash64!(LET_HASH, d.ty, d.val, d.body, d.nondep);
        let nlb =
            d.ty.nlb()
                .max(d.val.nlb())
                .max(d.body.nlb().saturating_sub(1));
        (
            hash,
            sup_join(&[d.ty.sup(), d.val.sup(), sup_under(d.body)], nlb),
            nlb | ((d.ty.meta() | d.val.meta() | d.body.meta()) & HAS_LOCAL),
        )
    }

    pub fn proj<'a>(name: NamePtr<'a>, idx: u16, e: ExprPtr<'a>) -> (Expr<'a>, Meta) {
        (
            Expr::Proj {
                name,
                idx,
                e,
                hash: hash64!(PROJ_HASH, name, idx, e),
                sup: e.sup(),
            },
            e.meta(),
        )
    }

    pub fn nat(n: BigUintPtr<'_>) -> (Expr<'_>, Meta) {
        (
            Expr::NatLit {
                n,
                hash: hash64!(NAT_HASH, n),
            },
            0,
        )
    }

    pub fn str(s: StringPtr<'_>) -> (Expr<'_>, Meta) {
        (
            Expr::StrLit {
                s,
                hash: hash64!(STR_HASH, s),
            },
            0,
        )
    }

    pub fn local<'a>(id: u32, ty: ExprPtr<'a>) -> (Expr<'a>, Meta) {
        (
            Expr::Local {
                id,
                ty,
                hash: hash64!(LOCAL_HASH, id),
            },
            HAS_LOCAL,
        )
    }
}
