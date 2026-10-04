use super::ptr::{ExprPtr, LevelsPtr, NamePtr};

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Hint {
    Opaque,
    Abbrev,
    Regular(u32),
}

impl Hint {
    /// Unfold the side with the smaller hint first.
    pub fn lt(self, o: Hint) -> bool {
        match (self, o) {
            (_, Hint::Opaque) | (Hint::Abbrev, _) => false,
            (Hint::Opaque, _) | (_, Hint::Abbrev) => true,
            (Hint::Regular(a), Hint::Regular(b)) => a < b,
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub struct Info<'a> {
    pub name: NamePtr<'a>,
    pub uparams: LevelsPtr<'a>,
    pub ty: ExprPtr<'a>,
}

#[derive(Clone, Copy, Debug)]
pub struct RecRule<'a> {
    pub ctor: NamePtr<'a>,
    pub nfields: u16,
    pub rhs: ExprPtr<'a>,
}

#[derive(Clone, Copy, Debug)]
pub struct Inductive<'a> {
    pub info: Info<'a>,
    pub is_rec: bool,
    pub is_nested: bool,
    pub num_nested: usize,
    pub is_reflexive: bool,
    pub num_params: u16,
    pub num_indices: u16,
    pub all: &'a [NamePtr<'a>],
    pub ctors: &'a [NamePtr<'a>],
}

#[derive(Clone, Copy, Debug)]
pub struct Constructor<'a> {
    pub info: Info<'a>,
    pub induct: NamePtr<'a>,
    pub cidx: u16,
    pub num_params: u16,
    pub num_fields: u16,
}

#[derive(Clone, Copy, Debug)]
pub struct Recursor<'a> {
    pub info: Info<'a>,
    pub all: &'a [NamePtr<'a>],
    pub num_params: u16,
    pub num_indices: u16,
    pub num_motives: u16,
    pub num_minors: u16,
    pub rules: &'a [RecRule<'a>],
    pub is_k: bool,
}

impl Recursor<'_> {
    pub fn major_idx(&self) -> usize {
        usize::from(self.num_params)
            + usize::from(self.num_motives)
            + usize::from(self.num_minors)
            + usize::from(self.num_indices)
    }
}

#[derive(Clone, Copy, Debug)]
pub enum Declar<'a> {
    Axiom(Info<'a>),
    Quot(Info<'a>),
    Thm(Info<'a>, ExprPtr<'a>),
    Def(Info<'a>, ExprPtr<'a>, Hint),
    Opaque(Info<'a>, ExprPtr<'a>),
    Ind(Inductive<'a>),
    Ctor(Constructor<'a>),
    Rec(Recursor<'a>),
}

impl<'a> Declar<'a> {
    pub fn info(&self) -> &Info<'a> {
        match self {
            Declar::Axiom(i)
            | Declar::Quot(i)
            | Declar::Thm(i, _)
            | Declar::Def(i, ..)
            | Declar::Opaque(i, _) => i,
            Declar::Ind(d) => &d.info,
            Declar::Ctor(d) => &d.info,
            Declar::Rec(d) => &d.info,
        }
    }

    pub fn name(&self) -> NamePtr<'a> {
        self.info().name
    }

    pub fn uparams(&self) -> LevelsPtr<'a> {
        self.info().uparams
    }

    pub fn ty(&self) -> ExprPtr<'a> {
        self.info().ty
    }

    /// Value the kernel may unfold, with its reducibility hint.
    pub fn unfoldable(&self) -> Option<(ExprPtr<'a>, Hint)> {
        match self {
            Declar::Def(_, v, h) => Some((*v, *h)),
            Declar::Thm(_, v) => Some((*v, Hint::Opaque)),
            _ => None,
        }
    }

    pub fn kind(&self) -> &'static str {
        match self {
            Declar::Axiom(_) => "axiom",
            Declar::Quot(_) => "quotient",
            Declar::Thm(..) => "theorem",
            Declar::Def(..) => "definition",
            Declar::Opaque(..) => "opaque",
            Declar::Ind(_) => "inductive",
            Declar::Ctor(_) => "constructor",
            Declar::Rec(_) => "recursor",
        }
    }
}
