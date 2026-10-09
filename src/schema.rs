pub const META: &str = "meta";

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Ref {
    Name,
    Level,
    Expr,
}

impl Ref {
    pub const ALL: [Self; 3] = [Self::Name, Self::Level, Self::Expr];

    pub const fn key(self) -> &'static str {
        match self {
            Self::Name => "in",
            Self::Level => "il",
            Self::Expr => "ie",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ExprKind {
    BVar,
    Sort,
    Const,
    App,
    Lam,
    ForallE,
    LetE,
    MData,
    Proj,
    NatVal,
    StrVal,
}

impl ExprKind {
    pub const ALL: [Self; 11] = [
        Self::BVar,
        Self::Sort,
        Self::Const,
        Self::App,
        Self::Lam,
        Self::ForallE,
        Self::LetE,
        Self::MData,
        Self::Proj,
        Self::NatVal,
        Self::StrVal,
    ];

    pub const fn key(self) -> &'static str {
        match self {
            Self::BVar => "bvar",
            Self::Sort => "sort",
            Self::Const => "const",
            Self::App => "app",
            Self::Lam => "lam",
            Self::ForallE => "forallE",
            Self::LetE => "letE",
            Self::MData => "mdata",
            Self::Proj => "proj",
            Self::NatVal => "natVal",
            Self::StrVal => "strVal",
        }
    }
}
