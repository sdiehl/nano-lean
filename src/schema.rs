use crate::error::{Result, invalid};
use serde_json::Value;

pub const FORMAT_VERSION: &str = "3.1.0";
/// Adds the per-inductive feature flags.
pub const FLAGS_VERSION: &str = "3.2.0";
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

pub(crate) fn array(v: &Value) -> Result<&[Value]> {
    v.as_array()
        .map(Vec::as_slice)
        .ok_or_else(|| invalid("expected array"))
}

pub(crate) fn string(v: &Value) -> Result<&str> {
    v.as_str().ok_or_else(|| invalid("expected string"))
}

pub(crate) fn boolean(v: &Value) -> Result<bool> {
    v.as_bool().ok_or_else(|| invalid("expected boolean"))
}
