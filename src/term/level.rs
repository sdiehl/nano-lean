use super::ptr::{LevelPtr, LevelsPtr, NamePtr};

pub const ZERO_HASH: u64 = 283;
pub const SUCC_HASH: u64 = 541;
pub const MAX_HASH: u64 = 1091;
pub const IMAX_HASH: u64 = 1747;
pub const PARAM_HASH: u64 = 947;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Level<'a> {
    Zero,
    Succ(LevelPtr<'a>, u64),
    Max(LevelPtr<'a>, LevelPtr<'a>, u64),
    IMax(LevelPtr<'a>, LevelPtr<'a>, u64),
    Param(NamePtr<'a>, u64),
}

impl Level<'_> {
    #[inline]
    pub fn get_hash(&self) -> u64 {
        match self {
            Level::Zero => ZERO_HASH,
            Level::Succ(_, h) | Level::Max(_, _, h) | Level::IMax(_, _, h) | Level::Param(_, h) => *h,
        }
    }
}

impl<'a> LevelPtr<'a> {
    pub fn is_param(self) -> bool {
        matches!(*self, Level::Param(..))
    }

    pub fn is_any_max(self) -> bool {
        matches!(*self, Level::Max(..) | Level::IMax(..))
    }

    /// Strip successors, returning the base and how many were stripped.
    pub fn succs(mut self) -> (LevelPtr<'a>, usize) {
        let mut n = 0;
        while let Level::Succ(p, _) = *self {
            self = p;
            n += 1;
        }
        (self, n)
    }

    /// Every parameter occurring in `self` is one of `params`.
    pub fn params_in(self, params: LevelsPtr<'a>) -> bool {
        match *self {
            Level::Zero => true,
            Level::Succ(l, _) => l.params_in(params),
            Level::Max(l, r, _) | Level::IMax(l, r, _) => l.params_in(params) && r.params_in(params),
            Level::Param(..) => params.contains(&self),
        }
    }
}

impl<'a> LevelsPtr<'a> {
    /// All elements are distinct parameters.
    pub fn distinct_params(self) -> bool {
        self.iter().enumerate().all(|(i, l)| l.is_param() && !self[..i].contains(l))
    }

    pub fn has_param(self, n: NamePtr<'a>) -> bool {
        self.iter().any(|l| matches!(**l, Level::Param(m, _) if m == n))
    }
}
