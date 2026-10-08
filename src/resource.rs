use crate::kernel::Error;
use crate::term::outcome::{Decline, raise};
use std::fmt;

const STACK_RED_ZONE: usize = 256 << 10;
const STACK_SEGMENT: usize = 16 << 20;

#[inline]
pub(crate) fn grow<T>(f: impl FnOnce() -> T) -> T {
    stacker::maybe_grow(STACK_RED_ZONE, STACK_SEGMENT, f)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Budget {
    Work,
    Arena,
    Checking,
    NestedExpansion,
    UniverseComparison,
}

impl Budget {
    pub const fn message(self) -> &'static str {
        match self {
            Self::Work => "declaration work budget exhausted",
            Self::Arena => "declaration arena budget exhausted",
            Self::Checking => "checking budget exhausted",
            Self::NestedExpansion => "checking budget exhausted during nested expansion",
            Self::UniverseComparison => "universe comparison budget exhausted",
        }
    }

    #[cold]
    #[inline(never)]
    pub(crate) fn decline(self) -> ! {
        raise(Decline::Exhausted(self))
    }
}

impl fmt::Display for Budget {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.message())
    }
}

impl From<Budget> for Error {
    #[cold]
    #[inline(never)]
    fn from(budget: Budget) -> Self {
        Error::Exhausted(budget)
    }
}
