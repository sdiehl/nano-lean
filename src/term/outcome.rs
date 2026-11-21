//! Both checkers record their failure and return through the `R` chain, so nothing panics or
//! unwinds on a rejection or a decline.

use crate::resource::Budget;

/// Unwinds the `R` chain, never a semantic answer. A probe ran out when the checker's `fail`
/// slot is empty. Zero sized so `R<V>` keeps the pointer niche.
#[derive(Debug)]
pub struct Stop;
pub type R<T> = Result<T, Stop>;

const PROBE_ESCAPED: &str = "probe exhaustion escaped its probe";

macro_rules! reject {
    ($s:expr, $($a:tt)+) => { return ::std::result::Result::Err($s.reject(::std::format_args!($($a)+))) };
}

macro_rules! ensure {
    ($s:expr, $c:expr, $($a:tt)+) => { if !$c { $crate::reject!($s, $($a)+) } };
}

pub(crate) use {ensure, reject};

#[derive(Debug, thiserror::Error)]
pub enum Decline {
    #[error("{0}")]
    Exhausted(Budget),
    #[error("{0}")]
    Unsupported(String),
}

pub enum Failure {
    Rejected(String),
    Declined(Decline),
    Internal(String),
}

impl Failure {
    pub fn status(&self) -> &'static str {
        match self {
            Failure::Rejected(_) => "rejected",
            Failure::Declined(_) => "unsupported",
            Failure::Internal(_) => "internal",
        }
    }

    pub fn reason(&self) -> &str {
        match self {
            Failure::Rejected(s) | Failure::Internal(s) => s,
            Failure::Declined(Decline::Exhausted(b)) => b.message(),
            Failure::Declined(Decline::Unsupported(s)) => s,
        }
    }

    pub fn exit_code(&self) -> i32 {
        match self {
            Failure::Rejected(_) => 1,
            _ => 2,
        }
    }

    /// The failure behind a `Stop` that reached the top of a check.
    pub(crate) fn escaped(slot: &mut Option<Failure>) -> Failure {
        slot.take()
            .unwrap_or_else(|| Failure::Internal(PROBE_ESCAPED.to_owned()))
    }
}
