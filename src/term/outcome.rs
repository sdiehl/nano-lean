//! Checking failures unwind as panics with a `Reject` or `Decline` payload. Others are internal
//! errors. This is a performance decision: failure is rare and fatal to the declaration, so
//! unwinding keeps every evaluation and conversion step free of a `Result` branch.

use crate::resource::Budget;
use std::any::Any;
use std::panic::{AssertUnwindSafe, catch_unwind};

pub struct Reject(pub String);

#[derive(Debug, thiserror::Error)]
pub enum Decline {
    #[error("{0}")]
    Exhausted(Budget),
    #[error("{0}")]
    Unsupported(String),
}

pub(crate) struct ProbeExhausted;

#[macro_export]
macro_rules! reject {
    ($($a:tt)+) => { ::std::panic::panic_any($crate::term::outcome::Reject(::std::format!($($a)+))) };
}

#[macro_export]
macro_rules! unsupported {
    ($($a:tt)+) => { ::std::panic::panic_any($crate::term::outcome::Decline::Unsupported(::std::format!($($a)+))) };
}

#[macro_export]
macro_rules! ensure {
    ($c:expr $(,)?) => { if !$c { $crate::reject!("check failed: {}", stringify!($c)) } };
    ($c:expr, $($a:tt)+) => { if !$c { $crate::reject!($($a)+) } };
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

    pub fn from_panic(p: Box<dyn Any + Send>) -> Self {
        match p.downcast::<Reject>() {
            Ok(r) => Failure::Rejected(r.0),
            Err(p) => match p.downcast::<Decline>() {
                Ok(d) => Failure::Declined(*d),
                Err(p) => Failure::Internal(
                    p.downcast_ref::<String>()
                        .cloned()
                        .or_else(|| p.downcast_ref::<&str>().map(|s| (*s).to_owned()))
                        .unwrap_or_else(|| "unknown panic".to_owned()),
                ),
            },
        }
    }
}

pub fn run<T>(f: impl FnOnce() -> T) -> Result<T, Failure> {
    catch_unwind(AssertUnwindSafe(f)).map_err(Failure::from_panic)
}

pub fn install_hook() {
    let prev = std::panic::take_hook();
    std::panic::set_hook(Box::new(move |info| {
        let p = info.payload();
        if !p.is::<Reject>() && !p.is::<Decline>() && !p.is::<ProbeExhausted>() {
            prev(info);
        }
    }));
}
