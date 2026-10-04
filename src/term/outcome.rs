//! Checking failures unwind as panics carrying one of two payloads and are
//! classified at the declaration boundary. Any other panic is an internal error.

use std::any::Any;
use std::panic::{AssertUnwindSafe, catch_unwind};

pub struct Reject(pub String);
pub struct Decline(pub String);

/// Internal control flow: an inconclusive speculative comparison.
pub(crate) struct ProbeExhausted;

#[macro_export]
macro_rules! reject {
    ($($a:tt)+) => { ::std::panic::panic_any($crate::term::outcome::Reject(::std::format!($($a)+))) };
}

#[macro_export]
macro_rules! unsupported {
    ($($a:tt)+) => { ::std::panic::panic_any($crate::term::outcome::Decline(::std::format!($($a)+))) };
}

#[macro_export]
macro_rules! ensure {
    ($c:expr $(,)?) => { if !$c { $crate::reject!("check failed: {}", stringify!($c)) } };
    ($c:expr, $($a:tt)+) => { if !$c { $crate::reject!($($a)+) } };
}

pub enum Failure {
    Rejected(String),
    Declined(String),
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
            Failure::Rejected(s) | Failure::Declined(s) | Failure::Internal(s) => s,
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
                Ok(d) => Failure::Declined(d.0),
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

/// Keep rejections and declines off stderr; other panics print as usual.
pub fn install_hook() {
    let prev = std::panic::take_hook();
    std::panic::set_hook(Box::new(move |info| {
        let p = info.payload();
        if !p.is::<Reject>() && !p.is::<Decline>() && !p.is::<ProbeExhausted>() {
            prev(info);
        }
    }));
}
