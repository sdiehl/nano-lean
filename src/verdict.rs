//! Run one export through every checker so their verdicts can be compared.

use crate::checker::{self, Adapter, Limits};
use crate::export::{ExportError, check_export};
use crate::term::{arena::Arena, outcome::Failure};
use crate::{import, value_checker};
use std::fmt;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Verdict {
    Accepted,
    Rejected(String),
    Unsupported(String),
    Internal(String),
}

impl Verdict {
    pub fn accepted(&self) -> bool {
        matches!(self, Self::Accepted)
    }
    pub fn rejected(&self) -> bool {
        matches!(self, Self::Rejected(_))
    }
}

impl fmt::Display for Verdict {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Accepted => f.write_str("accepted"),
            Self::Rejected(s) => write!(f, "rejected: {s}"),
            Self::Unsupported(s) => write!(f, "unsupported: {s}"),
            Self::Internal(s) => write!(f, "internal: {s}"),
        }
    }
}

impl From<Failure> for Verdict {
    fn from(f: Failure) -> Self {
        match f {
            Failure::Rejected(s) => Self::Rejected(s),
            Failure::Declined(s) => Self::Unsupported(s),
            Failure::Internal(s) => Self::Internal(s),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Verdicts {
    pub reference: Verdict,
    pub fast: Verdict,
    pub value: Verdict,
}

impl Verdicts {
    pub fn all(&self) -> [(&'static str, &Verdict); 3] {
        [
            ("reference", &self.reference),
            ("fast", &self.fast),
            ("value", &self.value),
        ]
    }
    /// No checker crashed and none accepts what another rejects.
    pub fn agree(&self) -> bool {
        let all = self.all();
        !all.iter().any(|(_, v)| matches!(v, Verdict::Internal(_)))
            && !(all.iter().any(|(_, v)| v.accepted()) && all.iter().any(|(_, v)| v.rejected()))
    }
}

impl fmt::Display for Verdicts {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (name, v) in self.all() {
            writeln!(f, "{name}: {v}")?;
        }
        Ok(())
    }
}

fn reference(source: &str) -> Verdict {
    match crate::term::outcome::run(|| check_export(source.as_bytes())) {
        Ok(Ok(_)) => Verdict::Accepted,
        Ok(Err(ExportError::Invalid(s))) => Verdict::Rejected(s),
        Ok(Err(ExportError::Unsupported(s))) => Verdict::Unsupported(s),
        Err(f) => Verdict::Internal(f.reason().to_owned()),
    }
}

fn fast(source: &str, limits: Limits, value_core: bool) -> Verdict {
    let arena = Arena::new();
    let store = match import::import_reader(&arena, source.as_bytes(), source.len()) {
        Ok(store) => store,
        Err(import::ImportError::Invalid(s)) => return Verdict::Rejected(s),
        Err(import::ImportError::Unsupported(s)) => return Verdict::Unsupported(s),
    };
    let mut session = value_checker::Session::new(&store);
    let mut adapter = Adapter::new(&store);
    for idx in 0..store.declars.len() as u32 {
        let r = if value_core {
            session.check(idx, limits, Some(&mut adapter), true)
        } else {
            checker::check_with_adapter(
                &store,
                session.arena_mut(),
                idx,
                limits,
                Some(&mut adapter),
                true,
            )
        };
        session.reset();
        if let Err(f) = r {
            let name = store.declars[idx as usize].name().to_string();
            return match Verdict::from(f) {
                Verdict::Rejected(s) => Verdict::Rejected(format!("{name}: {s}")),
                v => v,
            };
        }
    }
    Verdict::Accepted
}

/// Check an export with the reference kernel, the fast checker and the value core.
pub fn check(source: &str, limits: Limits) -> Verdicts {
    static HOOK: std::sync::Once = std::sync::Once::new();
    HOOK.call_once(crate::term::outcome::install_hook);
    std::thread::scope(|s| {
        std::thread::Builder::new()
            .stack_size(256 << 20)
            .spawn_scoped(s, || Verdicts {
                reference: reference(source),
                fast: fast(source, limits, false),
                value: fast(source, limits, true),
            })
            .unwrap()
            .join()
            .unwrap()
    })
}
