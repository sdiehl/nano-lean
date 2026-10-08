use crate::checker::{self, Adapter, Limits};
use crate::export::{ExportError, check_export};
use crate::import;
use crate::term::{
    arena::Arena,
    intern::Store,
    outcome::{self, Failure},
};
use crate::value_checker::Session;
use std::{fmt, sync::Once, thread};

const STACK_BYTES: usize = 256 << 20;

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
            Failure::Declined(d) => Self::Unsupported(d.to_string()),
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
    match outcome::run(|| check_export(source.as_bytes())) {
        Ok(Ok(_)) => Verdict::Accepted,
        Ok(Err(ExportError::Invalid(s))) => Verdict::Rejected(s),
        Ok(Err(ExportError::Unsupported(s))) => Verdict::Unsupported(s),
        Err(f) => Verdict::Internal(f.reason().to_owned()),
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Core {
    Term,
    Value,
}

impl Core {
    pub fn check<'a>(
        self,
        store: &'a Store<'a>,
        session: &mut Session<'a>,
        idx: u32,
        limits: Limits,
        adapter: &mut Adapter<'a>,
        native_only: bool,
    ) -> Result<bool, Failure> {
        match self {
            Self::Value => session.check(idx, limits, Some(adapter), native_only),
            Self::Term => checker::check_with_adapter(
                store,
                session.arena_mut(),
                idx,
                limits,
                Some(adapter),
                native_only,
            ),
        }
    }
}

fn fast(source: &str, limits: Limits, core: Core) -> Verdict {
    let arena = Arena::new();
    let store = match import::import_reader(&arena, source.as_bytes(), source.len()) {
        Ok(store) => store,
        Err(ExportError::Invalid(s)) => return Verdict::Rejected(s),
        Err(ExportError::Unsupported(s)) => return Verdict::Unsupported(s),
    };
    let mut session = Session::new(&store);
    let mut adapter = Adapter::new(&store);
    for idx in 0..store.declars.len() as u32 {
        let r = core.check(&store, &mut session, idx, limits, &mut adapter, true);
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

pub fn check(source: &str, limits: Limits) -> Verdicts {
    static HOOK: Once = Once::new();
    HOOK.call_once(outcome::install_hook);
    thread::scope(|s| {
        thread::Builder::new()
            .stack_size(STACK_BYTES)
            .spawn_scoped(s, || Verdicts {
                reference: reference(source),
                fast: fast(source, limits, Core::Term),
                value: fast(source, limits, Core::Value),
            })
            .unwrap()
            .join()
            .unwrap()
    })
}
