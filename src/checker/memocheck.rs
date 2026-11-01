use super::Tc;
use crate::term::outcome::R;
use crate::term::ptr::ExprPtr;

#[derive(Default)]
pub(super) struct Audit {
    active: bool,
    pub(super) bypass: bool,
}

impl<'t, 'a: 't> Tc<'t, 'a> {
    /// Recomputes a memo hit on a full budget, trusting the hits nested inside, and panics when
    /// the recomputation disagrees. A recomputation that stops proves nothing either way.
    pub(super) fn audit(&mut self, what: &str, f: impl FnOnce(&mut Self) -> R<bool>) {
        if self.audit.active {
            return;
        }
        let saved = (
            self.steps_left,
            self.probe_remaining.take(),
            self.fail.take(),
        );
        self.steps_left = self.limits.steps;
        self.audit.active = true;
        let r = f(self);
        self.audit = Audit::default();
        (self.steps_left, self.probe_remaining, self.fail) = saved;
        assert!(
            !matches!(r, Ok(false)),
            "memocheck: a term {what} hit disagrees"
        );
    }

    pub(super) fn audit_term(
        &mut self,
        what: &str,
        hit: ExprPtr<'t>,
        f: impl FnOnce(&mut Self) -> R<ExprPtr<'t>>,
    ) {
        self.audit(what, |c| {
            c.audit.bypass = true;
            let r = f(c)?;
            Ok(r == hit || c.def_eq(r, hit)?)
        });
    }
}
