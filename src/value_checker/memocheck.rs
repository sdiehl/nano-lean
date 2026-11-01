use super::value::V;
use super::{R, Vc};
use std::ptr;

#[derive(Default)]
pub(super) struct Audit {
    active: bool,
    pub(super) bypass: bool,
}

impl<'t, 'a: 't> Vc<'t, 'a> {
    /// Recomputes a memo hit on a full budget, trusting the hits nested inside, and panics when
    /// the recomputation disagrees. A recomputation that stops proves nothing either way.
    pub(super) fn audit(&mut self, what: &str, f: impl FnOnce(&mut Self) -> R<bool>) {
        if self.audit.active {
            return;
        }
        let saved = (
            self.steps_left,
            self.probe_outer.take(),
            self.scoped,
            self.fail.take(),
        );
        self.steps_left = self.limits.steps;
        self.audit.active = true;
        let r = f(self);
        self.audit = Audit::default();
        (self.steps_left, self.probe_outer, self.scoped, self.fail) = saved;
        assert!(!matches!(r, Ok(false)), "memocheck: a {what} hit disagrees");
    }

    pub(super) fn audit_value(
        &mut self,
        what: &str,
        hit: V<'t>,
        f: impl FnOnce(&mut Self) -> R<V<'t>>,
    ) {
        self.audit(what, |s| {
            let v = f(s)?;
            Ok(ptr::eq(v, hit) || s.def_eq(v, hit)?)
        });
    }

    /// The next lookup at the audited site misses so the recomputation reaches its body.
    pub(super) fn audit_bypass(&mut self) {
        self.audit.bypass = true;
    }

    pub(super) fn audit_entered(&mut self) {
        self.audit.bypass = false;
    }
}
