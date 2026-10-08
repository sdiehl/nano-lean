use super::{Session, Summary, Thunk, View};
use crate::kernel::prelude::*;

impl Session<'_, '_> {
    pub(super) fn summary(&mut self, name: &str, levels: &[Level]) -> Result<Summary> {
        let declaration = self.ev.tc.decl(name)?;
        self.ev.tc.level_arguments(&declaration.params, levels)?;
        if let Some((_, summary)) = declaration
            .relevance
            .borrow()
            .iter()
            .find(|(us, _)| us == levels)
        {
            return Ok(*summary);
        }
        let key = (name.to_owned(), levels.to_vec());
        if !self.relevance_active.insert(key.clone()) {
            return Ok(Summary::default());
        }
        let result = self.compute_summary(name, levels);
        self.relevance_active.remove(&key);
        let summary = result?;
        // Owned by the declaration, so rollback cannot leave a stale entry.
        let mut cached = declaration.relevance.borrow_mut();
        if cached.len() >= 16 {
            cached.clear();
        }
        cached.push((key.1, summary));
        Ok(summary)
    }
    fn compute_summary(&mut self, name: &str, levels: &[Level]) -> Result<Summary> {
        #[cfg(feature = "profile")]
        crate::profile::count("relevance_summaries");
        let head = self
            .ev
            .term(Expr::Const(name.into(), levels.to_vec()), None);
        let mut ty = self.infer(&head, false)?;
        let mut domains = Vec::new();
        let mut summary = Summary::default();
        loop {
            match self.view(&ty, true)? {
                View::Pi(domain, body) if domains.len() < 64 => {
                    let level = self.sort(&domain, false)?;
                    if level.equivalent(&Level::Nat(0))? {
                        summary.proofs |= 1 << domains.len();
                    }
                    domains.push(level);
                    let x = self.fresh(&domain);
                    ty = self.apply_body(&body, &x)?;
                }
                View::Pi(..) => break,
                View::Value(_) => {
                    let mut level = self.type_sort(&ty)?;
                    summary.set_result(domains.len(), &level)?;
                    for (arity, domain) in domains.into_iter().enumerate().rev() {
                        level = Level::imax(domain, level);
                        summary.set_result(arity, &level)?;
                    }
                    break;
                }
            }
        }
        Ok(summary)
    }
    pub(super) fn known_proof(&mut self, term: &Thunk) -> Result<Option<bool>> {
        if let Some(status) = self.proof_status.get(&term.id) {
            return Ok(*status);
        }
        let mut head = term.clone();
        let mut arity = 0;
        while let Expr::App(f, _) = &*head.expr {
            arity += 1;
            head = self.child(f, &head);
        }
        let status = match &*head.expr {
            Expr::Const(name, levels) => self.summary(name, levels)?.result(arity),
            Expr::Sort(_) | Expr::Pi(..) | Expr::Nat(_) | Expr::Str(_) if arity == 0 => Some(false),
            _ => None,
        };
        if self.proof_status.len() >= 16_384 {
            self.proof_status.clear();
        }
        self.proof_status.insert(term.id, status);
        Ok(status)
    }
}
