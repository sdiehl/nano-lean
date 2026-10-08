//! Soundness: results are conditional on ordinary dependencies the coordinator checks separately.

use super::{Environment, Error, InductiveBlock, Result};
use crate::Expr;
use std::{cell::Cell, collections::BTreeSet, rc::Rc};

const MAX_KNOWN_DEPENDENCIES: usize = 8192;

pub enum ExportDependency {
    Ordinary {
        name: String,
        params: Vec<String>,
        ty: Expr,
        value: Option<Expr>,
    },
    Inductive(InductiveBlock),
    Quotient {
        name: String,
        params: Vec<String>,
        ty: Expr,
        kind: &'static str,
    },
}

impl Environment {
    fn assume_dependency(&mut self, dependency: ExportDependency) -> Result<()> {
        match dependency {
            ExportDependency::Ordinary {
                name,
                params,
                ty,
                value,
            } => self.assume_export_declaration(name, params, ty, value, true),
            ExportDependency::Inductive(block) => self.declare_inductive(&block),
            ExportDependency::Quotient {
                name,
                params,
                ty,
                kind,
            } => self.declare_quotient(name, params, ty, kind),
        }
    }

    fn declare_target(&mut self, target: ExportDependency, theorem: bool) -> Result<()> {
        match target {
            ExportDependency::Ordinary {
                name,
                params,
                ty,
                value,
            } if theorem => self.declare_theorem(
                name,
                params,
                ty,
                value.ok_or_else(|| Error::Rejected("missing theorem body".into()))?,
            ),
            ExportDependency::Ordinary {
                name,
                params,
                ty,
                value,
            } => self.declare(name, params, ty, value, true),
            other => self.assume_dependency(other),
        }
    }

    fn set_order(&mut self, name: &str, order: u32) {
        Rc::make_mut(
            self.declarations
                .get_mut(name)
                .expect("declared before ordering"),
        )
        .order = order as usize;
    }
}

fn ordinary_name(dependency: &ExportDependency) -> Option<String> {
    match dependency {
        ExportDependency::Ordinary { name, .. } => Some(name.clone()),
        _ => None,
    }
}

/// Dependencies must precede the target in declaration order, and the conditional environment is never exposed.
pub fn validate_export_dependencies(
    dependencies: impl IntoIterator<Item = ExportDependency>,
    target: ExportDependency,
    theorem: bool,
    work: Rc<Cell<u64>>,
) -> Result<()> {
    let mut env = Environment::new();
    env.export_work = Some(work);
    for dependency in dependencies {
        env.assume_dependency(dependency)?;
    }
    env.declare_target(target, theorem)
}

#[derive(Default)]
pub struct ExportSession {
    env: Environment,
    known: BTreeSet<u32>,
    target: Option<u32>,
}

impl ExportSession {
    pub fn begin(&mut self, target: u32) {
        if self.known.len() > MAX_KNOWN_DEPENDENCIES
            || self.target.is_some_and(|previous| target <= previous)
        {
            *self = Self::default();
        }
        self.target = Some(target);
    }

    pub fn contains(&self, index: u32) -> bool {
        self.known.contains(&index)
    }

    pub fn validate(
        &mut self,
        dependencies: impl IntoIterator<Item = (u32, ExportDependency)>,
        target: ExportDependency,
        theorem: bool,
        work: Rc<Cell<u64>>,
    ) -> Result<()> {
        let index = self
            .target
            .ok_or_else(|| Error::Rejected("missing export target".into()))?;
        self.env.export_work = Some(work);
        let result = self.extend(dependencies, target, theorem, index);
        if result.is_err() {
            *self = Self::default();
        }
        result
    }

    fn extend(
        &mut self,
        dependencies: impl IntoIterator<Item = (u32, ExportDependency)>,
        target: ExportDependency,
        theorem: bool,
        index: u32,
    ) -> Result<()> {
        for (dependency_index, dependency) in dependencies {
            if dependency_index >= index || self.known.contains(&dependency_index) {
                return Err(Error::Rejected("invalid cached export dependency".into()));
            }
            let name = ordinary_name(&dependency);
            self.env.assume_dependency(dependency)?;
            // Preserve export order for the evaluator's unfolding heuristic.
            if let Some(name) = name {
                self.env.set_order(&name, dependency_index);
            }
            self.known.insert(dependency_index);
        }
        let name = ordinary_name(&target);
        self.env.declare_target(target, theorem)?;
        if let Some(name) = name {
            self.env.set_order(&name, index);
        }
        self.known.insert(index);
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Level;

    fn axiom(name: &str) -> ExportDependency {
        ExportDependency::Ordinary {
            name: name.into(),
            params: vec![],
            ty: Expr::Sort(Level::Nat(0)),
            value: None,
        }
    }

    #[test]
    fn cached_dependencies_preserve_export_unfolding_order() {
        let mut session = ExportSession::default();
        let work = Rc::new(Cell::new(10000));
        session.begin(10);
        session
            .validate([(9, axiom("later"))], axiom("first"), false, work.clone())
            .unwrap();
        session.begin(20);
        session
            .validate([(4, axiom("earlier"))], axiom("second"), false, work)
            .unwrap();
        assert!(
            session.env.declarations["earlier"].order < session.env.declarations["later"].order
        );
        session.begin(5);
        assert!(!session.contains(9));
    }
}
