//! Conditional validation for export checkers that verify ordinary declarations
//! separately. No environment assembled here is returned to callers.

use super::{Environment, InductiveBlock, Result};
use crate::Expr;

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

/// Validate a declaration, reconstructing all required inductive blocks.
///
/// This result is conditional on the validity of every ordinary dependency.
/// The export coordinator must check those declarations independently before
/// accepting the export, just as for `check_export_file_shard`. Dependencies
/// must precede the target and be supplied in declaration order. This function
/// never exposes the conditional environment as a validated `Environment`.
pub fn validate_export_dependencies(
    dependencies: impl IntoIterator<Item = ExportDependency>,
    target: ExportDependency,
    theorem: bool,
    work: std::rc::Rc<std::cell::Cell<u64>>,
) -> Result<()> {
    let mut env = Environment::new();
    env.export_work = Some(work);
    for dependency in dependencies {
        match dependency {
            ExportDependency::Ordinary {
                name,
                params,
                ty,
                value,
            } => {
                env.assume_export_declaration(name, params, ty, value, true)?;
            }
            ExportDependency::Inductive(block) => env.declare_inductive(block)?,
            ExportDependency::Quotient {
                name,
                params,
                ty,
                kind,
            } => {
                env.declare_quotient(name, params, ty, kind)?;
            }
        }
    }
    match target {
        ExportDependency::Inductive(block) => env.declare_inductive(block),
        ExportDependency::Quotient {
            name,
            params,
            ty,
            kind,
        } => env.declare_quotient(name, params, ty, kind),
        ExportDependency::Ordinary {
            name,
            params,
            ty,
            value,
        } if theorem => env.declare_theorem(
            name,
            params,
            ty,
            value.ok_or_else(|| super::Error("missing theorem body".into()))?,
        ),
        ExportDependency::Ordinary {
            name,
            params,
            ty,
            value,
        } => env.declare(name, params, ty, value, true),
    }
}

/// Reuse conditional dependencies while walking one immutable export in order.
/// As with `validate_export_dependencies`, the coordinator must independently
/// validate all ordinary declarations. Inductive blocks are checked before use.
#[derive(Default)]
pub struct ExportSession {
    env: Environment,
    known: std::collections::BTreeSet<u32>,
    target: Option<u32>,
}

impl ExportSession {
    pub fn begin(&mut self, target: u32) {
        // Bound retained dependency environments across long exports.
        if self.known.len() > 8192 || self.target.is_some_and(|previous| target <= previous) {
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
        work: std::rc::Rc<std::cell::Cell<u64>>,
    ) -> Result<()> {
        let index = self
            .target
            .ok_or_else(|| super::Error("missing export target".into()))?;
        self.env.export_work = Some(work);
        let result = (|| {
            for (dependency_index, dependency) in dependencies {
                if dependency_index >= index || self.known.contains(&dependency_index) {
                    return Err(super::Error("invalid cached export dependency".into()));
                }
                match dependency {
                    ExportDependency::Ordinary {
                        name,
                        params,
                        ty,
                        value,
                    } => {
                        let key = name.clone();
                        self.env
                            .assume_export_declaration(name, params, ty, value, true)?;
                        // Cache insertion order differs from export order. Preserve
                        // the latter for the evaluator's unfolding heuristic.
                        std::rc::Rc::make_mut(self.env.declarations.get_mut(&key).unwrap()).order =
                            dependency_index as usize;
                    }
                    ExportDependency::Inductive(block) => self.env.declare_inductive(block)?,
                    ExportDependency::Quotient {
                        name,
                        params,
                        ty,
                        kind,
                    } => {
                        self.env.declare_quotient(name, params, ty, kind)?;
                    }
                }
                self.known.insert(dependency_index);
            }
            let ordinary_name = match &target {
                ExportDependency::Ordinary { name, .. } => Some(name.clone()),
                _ => None,
            };
            match target {
                ExportDependency::Inductive(block) => self.env.declare_inductive(block)?,
                ExportDependency::Quotient {
                    name,
                    params,
                    ty,
                    kind,
                } => {
                    self.env.declare_quotient(name, params, ty, kind)?;
                }
                ExportDependency::Ordinary {
                    name,
                    params,
                    ty,
                    value,
                } if theorem => {
                    self.env.declare_theorem(
                        name,
                        params,
                        ty,
                        value.ok_or_else(|| super::Error("missing theorem body".into()))?,
                    )?;
                }
                ExportDependency::Ordinary {
                    name,
                    params,
                    ty,
                    value,
                } => {
                    self.env.declare(name, params, ty, value, true)?;
                }
            }
            if let Some(name) = ordinary_name {
                std::rc::Rc::make_mut(self.env.declarations.get_mut(&name).unwrap()).order =
                    index as usize;
            }
            self.known.insert(index);
            Ok(())
        })();
        if result.is_err() {
            *self = Self::default();
        }
        result
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
        let work = std::rc::Rc::new(std::cell::Cell::new(10000));
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
