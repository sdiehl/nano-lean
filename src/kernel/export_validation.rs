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
