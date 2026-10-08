mod check;
mod json;
mod prepass;

use crate::Error;
use json::invalid;
use prepass::count_uses;
use serde::{Deserialize, Serialize};
use serde_json::Value;
use sha2::{Digest, Sha256};
use std::{
    fmt,
    fs::File,
    io::{self, BufRead, BufReader, Seek},
    path::Path,
};

pub const FORMAT_VERSION: &str = "3.1.0";
pub const TRACE_VAR: &str = "NANO_LEAN_TRACE";
const STACK_BYTES: usize = 64 * 1024 * 1024;
const EXPRESSION: &str = "ie";

#[derive(Debug, thiserror::Error)]
pub enum ExportError {
    #[error("invalid export: {0}")]
    Invalid(String),
    #[error("unsupported: {0}")]
    Unsupported(String),
}

impl ExportError {
    pub(crate) fn at(self, unit: &str, n: usize) -> Self {
        match self {
            Self::Invalid(s) => Self::Invalid(format!("{unit} {}: {s}", n + 1)),
            Self::Unsupported(s) => Self::Unsupported(format!("{unit} {}: {s}", n + 1)),
        }
    }
}

impl From<io::Error> for ExportError {
    fn from(e: io::Error) -> Self {
        Self::Invalid(e.to_string())
    }
}

impl From<serde_json::Error> for ExportError {
    fn from(e: serde_json::Error) -> Self {
        Self::Invalid(e.to_string())
    }
}

impl From<Error> for ExportError {
    fn from(e: Error) -> Self {
        match e {
            Error::Rejected(s) => Self::Invalid(s),
            Error::Unsupported(s) => Self::Unsupported(s),
            e => Self::Unsupported(e.to_string()),
        }
    }
}
type Result<T> = std::result::Result<T, ExportError>;

#[derive(Clone, Copy, PartialEq, Eq)]
enum Kind {
    Axiom,
    Def,
    Thm,
    Opaque,
    Quot,
    Inductive,
}

impl Kind {
    const ALL: [Self; 6] = [
        Self::Axiom,
        Self::Def,
        Self::Thm,
        Self::Opaque,
        Self::Quot,
        Self::Inductive,
    ];

    fn key(self) -> &'static str {
        match self {
            Self::Axiom => "axiom",
            Self::Def => "def",
            Self::Thm => "thm",
            Self::Opaque => "opaque",
            Self::Quot => "quot",
            Self::Inductive => "inductive",
        }
    }

    fn of(key: &str) -> Option<Self> {
        Self::ALL.into_iter().find(|k| k.key() == key)
    }

    fn has_value(self) -> bool {
        matches!(self, Self::Def | Self::Thm | Self::Opaque)
    }
}

fn current_format(item: &Value) -> bool {
    item["meta"]["format"]["version"] == FORMAT_VERSION
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExportReport {
    pub declarations: usize,
    pub expressions: usize,
    pub names: usize,
    pub levels: usize,
}

/// Valid only if every partition succeeds on the same input digest.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ShardReport {
    pub shard: usize,
    pub workers: usize,
    pub assigned: usize,
    pub ordinary: usize,
    pub sha256: String,
    pub report: ExportReport,
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(tag = "status", rename_all = "snake_case")]
pub enum Report {
    Checked {
        #[serde(flatten)]
        report: ExportReport,
        #[serde(skip_serializing_if = "Option::is_none")]
        workers: Option<usize>,
        #[serde(skip_serializing_if = "Option::is_none")]
        sha256: Option<String>,
    },
    ShardChecked(ShardReport),
    Rejected {
        reason: String,
    },
    Unsupported {
        reason: String,
    },
}

impl From<ExportReport> for Report {
    fn from(report: ExportReport) -> Self {
        Self::Checked {
            report,
            workers: None,
            sha256: None,
        }
    }
}

impl From<ShardReport> for Report {
    fn from(report: ShardReport) -> Self {
        Self::ShardChecked(report)
    }
}

impl From<ExportError> for Report {
    fn from(e: ExportError) -> Self {
        let reason = e.to_string();
        match e {
            ExportError::Invalid(_) => Self::Rejected { reason },
            ExportError::Unsupported(_) => Self::Unsupported { reason },
        }
    }
}

impl fmt::Display for Report {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&serde_json::to_string(self).map_err(|_| fmt::Error)?)
    }
}

/// One stderr line per declaration when tracing.
#[derive(Debug, Serialize, Deserialize)]
pub struct Trace {
    pub line: usize,
    pub checked: Option<usize>,
    pub imported: usize,
    pub shard: Option<usize>,
    pub assigned_checked: usize,
    pub kind: String,
    pub name: Option<String>,
}

#[derive(Default)]
struct CheckPlan {
    shard: Option<(usize, usize)>,
    ordinary: usize,
    assigned: usize,
    digest: Sha256,
}

pub fn check_export(reader: impl BufRead) -> Result<ExportReport> {
    #[cfg(feature = "profile")]
    let _profile = crate::profile::export();
    check_with_counts(reader, None)
}

fn open_counted(path: impl AsRef<Path>) -> Result<(BufReader<File>, Option<Vec<u32>>)> {
    let mut reader = BufReader::new(File::open(path)?);
    let counts = count_uses(&mut reader)?;
    reader.rewind()?;
    Ok((reader, counts))
}

pub fn check_export_file(path: impl AsRef<Path>) -> Result<ExportReport> {
    #[cfg(feature = "profile")]
    let _profile = crate::profile::export();
    let (reader, counts) = open_counted(path)?;
    check_with_counts(reader, counts)
}

pub fn check_export_file_shard(
    path: impl AsRef<Path>,
    shard: usize,
    workers: usize,
) -> Result<ShardReport> {
    #[cfg(feature = "profile")]
    let _profile = crate::profile::export();
    if workers == 0 || shard >= workers {
        return Err(invalid("invalid worker partition"));
    }
    let (reader, counts) = open_counted(path)?;
    let mut plan = CheckPlan {
        shard: Some((shard, workers)),
        ..Default::default()
    };
    let report = stacker::grow(STACK_BYTES, || check::run(reader, counts, &mut plan))?;
    Ok(ShardReport {
        shard,
        workers,
        assigned: plan.assigned,
        ordinary: plan.ordinary,
        sha256: format!("{:x}", plan.digest.finalize()),
        report,
    })
}

fn check_with_counts(reader: impl BufRead, counts: Option<Vec<u32>>) -> Result<ExportReport> {
    stacker::grow(STACK_BYTES, || {
        check::run(reader, counts, &mut CheckPlan::default())
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Cursor;

    #[test]
    fn projection_prepass_counts_only_the_structure_expression() {
        let input = concat!(
            "{\"meta\":{\"format\":{\"version\":\"3.1.0\"}}}\n",
            "{\"in\":100,\"str\":{\"pre\":0,\"str\":\"S\"}}\n",
            "{\"ie\":0,\"bvar\":0}\n",
            "{\"ie\":1,\"proj\":{\"typeName\":100,\"idx\":2,\"struct\":0}}\n",
            "{\"ie\":2,\"proj\":{\"typeName\":100,\"idx\":3,\"struct\":0}}\n",
        );
        let counts = count_uses(Cursor::new(input)).unwrap().unwrap();
        assert_eq!(counts, [2, 0, 0]);
        let reclaimed = check_with_counts(Cursor::new(input), Some(counts)).unwrap();
        let stream = check_export(Cursor::new(input)).unwrap();
        assert_eq!(reclaimed, stream);
    }

    #[test]
    fn inductive_prepass_keeps_declaration_roots_alive() {
        let input = include_str!("../../tests/fixtures/inductive-boundaries.ndjson");
        let counts = count_uses(Cursor::new(input)).unwrap().unwrap();
        assert_eq!(counts.len(), 67);
        for root in [6, 17, 36, 45, 46, 50, 62, 66] {
            assert_eq!(counts[root], 1, "declaration root {root}");
        }
        let reclaimed = check_with_counts(Cursor::new(input), Some(counts)).unwrap();
        assert_eq!(reclaimed.declarations, 6);
        assert_eq!(reclaimed, check_export(Cursor::new(input)).unwrap());
    }

    #[test]
    fn primitive_prepass_handles_literals_and_quotient_signature_roots() {
        let input = include_str!("../../tests/fixtures/primitives.ndjson");
        let input = format!("{input}{{\"ie\":460,\"strVal\":\"水🦀\"}}\n");
        let counts = count_uses(Cursor::new(&input)).unwrap().unwrap();
        assert_eq!(counts.len(), 461);
        let reclaimed = check_with_counts(Cursor::new(&input), Some(counts)).unwrap();
        assert_eq!(reclaimed.declarations, 35);
        assert_eq!(reclaimed, check_export(Cursor::new(input)).unwrap());
    }
}
