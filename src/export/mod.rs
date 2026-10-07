mod check;
mod json;
mod prepass;

use crate::Error;
use crate::resource::Budget;
use json::{invalid, io};
use prepass::count_uses;
use serde_json::{Value, json};
use sha2::{Digest, Sha256};
use std::{
    fmt,
    fs::File,
    io::{BufRead, BufReader, Seek},
    path::Path,
};

pub const FORMAT_VERSION: &str = "3.1.0";
pub const TRACE_VAR: &str = "NANO_LEAN_TRACE";
const STACK_BYTES: usize = 64 * 1024 * 1024;
const EXPRESSION: &str = "ie";

#[derive(Debug)]
pub enum ExportError {
    Invalid(String),
    Unsupported(String),
}
impl fmt::Display for ExportError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Invalid(s) => write!(f, "invalid export: {s}"),
            Self::Unsupported(s) => write!(f, "unsupported: {s}"),
        }
    }
}
impl std::error::Error for ExportError {}
impl From<Error> for ExportError {
    fn from(e: Error) -> Self {
        if Budget::exhausted(&e.0) || e.0.starts_with("unsupported:") {
            Self::Unsupported(e.0)
        } else {
            Self::Invalid(e.0)
        }
    }
}
impl ExportError {
    fn at_line(self, line: usize) -> Self {
        match self {
            Self::Invalid(s) => Self::Invalid(format!("line {}: {s}", line + 1)),
            Self::Unsupported(s) => Self::Unsupported(format!("line {}: {s}", line + 1)),
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

#[derive(Debug)]
pub struct ExportReport {
    pub declarations: usize,
    pub expressions: usize,
    pub names: usize,
    pub levels: usize,
}
impl ExportReport {
    fn counts(&self) -> Value {
        json!({"declarations":self.declarations,"expressions":self.expressions,"names":self.names,"levels":self.levels})
    }

    pub fn json(&self) -> Value {
        let mut report = self.counts();
        report["status"] = json!("checked");
        report
    }
}

/// Valid only if every partition succeeds on the same input digest.
#[derive(Debug)]
pub struct ShardReport {
    report: ExportReport,
    index: usize,
    workers: usize,
    assigned: usize,
    ordinary: usize,
    digest: String,
}
impl ShardReport {
    pub fn json(&self) -> Value {
        json!({"status": "shard_checked", "shard": self.index, "workers": self.workers,
            "assigned": self.assigned, "ordinary": self.ordinary, "sha256": self.digest,
            "report": self.report.counts()})
    }
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
    let mut reader = BufReader::new(File::open(path).map_err(io)?);
    let counts = count_uses(&mut reader)?;
    reader.rewind().map_err(io)?;
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
        report,
        index: shard,
        workers,
        assigned: plan.assigned,
        ordinary: plan.ordinary,
        digest: format!("{:x}", plan.digest.finalize()),
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
        assert_eq!(reclaimed.json(), stream.json());
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
        assert_eq!(
            reclaimed.json(),
            check_export(Cursor::new(input)).unwrap().json()
        );
    }

    #[test]
    fn primitive_prepass_handles_literals_and_quotient_signature_roots() {
        let input = include_str!("../../tests/fixtures/primitives.ndjson");
        let input = format!("{input}{{\"ie\":460,\"strVal\":\"水🦀\"}}\n");
        let counts = count_uses(Cursor::new(&input)).unwrap().unwrap();
        assert_eq!(counts.len(), 461);
        let reclaimed = check_with_counts(Cursor::new(&input), Some(counts)).unwrap();
        assert_eq!(reclaimed.declarations, 35);
        assert_eq!(
            reclaimed.json(),
            check_export(Cursor::new(input)).unwrap().json()
        );
    }
}
