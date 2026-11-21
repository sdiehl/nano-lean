use crate::kernel::Error;
use std::io;

#[derive(Debug, thiserror::Error)]
pub enum ExportError {
    #[error("invalid export: {0}")]
    Invalid(String),
    #[error("unsupported: {0}")]
    Unsupported(String),
    #[error("internal: {0}")]
    Internal(String),
}

pub(crate) type Result<T> = std::result::Result<T, ExportError>;

#[cold]
#[inline(never)]
pub(crate) fn invalid(s: impl Into<String>) -> ExportError {
    ExportError::Invalid(s.into())
}

#[cold]
#[inline(never)]
pub(crate) fn unsupported(s: impl Into<String>) -> ExportError {
    ExportError::Unsupported(s.into())
}

impl ExportError {
    /// 1 for an invalid export, 2 for anything the checker could not settle.
    pub fn exit_code(&self) -> u8 {
        match self {
            Self::Invalid(_) => 1,
            Self::Unsupported(_) | Self::Internal(_) => 2,
        }
    }

    pub(crate) fn at(self, unit: &str, n: usize) -> Self {
        let f = |s| format!("{unit} {}: {s}", n + 1);
        match self {
            Self::Invalid(s) => Self::Invalid(f(s)),
            Self::Unsupported(s) => Self::Unsupported(f(s)),
            Self::Internal(s) => Self::Internal(f(s)),
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
            Error::Internal(s) => Self::Internal(s),
            e => Self::Unsupported(e.to_string()),
        }
    }
}
