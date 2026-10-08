use super::{ExportError, Result};
use serde_json::Value;
use std::collections::HashMap;

pub(super) fn invalid(s: impl Into<String>) -> ExportError {
    ExportError::Invalid(s.into())
}

pub(super) fn unsupported(s: impl Into<String>) -> ExportError {
    ExportError::Unsupported(s.into())
}

pub(super) fn index(v: &Value) -> Result<usize> {
    v.as_u64()
        .and_then(|n| usize::try_from(n).ok())
        .ok_or_else(|| invalid("expected nonnegative index"))
}

pub(super) fn array(v: &Value) -> Result<&[Value]> {
    v.as_array()
        .map(Vec::as_slice)
        .ok_or_else(|| invalid("expected array"))
}

pub(super) fn string(v: &Value) -> Result<&str> {
    v.as_str().ok_or_else(|| invalid("expected string"))
}

pub(super) fn boolean(v: &Value) -> Result<bool> {
    v.as_bool().ok_or_else(|| invalid("expected boolean"))
}

pub(super) fn lookup<'a, T>(items: &'a HashMap<usize, T>, v: &Value) -> Result<&'a T> {
    items
        .get(&index(v)?)
        .ok_or_else(|| invalid("unknown or forward reference"))
}

pub(super) fn append<T>(items: &mut HashMap<usize, T>, id: &Value, value: T) -> Result<()> {
    let id = index(id)?;
    if items.contains_key(&id) {
        return Err(invalid("duplicate index"));
    }
    items.insert(id, value);
    Ok(())
}
