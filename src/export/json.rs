use crate::error::{Result, invalid};
use serde_json::Value;
use std::collections::HashMap;

pub(super) fn index(v: &Value) -> Result<usize> {
    v.as_u64()
        .and_then(|n| usize::try_from(n).ok())
        .ok_or_else(|| invalid("expected nonnegative index"))
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
