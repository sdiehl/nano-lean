mod operators;
mod table;

pub use operators::{Operator, mutants};
pub use table::{Ref, compact, defines, is_declaration, refs};

use crate::checker::Limits;
use crate::verdict::{self, Verdict, Verdicts};
use serde_json::Value;
use std::fmt::Write;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Expect {
    Reject,
    Agree,
    Same,
}

#[derive(Clone, Debug)]
pub enum Edit {
    Set(usize, String, Value),
    Replace(usize, Value),
    Remove(usize),
    Duplicate(usize),
    Swap(usize, usize),
}

#[derive(Clone, Debug)]
pub struct Mutant {
    pub op: Operator,
    pub expect: Expect,
    pub edit: Edit,
}

impl Mutant {
    pub fn apply(&self, lines: &[Value]) -> Vec<Value> {
        let mut out = lines.to_vec();
        match &self.edit {
            Edit::Set(i, ptr, v) => {
                *out[*i]
                    .pointer_mut(ptr)
                    .expect("edit targets an existing path") = v.clone();
            }
            Edit::Replace(i, v) => out[*i] = v.clone(),
            Edit::Remove(i) => {
                out.remove(*i);
            }
            Edit::Duplicate(i) => out.insert(*i + 1, lines[*i].clone()),
            Edit::Swap(a, b) => out.swap(*a, *b),
        }
        out
    }

    /// Lines the edit touches, which shrinking must keep.
    pub fn pins(&self) -> Vec<usize> {
        match self.edit {
            Edit::Set(i, ..) | Edit::Replace(i, _) | Edit::Remove(i) | Edit::Duplicate(i) => {
                vec![i]
            }
            Edit::Swap(a, b) => vec![a, b],
        }
    }

    /// The same edit aimed at the lines `pins` moved to.
    pub fn at(&self, pins: &[usize]) -> Self {
        let edit = match &self.edit {
            Edit::Set(_, ptr, v) => Edit::Set(pins[0], ptr.clone(), v.clone()),
            Edit::Replace(_, v) => Edit::Replace(pins[0], v.clone()),
            Edit::Remove(_) => Edit::Remove(pins[0]),
            Edit::Duplicate(_) => Edit::Duplicate(pins[0]),
            Edit::Swap(..) => Edit::Swap(pins[0], pins[1]),
        };
        Self {
            edit,
            ..self.clone()
        }
    }

    pub fn site(&self) -> String {
        match &self.edit {
            Edit::Set(i, ptr, v) => format!("line {} {ptr} = {v}", i + 1),
            Edit::Replace(i, _) => format!("line {} replaced", i + 1),
            Edit::Remove(i) => format!("line {} removed", i + 1),
            Edit::Duplicate(i) => format!("line {} duplicated", i + 1),
            Edit::Swap(a, b) => format!("lines {} and {} swapped", a + 1, b + 1),
        }
    }
}

pub fn parse(source: &str) -> Result<Vec<Value>, serde_json::Error> {
    source
        .lines()
        .filter(|l| !l.trim().is_empty())
        .map(serde_json::from_str)
        .collect()
}

pub fn render(lines: &[Value]) -> String {
    let mut out = String::new();
    for l in lines {
        let _ = writeln!(out, "{l}");
    }
    out
}

const GOLDEN_GAMMA: u64 = 0x9e37_79b9_7f4a_7c15;

pub struct Rng(u64);

impl Rng {
    pub fn new(seed: u64) -> Self {
        Self(seed ^ GOLDEN_GAMMA)
    }

    pub fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(GOLDEN_GAMMA);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }

    pub fn below(&mut self, n: usize) -> usize {
        (self.next_u64() % n as u64) as usize
    }
}

fn category(v: &Verdict) -> char {
    match v {
        Verdict::Accepted => 'A',
        Verdict::Rejected(_) => 'R',
        Verdict::Unsupported(_) => 'U',
        Verdict::Internal(_) => 'I',
    }
}

pub fn signature(v: &Verdicts) -> String {
    v.all().iter().map(|(_, v)| category(v)).collect()
}

pub fn finding(expect: Expect, baseline: &Verdicts, v: &Verdicts) -> Option<&'static str> {
    let all = v.all();
    if !v.agree() {
        let internal = all.iter().any(|(_, v)| matches!(v, Verdict::Internal(_)));
        return Some(if internal {
            "internal error"
        } else {
            "checkers disagree"
        });
    }
    match expect {
        Expect::Reject if all.iter().any(|(_, v)| v.accepted()) => {
            Some("accepted an invalid export")
        }
        Expect::Same if signature(v) != signature(baseline) => Some("verdict changed"),
        _ => None,
    }
}

/// A checker declined while another accepted, which `agree` tolerates but can hide a wrong accept.
pub fn declined(v: &Verdicts) -> bool {
    let all = v.all();
    all.iter().any(|(_, v)| v.accepted())
        && all
            .iter()
            .any(|(_, v)| matches!(v, Verdict::Unsupported(_)))
}

/// Removes declarations and dead definitions while `keep` holds, returning the survivors and
/// where the pinned lines ended up.
pub fn shrink(
    mut lines: Vec<Value>,
    mut pins: Vec<usize>,
    keep: impl Fn(&[Value], &[usize]) -> bool,
) -> (Vec<Value>, Vec<usize>) {
    loop {
        let before = lines.len();
        for i in (0..lines.len()).rev() {
            if is_declaration(&lines[i]) && !pins.contains(&i) {
                let mut candidate = lines.clone();
                candidate.remove(i);
                let moved: Vec<_> = pins.iter().map(|&p| p - usize::from(p > i)).collect();
                if keep(&candidate, &moved) {
                    lines = candidate;
                    pins = moved;
                }
            }
        }
        let (compacted, moved) = compact(&lines, &pins);
        if compacted.len() < lines.len() && keep(&compacted, &moved) {
            lines = compacted;
            pins = moved;
        }
        if lines.len() == before {
            return (lines, pins);
        }
    }
}

pub fn check(lines: &[Value], limits: Limits) -> Verdicts {
    verdict::check(&render(lines), limits)
}
