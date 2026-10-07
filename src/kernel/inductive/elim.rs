use super::{InductiveType, Recursor};
use rustc_hash::FxHashSet;
use std::hash::Hash;

impl InductiveType {
    pub(crate) fn distinct_params<T: Eq + Hash>(params: &[T]) -> bool {
        params.iter().collect::<FxHashSet<_>>().len() == params.len()
    }
}

impl Recursor {
    pub(crate) const SUFFIX: &str = "rec";

    pub(crate) fn forced_elimination(
        positive: bool,
        num_types: usize,
        num_ctors: usize,
    ) -> Option<bool> {
        if positive {
            Some(true)
        } else if num_types > 1 || num_ctors > 1 {
            Some(false)
        } else if num_ctors == 0 {
            Some(true)
        } else {
            None
        }
    }

    pub(crate) fn k_like(
        prop: bool,
        num_types: usize,
        mut fields: impl ExactSizeIterator<Item = usize>,
    ) -> bool {
        prop && num_types == 1 && fields.len() == 1 && fields.next() == Some(0)
    }

    pub(crate) fn large_params<T: PartialEq>(rec: &[T], ty: &[T]) -> bool {
        rec.len() == ty.len() + 1 && rec[1..] == *ty && !ty.contains(&rec[0])
    }
}
