use super::tables::LOG;
use super::value::*;
use super::{Vc, stat};
use crate::term::ptr::{ExprPtr, LevelPtr, LevelsPtr, NamePtr};
use rustc_hash::FxBuildHasher;
use std::hash::{BuildHasher, Hash, Hasher};
use std::ptr;

#[derive(Clone, Copy, Hash, PartialEq, Eq)]
pub(super) enum HKey<'t> {
    Sort(LevelPtr<'t>),
    Pi(usize, (usize, Sub<'t>, ExprPtr<'t>, bool)),
    Lam(usize, (usize, Sub<'t>, ExprPtr<'t>, bool)),
    Const(NamePtr<'t>, LevelsPtr<'t>),
    Proj(NamePtr<'t>, u16, usize),
    Str(usize, usize),
}

fn head_eq<'t>(a: Head<'t>, b: Head<'t>) -> bool {
    match (a, b) {
        (Head::Local(i, _), Head::Local(j, _)) => i == j,
        (Head::Const(n, l), Head::Const(m, k)) => n == m && l == k,
        (Head::Proj(n, i, x), Head::Proj(m, j, y)) => n == m && i == j && ptr::eq(x, y),
        _ => false,
    }
}

fn neu_hash<'t, 'v>(h: Head<'t>, n: usize, args: impl Iterator<Item = &'v V<'t>>) -> u64
where
    't: 'v,
{
    let mut s = FxBuildHasher.build_hasher();
    match h {
        Head::Local(i, _) => (0u8, i).hash(&mut s),
        Head::Const(c, l) => (1u8, c, l).hash(&mut s),
        Head::Proj(c, i, x) => (2u8, c, i, key(x)).hash(&mut s),
    }
    s.write_usize(n);
    for &a in args {
        s.write_usize(key(a));
    }
    s.finish()
}

#[repr(transparent)]
pub(super) struct Ptrs<'t>([V<'t>]);

impl<'t> Ptrs<'t> {
    pub(super) fn new<'s>(a: &'s [V<'t>]) -> &'s Self {
        // SAFETY: `Ptrs` is a transparent wrapper over the slice.
        unsafe { &*(a as *const [V<'t>] as *const Self) }
    }
}

impl Hash for Ptrs<'_> {
    fn hash<H: Hasher>(&self, h: &mut H) {
        h.write_usize(self.0.len());
        for &v in &self.0 {
            h.write_usize(key(v));
        }
    }
}

impl PartialEq for Ptrs<'_> {
    fn eq(&self, o: &Self) -> bool {
        self.0.len() == o.0.len() && self.0.iter().zip(&o.0).all(|(&a, &b)| ptr::eq(a, b))
    }
}

impl Eq for Ptrs<'_> {}

impl<'t, 'a: 't> Vc<'t, 'a> {
    pub(crate) fn mk(&mut self, k: K<'t>, open: bool) -> V<'t> {
        // Open Pi values almost never recur, so probing for them only costs.
        if open && matches!(k, K::Pi(..)) {
            stat!(self, vals);
            return self.ctx.arena.alloc(Val { k, open });
        }
        let ck = |c: Clo<'t>| (c.env.key(), c.sub, c.body, c.typed);
        let hk = match k {
            K::Sort(l) => HKey::Sort(l),
            K::Pi(d, c) => HKey::Pi(key(d), ck(c)),
            K::Lam(d, c) => HKey::Lam(d as *const Lazy as usize, ck(c)),
            K::Neu(h, a) => {
                debug_assert!(a.is_empty());
                match h {
                    Head::Local(..) => unreachable!("locals are not interned"),
                    Head::Const(n, ls) => HKey::Const(n, ls),
                    Head::Proj(n, i, x) => HKey::Proj(n, i, key(x)),
                }
            }
            K::Nat(n) => return self.nat(n.clone()),
            K::Str(x) => HKey::Str(x.as_ptr() as usize, x.len()),
        };
        stat!(self, mk_req);
        #[cfg(feature = "vstats")]
        let kind = match (&hk, open) {
            (HKey::Sort(_), _) => 0,
            (HKey::Pi(..), true) => 1,
            (HKey::Pi(..), false) => 2,
            (HKey::Lam(..), true) => 3,
            (HKey::Lam(..), false) => 4,
            (HKey::Str(..), _) => 6,
            (_, true) => 5,
            (_, false) => 7,
        };
        let hc = &mut self.t.hc[usize::from(open)];
        let h = match hc.probe(&hk) {
            Ok(&v) => {
                #[cfg(feature = "vstats")]
                self.stats.mk_kind(kind, true);
                return v;
            }
            Err(h) => h,
        };
        #[cfg(feature = "vstats")]
        self.stats.mk_kind(kind, false);
        let v = self.ctx.arena.alloc(Val { k, open });
        hc.insert_new(h, hk, v);
        stat!(self, vals);
        v
    }

    pub(crate) fn neu(&mut self, h: Head<'t>, sp: &[V<'t>], rest: &[V<'t>], open: bool) -> V<'t> {
        stat!(self, spine_req);
        let n = sp.len() + rest.len();
        let hash = neu_hash(h, n, sp.iter().chain(rest));
        let same = |&(hv, v): &(u64, V<'t>)| {
            hv == hash
                && matches!(v.k, K::Neu(g, a) if a.len() == n && head_eq(g, h)
                && a.iter().zip(sp.iter().chain(rest)).all(|(&x, &y)| ptr::eq(x, y)))
        };
        let o = usize::from(open);
        if let Some(&(_, v)) = self.t.neus[o].find(hash, same) {
            #[cfg(feature = "vstats")]
            if open {
                self.stats.neu_open_hit += 1
            } else {
                self.stats.neu_closed_hit += 1
            }
            return v;
        }
        #[cfg(feature = "vstats")]
        if open {
            self.stats.neu_open_miss += 1
        } else {
            self.stats.neu_closed_miss += 1
        }
        let all: &'t [V<'t>] = if sp.is_empty() {
            self.ctx.arena.alloc_slice_copy(rest)
        } else {
            let m = sp.len();
            self.ctx
                .arena
                .alloc_slice_fill_with(n, |i| if i < m { sp[i] } else { rest[i - m] })
        };
        #[cfg(feature = "vstats")]
        {
            self.stats.spine_new += 1;
            self.stats.spine_copied += n as u64;
        }
        stat!(self, vals);
        let v = self.ctx.arena.alloc(Val {
            k: K::Neu(h, all),
            open,
        });
        if open && self.t.neu_log.len() < LOG {
            self.t.neu_log.push((hash, v));
        }
        self.t.neus[o].insert_unique(hash, (hash, v), |&(g, _)| g);
        v
    }
}
