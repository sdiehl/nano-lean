//! Rules derived for hot definitions. Evaluating `f x̄` on fresh locals and splitting on the
//! constructors of each local a recursor blocks on gives a tree of guards whose leaves are
//! reducts of `f x̄[σ]`. Reduction commutes with substitution, so a leaf instantiated at
//! matching arguments is a reduct of the call.

use super::tables::{Branch, Hot, Node, Rule};
use super::value::{Head, K, V};
use super::{R, Stop, Vc, stat};
use crate::checker::env::Decls;
use crate::term::decl::{Declar, Recursor};
use crate::term::expr::Expr;
use crate::term::ptr::{ExprPtr, LevelsPtr};
use num_traits::Zero;
use smallvec::SmallVec;

pub(super) const HOT: u32 = 32;
const MAX_DERIVATIONS: u32 = 256;
const BUDGET: u64 = 1 << 16;
const MAX_ARITY: usize = 16;
const MAX_SPLITS: u32 = 3;
const MAX_CTORS: usize = 8;
const MAX_NODES: usize = 64;
const TEMPLATE_NODES: usize = 256;
const BLOCKER_DEPTH: usize = 8;

type Binds<'t> = SmallVec<[(u32, V<'t>); 32]>;

struct Slot<'t> {
    id: u32,
    local: V<'t>,
    split: Option<(V<'t>, usize, usize)>,
}

impl<'t, 'a: 't> Vc<'t, 'a> {
    #[cold]
    #[inline(never)]
    pub(super) fn derive(&mut self, f: V<'t>, body: ExprPtr<'t>) -> R<Hot> {
        let mut arity = 0;
        let mut e = body;
        while let Expr::Lam { body: b, .. } = *e {
            arity += 1;
            e = b;
        }
        if arity == 0 || arity > MAX_ARITY || self.derivations >= MAX_DERIVATIONS {
            return Ok(Hot::Never);
        }
        self.derivations += 1;
        let outer = self.steps_left;
        let budget = outer.min(BUDGET);
        let probe = self.probe_outer.replace(outer);
        self.steps_left = budget;
        self.deriving = true;
        let id0 = self.next_local + 1;
        let mut slots: Vec<Slot<'t>> = (0..arity)
            .map(|_| {
                let local = self.fresh_local(self.dummy);
                let K::Neu(Head::Local(id, ..), _) = local.k else {
                    unreachable!()
                };
                Slot {
                    id,
                    local,
                    split: None,
                }
            })
            .collect();
        let (nodes, branches) = (self.t.derived.nodes.len(), self.t.derived.branches.len());
        let r = self.explore(f, arity, &mut slots, 0, nodes);
        self.deriving = false;
        self.steps_left = outer - (budget - self.steps_left);
        self.probe_outer = probe;
        let root = match r {
            Ok(root) if !matches!(self.t.derived.nodes[root as usize], Node::Leaf(None)) => root,
            _ => {
                self.fail = None;
                self.t.derived.nodes.truncate(nodes);
                self.t.derived.branches.truncate(branches);
                stat!(self, derive_fails);
                return Ok(Hot::Never);
            }
        };
        stat!(self, derives);
        let rules = &mut self.t.derived.rules;
        rules.push(Rule {
            arity: arity as u16,
            id0,
            root,
        });
        Ok(Hot::Rule(rules.len() as u32 - 1))
    }

    fn explore(
        &mut self,
        f: V<'t>,
        arity: usize,
        slots: &mut Vec<Slot<'t>>,
        depth: u32,
        base: usize,
    ) -> R<u32> {
        if self.t.derived.nodes.len() - base >= MAX_NODES {
            return Err(Stop);
        }
        let mut args = SmallVec::<[V<'t>; 16]>::new();
        for i in 0..arity {
            args.push(self.resolve(slots, i)?);
        }
        let app = self.apply(f, &args)?;
        let r = self.whnf(app)?;
        let split = match depth < MAX_SPLITS {
            true => self.blocker(r, slots)?,
            false => None,
        };
        let leaf = Node::Leaf((template_size(r, &mut 0) <= TEMPLATE_NODES).then_some(r));
        let Some((s, rec, ls)) = split else {
            return Ok(self.node(leaf));
        };
        let Some(Declar::Ind(ind)) = self.rec_induct(&rec).and_then(|i| self.declar(i)) else {
            return Ok(self.node(leaf));
        };
        let nl = ind.info.uparams.len();
        let cls = match ls.len() {
            n if n == nl => ls,
            n if n == nl + 1 => self.ctx.levels(&ls[1..]),
            _ => return Ok(self.node(leaf)),
        };
        if ind.ctors.len() > MAX_CTORS {
            return Ok(self.node(leaf));
        }
        let mut bs = SmallVec::<[Branch<'t>; 8]>::new();
        for &c in ind.ctors {
            let Some(Declar::Ctor(ctor)) = self.declar(c) else {
                return Ok(self.node(leaf));
            };
            let n = usize::from(ctor.num_params) + usize::from(ctor.num_fields);
            let k = slots.len();
            for _ in 0..n {
                let local = self.fresh_local(self.dummy);
                let K::Neu(Head::Local(id, ..), _) = local.k else {
                    unreachable!()
                };
                slots.push(Slot {
                    id,
                    local,
                    split: None,
                });
            }
            let head = self.mk(K::Neu(Head::Const(c, cls), &[]), false);
            slots[s].split = Some((head, k, n));
            let node = self.explore(f, arity, slots, depth + 1, base)?;
            slots[s].split = None;
            let id0 = slots.get(k).map_or(0, |s| s.id);
            slots.truncate(k);
            bs.push(Branch {
                ctor: c,
                ls: cls,
                nargs: n as u16,
                id0,
                node,
            });
        }
        let d = &mut self.t.derived;
        let start = d.branches.len() as u32;
        d.branches.extend(bs);
        Ok(self.node(Node::Split {
            slot: s as u16,
            start,
            len: ind.ctors.len() as u16,
        }))
    }

    fn node(&mut self, n: Node<'t>) -> u32 {
        self.t.derived.nodes.push(n);
        self.t.derived.nodes.len() as u32 - 1
    }

    fn resolve(&mut self, slots: &[Slot<'t>], i: usize) -> R<V<'t>> {
        let Some((head, k, n)) = slots[i].split else {
            return Ok(slots[i].local);
        };
        let mut vs = SmallVec::<[V<'t>; 8]>::new();
        for j in k..k + n {
            vs.push(self.resolve(slots, j)?);
        }
        self.apply(head, &vs)
    }

    /// The unsplit slot whose local is the major a recursor in `r` waits on.
    fn blocker(
        &mut self,
        mut r: V<'t>,
        slots: &[Slot<'t>],
    ) -> R<Option<(usize, Recursor<'t>, LevelsPtr<'t>)>> {
        for _ in 0..BLOCKER_DEPTH {
            r = match r.k {
                K::Neu(Head::Const(c, ls), args) => {
                    let Some(Declar::Rec(rec)) = self.declar(c) else {
                        return Ok(None);
                    };
                    let Some(&m) = args.get(rec.major_idx()) else {
                        return Ok(None);
                    };
                    let m = self.whnf(m)?;
                    if let K::Neu(Head::Local(id, _, None), []) = m.k {
                        let s = slots.iter().position(|s| s.id == id && s.split.is_none());
                        return Ok(s.map(|s| (s, rec, ls)));
                    }
                    m
                }
                K::Neu(Head::Proj(_, _, s), _) => self.whnf(s)?,
                _ => return Ok(None),
            };
        }
        Ok(None)
    }

    #[inline(never)]
    pub(super) fn fire(&mut self, rule: u32, args: &'t [V<'t>]) -> R<Option<V<'t>>> {
        let Rule { arity, id0, root } = self.t.derived.rules[rule as usize];
        let arity = usize::from(arity);
        if args.len() < arity {
            return Ok(None);
        }
        let mut bind: Binds<'t> = (0..arity).map(|i| (id0 + i as u32, args[i])).collect();
        let mut node = root;
        loop {
            match self.t.derived.nodes[node as usize] {
                Node::Leaf(None) => break,
                Node::Leaf(Some(t)) => {
                    stat!(self, fires);
                    let v = self.subst(&bind, t)?;
                    return Ok(Some(self.apply(v, &args[arity..])?));
                }
                Node::Split { slot, start, len } => {
                    let v = self.whnf(bind[usize::from(slot)].1)?;
                    let Some(b) = self.guard_match(v, start, len, &mut bind)? else {
                        break;
                    };
                    node = b;
                }
            }
        }
        stat!(self, fire_misses);
        Ok(None)
    }

    fn guard_match(
        &mut self,
        mut v: V<'t>,
        start: u32,
        len: u16,
        bind: &mut Binds<'t>,
    ) -> R<Option<u32>> {
        if let K::Str(x) = v.k {
            let e = self.str_to_ctor(x)?;
            v = self.whnf(e)?;
        }
        let (c, ls, args) = match v.k {
            K::Nat(n) => {
                let c = if n.is_zero() {
                    self.names.nat_zero
                } else {
                    self.names.nat_succ
                };
                let Some(c) = c else { return Ok(None) };
                (c, self.id.ks, &[][..])
            }
            K::Neu(Head::Const(c, ls), args) => (c, ls, args),
            _ => return Ok(None),
        };
        let range = start as usize..start as usize + usize::from(len);
        let Some(&b) = self.t.derived.branches[range].iter().find(|b| b.ctor == c) else {
            return Ok(None);
        };
        if let K::Nat(n) = v.k {
            if !n.is_zero() {
                let p = self.nat(n - 1u32);
                bind.push((b.id0, p));
            }
            return Ok(Some(b.node));
        }
        if b.ls != ls || args.len() != usize::from(b.nargs) {
            return Ok(None);
        }
        bind.extend(args.iter().enumerate().map(|(j, &a)| (b.id0 + j as u32, a)));
        Ok(Some(b.node))
    }
}

/// Open nodes a substitution walks, counted up to the cap.
fn template_size(v: V<'_>, n: &mut usize) -> usize {
    if !v.open || *n > TEMPLATE_NODES {
        return *n;
    }
    *n += 1;
    match v.k {
        K::Neu(h, args) => {
            if let Head::Proj(_, _, s) = h {
                template_size(s, n);
            }
            for &a in args {
                template_size(a, n);
            }
        }
        K::Pi(d, c) => {
            template_size(d, n);
            *n += c.env.size();
        }
        K::Lam(l, c) => *n += l.env.size() + c.env.size(),
        _ => {}
    }
    *n
}
