use super::value::*;
use super::{R, Vc, stat};
use crate::checker::env::Decls;
use crate::checker::nat::{self, NatValue};
use crate::reject;
use crate::term::decl::{Declar, Hint, Recursor};
use crate::term::names::{QUOT_FN, QUOT_IND_MAJOR, QUOT_LIFT_MAJOR, QUOT_MK_ARITY};
use crate::term::ptr::{LevelsPtr, NamePtr};
use num_bigint::BigUint;
use num_traits::Zero;
use smallvec::SmallVec;

impl<'t, 'a: 't> Vc<'t, 'a> {
    pub(crate) fn whnf_core(&mut self, v: V<'t>) -> R<V<'t>> {
        self.tick()?;
        let K::Neu(h, args) = v.k else { return Ok(v) };
        if matches!(h, Head::Local(..)) {
            return Ok(v);
        }
        if let Some(&r) = self.t.whnf_core_cache.get(&key(v)) {
            return Ok(r);
        }
        let r = match h {
            Head::Const(n, ls) => match self.reduce_rec(n, ls, args)? {
                Some(r) => self.whnf_core(r)?,
                None => v,
            },
            Head::Proj(_, idx, s) => match self.reduce_proj(idx, s)? {
                Some(f) => {
                    let f = self.apply(f, args)?;
                    self.whnf_core(f)?
                }
                None => v,
            },
            Head::Local(..) => unreachable!(),
        };
        self.t.whnf_core_cache.insert(key(v), r);
        Ok(r)
    }

    pub(crate) fn whnf(&mut self, v: V<'t>) -> R<V<'t>> {
        match v.k {
            K::Neu(Head::Local(..), _)
            | K::Sort(_)
            | K::Pi(..)
            | K::Lam(..)
            | K::Nat(_)
            | K::Str(_) => return Ok(v),
            _ => {}
        }
        if let Some(&r) = self.t.whnf_cache.get(&key(v)) {
            return Ok(r);
        }
        stat!(self, whnfs);
        let mut t = v;
        let mut path = SmallVec::<[V<'t>; 8]>::new();
        let r = loop {
            self.tick()?;
            if let Some(&r) = self.t.whnf_cache.get(&key(t)) {
                break r;
            }
            path.push(t);
            let t1 = self.whnf_core(t)?;
            if let Some(n) = self.reduce_nat(t1)? {
                break n;
            }
            match self.unfold(t1)? {
                Some(n) => t = n,
                None => break t1,
            }
        };
        for p in path {
            self.t.whnf_cache.insert(key(p), r);
        }
        Ok(r)
    }

    pub(crate) fn delta_hint(&self, v: V<'t>) -> Option<Hint> {
        let K::Neu(Head::Const(n, ls), _) = v.k else {
            return None;
        };
        let d = self.declar(n)?;
        let (_, h) = d.unfoldable()?;
        (ls.len() == d.uparams().len()).then_some(h)
    }

    pub(crate) fn unfold(&mut self, v: V<'t>) -> R<Option<V<'t>>> {
        if let Some(&r) = self.t.unfold_cache.get(&key(v)) {
            return Ok(r);
        }
        let r = self.unfold_uncached(v)?;
        self.t.unfold_cache.insert(key(v), r);
        Ok(r)
    }

    fn unfold_uncached(&mut self, v: V<'t>) -> R<Option<V<'t>>> {
        let K::Neu(Head::Const(n, ls), args) = v.k else {
            return Ok(None);
        };
        let Some(d) = self.declar(n) else {
            return Ok(None);
        };
        let Some((body, _)) = d.unfoldable() else {
            return Ok(None);
        };
        #[cfg(feature = "vstats")]
        {
            *self.unfolded.entry(n).or_default() += 1;
        }
        if ls.len() != d.uparams().len() {
            return Ok(None);
        }
        stat!(self, unfolds);
        let f = match self.t.delta.get(&(n, ls)) {
            Some(&f) => f,
            None => {
                let f = self.eval_at(d.uparams(), ls, body)?;
                self.t.delta.insert((n, ls), f);
                f
            }
        };
        Ok(Some(self.apply(f, args)?))
    }

    fn reduce_proj(&mut self, idx: u16, s: V<'t>) -> R<Option<V<'t>>> {
        let mut c = self.whnf(s)?;
        if let K::Str(x) = c.k {
            let e = self.str_to_ctor(x)?;
            c = self.whnf(e)?;
        }
        let K::Neu(Head::Const(n, _), args) = c.k else {
            return Ok(None);
        };
        let Some(Declar::Ctor(k)) = self.declar(n) else {
            return Ok(None);
        };
        Ok(args
            .get(usize::from(k.num_params) + usize::from(idx))
            .copied())
    }

    fn reduce_rec(
        &mut self,
        n: NamePtr<'t>,
        ls: LevelsPtr<'t>,
        args: &'t [V<'t>],
    ) -> R<Option<V<'t>>> {
        let n0 = Some(n);
        if n0 == self.names.quot_lift {
            return self.reduce_quot(args, QUOT_LIFT_MAJOR);
        }
        if n0 == self.names.quot_ind {
            return self.reduce_quot(args, QUOT_IND_MAJOR);
        }
        match self.declar(n) {
            Some(Declar::Rec(r)) => self.reduce_ind_rec(r, ls, args),
            _ => Ok(None),
        }
    }

    fn reduce_quot(&mut self, args: &'t [V<'t>], mk_pos: usize) -> R<Option<V<'t>>> {
        let Some(&m) = args.get(mk_pos) else {
            return Ok(None);
        };
        let mk = self.whnf(m)?;
        let K::Neu(Head::Const(c, _), margs) = mk.k else {
            return Ok(None);
        };
        if margs.len() != QUOT_MK_ARITY || Some(c) != self.names.quot_mk {
            return Ok(None);
        }
        let r = self.apply(args[QUOT_FN], &margs[QUOT_MK_ARITY - 1..])?;
        Ok(Some(self.apply(r, &args[mk_pos + 1..])?))
    }

    fn reduce_ind_rec(
        &mut self,
        rec: Recursor<'t>,
        ls: LevelsPtr<'t>,
        args: &'t [V<'t>],
    ) -> R<Option<V<'t>>> {
        let mi = rec.major_idx();
        let Some(&m) = args.get(mi) else {
            return Ok(None);
        };
        let mut major = m;
        if rec.is_k {
            major = self.expose_ctor_when_k(&rec, major)?;
        }
        major = self.whnf(major)?;
        match major.k {
            K::Nat(x) => major = self.nat_to_ctor(x)?,
            K::Str(x) => {
                let e = self.str_to_ctor(x)?;
                major = self.whnf(e)?;
            }
            _ => {
                if let Some(ind) = self.rec_induct(&rec) {
                    major = self.expose_ctor_when_structure(ind, major)?;
                }
            }
        }
        let K::Neu(Head::Const(cname, _), margs) = major.k else {
            return Ok(None);
        };
        let Some(ri) = rec.rules.iter().position(|r| r.ctor == cname) else {
            return Ok(None);
        };
        let rule = rec.rules[ri];
        let nf = usize::from(rule.nfields);
        if margs.len() < nf || ls.len() != rec.info.uparams.len() {
            return Ok(None);
        }
        let rhs = match self.t.rules.get(&(rec.info.name, ri, ls)) {
            Some(&v) => v,
            None => {
                let v = self.eval_at(rec.info.uparams, ls, rule.rhs)?;
                self.t.rules.insert((rec.info.name, ri, ls), v);
                v
            }
        };
        let np = usize::from(rec.num_params)
            + usize::from(rec.num_motives)
            + usize::from(rec.num_minors);
        let mut all = SmallVec::<[V<'t>; 16]>::from_slice(&args[..np]);
        all.extend_from_slice(&margs[margs.len() - nf..]);
        all.extend_from_slice(&args[mi + 1..]);
        Ok(Some(self.apply(rhs, &all)?))
    }

    fn expose_ctor_when_k(&mut self, rec: &Recursor<'t>, e: V<'t>) -> R<V<'t>> {
        let Some(ind) = self.rec_induct(rec) else {
            return Ok(e);
        };
        let t = self.type_of(e)?;
        let t = self.whnf(t)?;
        let K::Neu(Head::Const(n, ls), targs) = t.k else {
            return Ok(e);
        };
        let np = usize::from(rec.num_params);
        if n != ind || targs.len() < np {
            return Ok(e);
        }
        let c = self.mk(K::Neu(Head::Const(rec.rules[0].ctor, ls), &[]), false);
        let nc = self.apply(c, &targs[..np])?;
        let nt = self.type_of(nc)?;
        Ok(if self.def_eq(t, nt)? { nc } else { e })
    }

    pub(crate) fn expose_ctor_when_structure(&mut self, ind: NamePtr<'t>, e: V<'t>) -> R<V<'t>> {
        let Some((i, c)) = self.structure_like(ind) else {
            return Ok(e);
        };
        if let K::Neu(Head::Const(n, _), _) = e.k
            && matches!(self.declar(n), Some(Declar::Ctor(_)))
        {
            return Ok(e);
        }
        let t = self.type_of(e)?;
        let t = self.whnf(t)?;
        let K::Neu(Head::Const(n, ls), targs) = t.k else {
            return Ok(e);
        };
        if n != ind || self.is_prop(t)? {
            return Ok(e);
        }
        let mut all = SmallVec::<[V<'t>; 16]>::from_slice(
            &targs[..usize::from(i.num_params).min(targs.len())],
        );
        for f in 0..c.num_fields {
            all.push(self.mk(K::Neu(Head::Proj(ind, f, e), &[]), e.open));
        }
        let k = self.mk(K::Neu(Head::Const(c.info.name, ls), &[]), false);
        self.apply(k, &all)
    }

    pub(crate) fn nat_to_ctor(&mut self, n: &'t BigUint) -> R<V<'t>> {
        if n.is_zero() {
            return Ok(self.konst0(self.names.nat_zero));
        }
        let s = self.konst0(self.names.nat_succ);
        let p = self.nat(n - 1u32);
        self.apply(s, &[p])
    }

    pub(crate) fn nat(&mut self, n: BigUint) -> V<'t> {
        stat!(self, nat_req);
        if let Some(&v) = self.t.nats.get(&n) {
            return v;
        }
        let p = self.ctx.arena.alloc_nat(n.clone());
        let v = &*self.ctx.arena.alloc(Val {
            k: K::Nat(p),
            open: false,
        });
        self.t.nats.insert(n, v);
        v
    }

    pub(crate) fn str_to_ctor(&mut self, s: &'t str) -> R<V<'t>> {
        let z = self.ctx.zero();
        let l0 = self.ctx.levels(&[z]);
        let ch = self.konst0(self.names.char);
        let of_nat = self.konst0(self.names.char_of_nat);
        let (Some(nil), Some(cons)) = (self.names.list_nil, self.names.list_cons) else {
            reject!("missing builtin constant")
        };
        let nil = self.mk(K::Neu(Head::Const(nil, l0), &[]), false);
        let cons = self.mk(K::Neu(Head::Const(cons, l0), &[]), false);
        let mut out = self.apply(nil, &[ch])?;
        for c in s.chars().rev() {
            let n = self.nat(BigUint::from(c as u32));
            let x = self.apply(of_nat, &[n])?;
            out = self.apply(cons, &[ch, x, out])?;
        }
        let f = self.konst0(self.names.string_of_list);
        self.apply(f, &[out])
    }

    fn nat_val(&mut self, v: V<'t>) -> R<Option<BigUint>> {
        let w = self.whnf(v)?;
        Ok(match w.k {
            K::Nat(n) => Some(n.clone()),
            K::Neu(Head::Const(n, _), []) if Some(n) == self.names.nat_zero => {
                Some(BigUint::zero())
            }
            _ => None,
        })
    }

    pub(crate) fn reduce_nat(&mut self, v: V<'t>) -> R<Option<V<'t>>> {
        if v.open {
            return Ok(None);
        }
        let K::Neu(Head::Const(n, _), args) = v.k else {
            return Ok(None);
        };
        if args.is_empty() || args.len() > 2 {
            return Ok(None);
        }
        let Some(op) = n.nat_red() else {
            return Ok(None);
        };
        if args.len() == 1 {
            if !nat::is_unary(op) {
                return Ok(None);
            }
            let Some(x) = self.nat_val(args[0])? else {
                return Ok(None);
            };
            let Some(r) = nat::unary(op, x) else {
                return Ok(None);
            };
            return Ok(Some(self.nat(r)));
        }
        if nat::is_unary(op) {
            return Ok(None);
        }
        let Some(x) = self.nat_val(args[0])? else {
            return Ok(None);
        };
        let Some(y) = self.nat_val(args[1])? else {
            return Ok(None);
        };
        let Some(r) = nat::binary(op, x, y) else {
            return Ok(None);
        };
        Ok(Some(match r {
            NatValue::Nat(r) => self.nat(r),
            NatValue::Bool(true) => self.konst0(self.names.bool_true),
            NatValue::Bool(false) => self.konst0(self.names.bool_false),
        }))
    }
}
