use super::Tc;
use super::env::Decls;
use super::nat::{self, NatValue};
use crate::reject;
use crate::term::decl::{Hint, Recursor};
use crate::term::expr::Expr;
use crate::term::names::{QUOT_FN, QUOT_MK_ARITY};
use crate::term::outcome::R;
use crate::term::ptr::{BigUintPtr, ExprPtr, LevelsPtr, NamePtr, StringPtr};
use num_bigint::BigUint;
use num_traits::Zero;

impl<'t, 'a: 't> Tc<'t, 'a> {
    pub fn whnf_core(&mut self, e: ExprPtr<'t>) -> R<ExprPtr<'t>> {
        self.tick()?;
        if !matches!(*e, Expr::App { .. } | Expr::Let { .. } | Expr::Proj { .. }) {
            if let Expr::Local { id, .. } = *e
                && !self.let_vals.is_empty()
            {
                return self.zeta_local(e, id);
            }
            return Ok(e);
        }
        if let Some(&r) = self.whnf_core_cache.get(&e) {
            return Ok(r);
        }
        let r = match *e {
            Expr::Let { .. } => {
                let mut values = Vec::new();
                let mut body = e;
                while let Expr::Let { data, .. } = *body {
                    self.tick()?;
                    let value = self.inst(data.val, &values)?;
                    values.push(value);
                    body = data.body;
                }
                let body = self.inst(body, &values)?;
                self.whnf_core(body)?
            }
            Expr::App { .. } => {
                let (f0, args) = self.ctx.unfold_apps(e);
                let f = self.whnf_core(f0)?;
                if f.is_lambda() {
                    let mut m = 0;
                    let mut b = f;
                    while m < args.len()
                        && let Expr::Lam { body, .. } = *b
                    {
                        b = body;
                        m += 1;
                    }
                    let b = self.reduce_binders(b, args[..m].to_vec())?;
                    let r = self.ctx.apps(b, &args[m..]);
                    self.whnf_core(r)?
                } else if f == f0 {
                    match self.reduce_rec(f, &args)? {
                        Some(r) => self.whnf_core(r)?,
                        None => e,
                    }
                } else {
                    let r = self.ctx.apps(f, &args);
                    self.whnf_core(r)?
                }
            }
            Expr::Proj { idx, e: s, .. } => match self.reduce_proj(idx, s)? {
                Some(r) => self.whnf_core(r)?,
                None => e,
            },
            _ => unreachable!(),
        };
        self.whnf_core_cache.insert(e, r);
        Ok(r)
    }

    #[cold]
    #[inline(never)]
    fn zeta_local(&mut self, e: ExprPtr<'t>, id: u32) -> R<ExprPtr<'t>> {
        match self.let_vals.get(&id) {
            Some(&v) => self.whnf_core(v),
            None => Ok(e),
        }
    }

    /// Keeps substitutions outside the body across beta and let until syntax is needed.
    fn reduce_binders(
        &mut self,
        mut body: ExprPtr<'t>,
        mut env: Vec<ExprPtr<'t>>,
    ) -> R<ExprPtr<'t>> {
        loop {
            self.tick()?;
            match *body {
                Expr::Let { data, .. } => {
                    let value = self.inst(data.val, &env)?;
                    env.push(value);
                    body = data.body;
                }
                Expr::App { .. } => {
                    let (mut head, args) = self.ctx.unfold_apps(body);
                    let mut consumed = 0;
                    let mut values = Vec::new();
                    while consumed < args.len() {
                        let Expr::Lam { body: next, .. } = *head else {
                            break;
                        };
                        values.push(self.inst(args[consumed], &env)?);
                        consumed += 1;
                        head = next;
                    }
                    if consumed == args.len() {
                        env.extend(values);
                        body = head;
                    } else {
                        return self.inst(body, &env);
                    }
                }
                _ => return self.inst(body, &env),
            }
        }
    }

    pub fn whnf(&mut self, e: ExprPtr<'t>) -> R<ExprPtr<'t>> {
        if matches!(
            *e,
            Expr::Var { .. }
                | Expr::Sort { .. }
                | Expr::Pi { .. }
                | Expr::Lam { .. }
                | Expr::NatLit { .. }
                | Expr::StrLit { .. }
        ) {
            return Ok(e);
        }
        if let Expr::Local { id, .. } = *e
            && !self.let_vals.contains_key(&id)
        {
            return Ok(e);
        }
        if let Some(&r) = self.whnf_cache.get(&e) {
            return Ok(r);
        }
        let mut t = e;
        let mut path = Vec::new();
        let r = loop {
            self.tick()?;
            if let Some(&r) = self.whnf_cache.get(&t) {
                break r;
            }
            path.push(t);
            let t1 = self.whnf_core(t)?;
            if let Some(v) = self.reduce_nat(t1)? {
                break v;
            }
            match self.unfold(t1) {
                Some(n) => t = n,
                None => break t1,
            }
        };
        for node in path {
            self.whnf_cache.insert(node, r);
        }
        Ok(r)
    }

    pub(crate) fn delta_hint(&self, e: ExprPtr<'t>) -> Option<Hint> {
        let Expr::Const { name, levels, .. } = *e.head() else {
            return None;
        };
        self.hint(name, levels)
    }

    pub(crate) fn unfold(&mut self, e: ExprPtr<'t>) -> Option<ExprPtr<'t>> {
        if let Some(&result) = self.unfold_cache.get(&e) {
            return result;
        }
        let result = self.unfold_uncached(e);
        self.unfold_cache.insert(e, result);
        result
    }

    fn unfold_uncached(&mut self, e: ExprPtr<'t>) -> Option<ExprPtr<'t>> {
        let h = e.head();
        let Expr::Const { name, levels, .. } = *h else {
            return None;
        };
        let d = self.declar(name)?;
        let (v, _) = d.unfoldable()?;
        if levels.len() != d.uparams().len() {
            return None;
        }
        let v = self.ctx.subst_expr_levels(v, d.uparams(), levels);
        if h == e {
            return Some(v);
        }
        let (_, args) = self.ctx.unfold_apps(e);
        Some(self.ctx.apps(v, &args))
    }

    fn reduce_proj(&mut self, idx: u16, s: ExprPtr<'t>) -> R<Option<ExprPtr<'t>>> {
        // Exposing the structure here stops conversion unfolding its visible twin too early.
        let mut c = self.whnf(s)?;
        if let Expr::StrLit { s, .. } = *c {
            let x = self.str_to_ctor(s)?;
            c = self.whnf(x)?;
        }
        let Expr::Const { name, .. } = *c.head() else {
            return Ok(None);
        };
        let Some(k) = self.ctor(name) else {
            return Ok(None);
        };
        let (_, args) = self.ctx.unfold_apps(c);
        Ok(args
            .get(usize::from(k.num_params) + usize::from(idx))
            .copied())
    }

    fn reduce_rec(&mut self, f: ExprPtr<'t>, args: &[ExprPtr<'t>]) -> R<Option<ExprPtr<'t>>> {
        let Expr::Const { name, levels, .. } = *f else {
            return Ok(None);
        };
        if let Some(mk_pos) = self.quot_major(name) {
            return self.reduce_quot(args, mk_pos);
        }
        let Some(r) = self.recursor(name) else {
            return Ok(None);
        };
        self.reduce_ind_rec(r, levels, args)
    }

    fn reduce_quot(&mut self, args: &[ExprPtr<'t>], mk_pos: usize) -> R<Option<ExprPtr<'t>>> {
        let Some(&major) = args.get(mk_pos) else {
            return Ok(None);
        };
        let mk = self.whnf(major)?;
        let Expr::App { arg, .. } = *mk else {
            return Ok(None);
        };
        if mk.num_args() != QUOT_MK_ARITY || mk.head().const_name() != self.names.quot_mk {
            return Ok(None);
        }
        let r = self.ctx.app(args[QUOT_FN], arg);
        Ok(Some(self.ctx.apps(r, &args[mk_pos + 1..])))
    }

    fn reduce_ind_rec(
        &mut self,
        rec: Recursor<'t>,
        levels: LevelsPtr<'t>,
        args: &[ExprPtr<'t>],
    ) -> R<Option<ExprPtr<'t>>> {
        let mi = rec.major_idx();
        let Some(&major) = args.get(mi) else {
            return Ok(None);
        };
        let mut major = major;
        if rec.is_k {
            major = self.expose_ctor_when_k(&rec, major)?;
        }
        major = self.whnf(major)?;
        match *major {
            Expr::NatLit { n, .. } => major = self.nat_to_ctor(n)?,
            Expr::StrLit { s, .. } => {
                let x = self.str_to_ctor(s)?;
                major = self.whnf(x)?;
            }
            _ => {
                if let Some(ind) = self.rec_induct(&rec) {
                    major = self.expose_ctor_when_structure(ind, major)?;
                }
            }
        }
        let Expr::Const { name: cname, .. } = *major.head() else {
            return Ok(None);
        };
        let mut canonical = args.to_vec();
        canonical[mi] = major;
        let key = (rec.info.name, levels, canonical);
        if let Some(&result) = self.rec_cache.get(&key) {
            return Ok(Some(result));
        }
        let Some(rule) = rec.rules.iter().find(|r| r.ctor == cname) else {
            return Ok(None);
        };
        let (_, margs) = self.ctx.unfold_apps(major);
        let nf = usize::from(rule.nfields);
        if margs.len() < nf || levels.len() != rec.info.uparams.len() {
            return Ok(None);
        }
        let rhs = self
            .ctx
            .subst_expr_levels(rule.rhs, rec.info.uparams, levels);
        let np = usize::from(rec.num_params)
            + usize::from(rec.num_motives)
            + usize::from(rec.num_minors);
        let rhs = self.ctx.apps(rhs, &args[..np]);
        let rhs = self.ctx.apps(rhs, &margs[margs.len() - nf..]);
        let result = self.ctx.apps(rhs, &args[mi + 1..]);
        self.rec_cache.insert(key, result);
        Ok(Some(result))
    }

    fn expose_ctor_when_k(&mut self, rec: &Recursor<'t>, e: ExprPtr<'t>) -> R<ExprPtr<'t>> {
        let Some(ind) = self.rec_induct(rec) else {
            return Ok(e);
        };
        let t = self.infer(e, true)?;
        let t = self.whnf(t)?;
        let Expr::Const { name, levels, .. } = *t.head() else {
            return Ok(e);
        };
        if name != ind {
            return Ok(e);
        }
        let (_, targs) = self.ctx.unfold_apps(t);
        let np = usize::from(rec.num_params);
        if targs.len() < np {
            return Ok(e);
        }
        let c = self.ctx.konst(rec.rules[0].ctor, levels);
        let nc = self.ctx.apps(c, &targs[..np]);
        let nt = self.infer(nc, true)?;
        Ok(if self.def_eq(t, nt)? { nc } else { e })
    }

    pub(crate) fn expose_ctor_when_structure(
        &mut self,
        ind: NamePtr<'t>,
        e: ExprPtr<'t>,
    ) -> R<ExprPtr<'t>> {
        let Some((i, c)) = self.structure_like(ind) else {
            return Ok(e);
        };
        if let Expr::Const { name, .. } = *e.head()
            && self.ctor(name).is_some()
        {
            return Ok(e);
        }
        let t = self.infer(e, true)?;
        let t = self.whnf(t)?;
        let Expr::Const { name, levels, .. } = *t.head() else {
            return Ok(e);
        };
        if name != ind {
            return Ok(e);
        }
        if self.is_prop(t)? {
            return Ok(e);
        }
        let (_, targs) = self.ctx.unfold_apps(t);
        let k = self.ctx.konst(c.info.name, levels);
        let mut r = self
            .ctx
            .apps(k, &targs[..usize::from(i.num_params).min(targs.len())]);
        for f in 0..c.num_fields {
            let p = self.ctx.proj(ind, f, e);
            r = self.ctx.app(r, p);
        }
        Ok(r)
    }

    pub(crate) fn nat_to_ctor(&mut self, n: BigUintPtr<'t>) -> R<ExprPtr<'t>> {
        if n.is_zero() {
            return self.konst0(self.names.nat_zero);
        }
        let s = self.konst0(self.names.nat_succ)?;
        let p = self.ctx.nat_lit(n.as_ref() - 1u32);
        Ok(self.ctx.app(s, p))
    }

    pub(crate) fn str_to_ctor(&mut self, s: StringPtr<'t>) -> R<ExprPtr<'t>> {
        let z = self.ctx.zero();
        let l0 = self.ctx.levels(&[z]);
        let ch = self.konst0(self.names.char)?;
        let of_nat = self.konst0(self.names.char_of_nat)?;
        let (Some(nil), Some(cons)) = (self.names.list_nil, self.names.list_cons) else {
            reject!(self, "missing builtin constant")
        };
        let nil = self.ctx.konst(nil, l0);
        let cons = self.ctx.konst(cons, l0);
        let mut out = self.ctx.app(nil, ch);
        let cons = self.ctx.app(cons, ch);
        for c in s.s.chars().rev() {
            let n = self.ctx.nat_lit(BigUint::from(c as u32));
            let x = self.ctx.app(of_nat, n);
            let y = self.ctx.app(cons, x);
            out = self.ctx.app(y, out);
        }
        let f = self.konst0(self.names.string_of_list)?;
        Ok(self.ctx.app(f, out))
    }

    fn nat_val(&mut self, e: ExprPtr<'t>) -> R<Option<BigUint>> {
        let w = self.whnf(e)?;
        Ok(match *w {
            Expr::NatLit { n, .. } => Some(n.as_ref().clone()),
            Expr::Const { name, .. } if Some(name) == self.names.nat_zero => Some(BigUint::zero()),
            _ => None,
        })
    }

    pub(crate) fn reduce_nat(&mut self, e: ExprPtr<'t>) -> R<Option<ExprPtr<'t>>> {
        if e.has_local() {
            return Ok(None);
        }
        let Expr::App { fun, arg, .. } = *e else {
            return Ok(None);
        };
        let nargs = e.num_args();
        if nargs > 2 {
            return Ok(None);
        }
        let Expr::Const { name, .. } = *e.head() else {
            return Ok(None);
        };
        let Some(op) = name.nat_red() else {
            return Ok(None);
        };
        if nargs == 1 {
            if !nat::is_unary(op) {
                return Ok(None);
            }
            let Some(x) = self.nat_val(arg)? else {
                return Ok(None);
            };
            return Ok(nat::unary(op, x).map(|r| self.ctx.nat_lit(r)));
        }
        let Expr::App { arg: a, .. } = *fun else {
            return Ok(None);
        };
        if nat::is_unary(op) {
            return Ok(None);
        }
        let Some(x) = self.nat_val(a)? else {
            return Ok(None);
        };
        let Some(y) = self.nat_val(arg)? else {
            return Ok(None);
        };
        Ok(Some(match nat::binary(op, x, y) {
            None => return Ok(None),
            Some(NatValue::Nat(r)) => self.ctx.nat_lit(r),
            Some(NatValue::Bool(true)) => self.konst0(self.names.bool_true)?,
            Some(NatValue::Bool(false)) => self.konst0(self.names.bool_false)?,
        }))
    }
}
