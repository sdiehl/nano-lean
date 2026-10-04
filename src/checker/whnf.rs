use super::Tc;
use crate::term::decl::{Declar, Hint, Recursor};
use crate::term::expr::Expr;
use crate::term::name::NatRed;
use crate::term::ptr::{BigUintPtr, ExprPtr, LevelsPtr, StringPtr};
use num_bigint::BigUint;
use num_integer::Integer;
use num_traits::{ToPrimitive, Zero};

const BIG_EXP: u64 = 1 << 24;

impl<'t, 'a: 't> Tc<'t, 'a> {
    pub fn whnf_core(&mut self, e: ExprPtr<'t>) -> ExprPtr<'t> {
        self.tick();
        if !matches!(*e, Expr::App { .. } | Expr::Let { .. } | Expr::Proj { .. }) {
            return e;
        }
        if let Some(&r) = self.whnf_core_cache.get(&e) {
            return r;
        }
        let r = match *e {
            Expr::Let { .. } => {
                let mut values = Vec::new();
                let mut body = e;
                while let Expr::Let { data, .. } = *body {
                    self.tick();
                    values.push(self.ctx.inst(data.val, &values));
                    body = data.body;
                }
                let body = self.ctx.inst(body, &values);
                self.whnf_core(body)
            }
            Expr::App { .. } => {
                let (f0, args) = self.ctx.unfold_apps(e);
                let f = self.whnf_core(f0);
                if f.is_lambda() {
                    let mut m = 0;
                    let mut b = f;
                    while m < args.len()
                        && let Expr::Lam { body, .. } = *b
                    {
                        b = body;
                        m += 1;
                    }
                    let b = self.reduce_binders(b, args[..m].to_vec());
                    let r = self.ctx.apps(b, &args[m..]);
                    self.whnf_core(r)
                } else if f == f0 {
                    match self.reduce_rec(f, &args) {
                        Some(r) => self.whnf_core(r),
                        None => e,
                    }
                } else {
                    let r = self.ctx.apps(f, &args);
                    self.whnf_core(r)
                }
            }
            Expr::Proj { idx, e: s, .. } => match self.reduce_proj(idx, s) {
                Some(r) => self.whnf_core(r),
                None => e,
            },
            _ => unreachable!(),
        };
        self.whnf_core_cache.insert(e, r);
        r
    }

    /// Keep substitutions outside the body while exposing adjacent beta/let
    /// steps. Materialize only when another reduction rule needs syntax.
    fn reduce_binders(&mut self, mut body: ExprPtr<'t>, mut env: Vec<ExprPtr<'t>>) -> ExprPtr<'t> {
        loop {
            self.tick();
            match *body {
                Expr::Let { data, .. } => {
                    let value = self.ctx.inst(data.val, &env);
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
                        values.push(self.ctx.inst(args[consumed], &env));
                        consumed += 1;
                        head = next;
                    }
                    if consumed == args.len() {
                        env.extend(values);
                        body = head;
                    } else {
                        return self.ctx.inst(body, &env);
                    }
                }
                _ => return self.ctx.inst(body, &env),
            }
        }
    }

    pub fn whnf(&mut self, e: ExprPtr<'t>) -> ExprPtr<'t> {
        if matches!(
            *e,
            Expr::Var { .. }
                | Expr::Sort { .. }
                | Expr::Pi { .. }
                | Expr::Lam { .. }
                | Expr::NatLit { .. }
                | Expr::StrLit { .. }
                | Expr::Local { .. }
        ) {
            return e;
        }
        if let Some(&r) = self.whnf_cache.get(&e) {
            return r;
        }
        let mut t = e;
        let mut path = Vec::new();
        let r = loop {
            self.tick();
            if let Some(&r) = self.whnf_cache.get(&t) {
                break r;
            }
            path.push(t);
            let t1 = self.whnf_core(t);
            if let Some(v) = self.reduce_nat(t1) {
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
        r
    }

    /// Hint of the unfoldable constant at the head of `e`.
    pub(crate) fn delta_hint(&self, e: ExprPtr<'t>) -> Option<Hint> {
        let Expr::Const { name, levels, .. } = *e.head() else {
            return None;
        };
        let d = self.declar(name)?;
        let (_, h) = d.unfoldable()?;
        (levels.len() == d.uparams().len()).then_some(h)
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

    fn reduce_proj(&mut self, idx: u16, s: ExprPtr<'t>) -> Option<ExprPtr<'t>> {
        // Expose the structure even during cheap reduction. Otherwise a hidden
        // operation can make conversion unfold its visible counterpart too early.
        let mut c = self.whnf(s);
        if let Expr::StrLit { s, .. } = *c {
            let x = self.str_to_ctor(s);
            c = self.whnf(x);
        }
        let Expr::Const { name, .. } = *c.head() else {
            return None;
        };
        let Some(Declar::Ctor(k)) = self.declar(name) else {
            return None;
        };
        let (_, args) = self.ctx.unfold_apps(c);
        args.get(usize::from(k.num_params) + usize::from(idx))
            .copied()
    }

    fn reduce_rec(&mut self, f: ExprPtr<'t>, args: &[ExprPtr<'t>]) -> Option<ExprPtr<'t>> {
        let Expr::Const { name, levels, .. } = *f else {
            return None;
        };
        let n = Some(name);
        if n == self.names.quot_lift {
            return self.reduce_quot(args, 5, 3);
        }
        if n == self.names.quot_ind {
            return self.reduce_quot(args, 4, 3);
        }
        match self.declar(name) {
            Some(Declar::Rec(r)) => self.reduce_ind_rec(r, levels, args),
            _ => None,
        }
    }

    fn reduce_quot(
        &mut self,
        args: &[ExprPtr<'t>],
        mk_pos: usize,
        arg_pos: usize,
    ) -> Option<ExprPtr<'t>> {
        let mk = self.whnf(*args.get(mk_pos)?);
        let Expr::App { arg, .. } = *mk else {
            return None;
        };
        if mk.num_args() != 3 || mk.head().const_name() != self.names.quot_mk {
            return None;
        }
        let r = self.ctx.app(args[arg_pos], arg);
        Some(self.ctx.apps(r, &args[mk_pos + 1..]))
    }

    fn reduce_ind_rec(
        &mut self,
        rec: Recursor<'t>,
        levels: LevelsPtr<'t>,
        args: &[ExprPtr<'t>],
    ) -> Option<ExprPtr<'t>> {
        let mi = rec.major_idx();
        let mut major = *args.get(mi)?;
        if rec.is_k {
            major = self.expose_ctor_when_k(&rec, major);
        }
        major = self.whnf(major);
        match *major {
            Expr::NatLit { n, .. } => major = self.nat_to_ctor(n),
            Expr::StrLit { s, .. } => {
                let x = self.str_to_ctor(s);
                major = self.whnf(x);
            }
            _ => {
                if let Some(ind) = self.rec_induct(&rec) {
                    major = self.expose_ctor_when_structure(ind, major);
                }
            }
        }
        let Expr::Const { name: cname, .. } = *major.head() else {
            return None;
        };
        let mut canonical = args.to_vec();
        canonical[mi] = major;
        let key = (rec.info.name, levels, canonical);
        if let Some(&result) = self.rec_cache.get(&key) {
            return Some(result);
        }
        let rule = rec.rules.iter().find(|r| r.ctor == cname)?;
        let (_, margs) = self.ctx.unfold_apps(major);
        let nf = usize::from(rule.nfields);
        if margs.len() < nf || levels.len() != rec.info.uparams.len() {
            return None;
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
        Some(result)
    }

    fn rec_induct(&self, rec: &Recursor<'t>) -> Option<crate::term::ptr::NamePtr<'t>> {
        match self.declar(rec.rules.first()?.ctor)? {
            Declar::Ctor(c) => Some(c.induct),
            _ => None,
        }
    }

    fn expose_ctor_when_k(&mut self, rec: &Recursor<'t>, e: ExprPtr<'t>) -> ExprPtr<'t> {
        let Some(ind) = self.rec_induct(rec) else {
            return e;
        };
        let t = self.infer(e, true);
        let t = self.whnf(t);
        let Expr::Const { name, levels, .. } = *t.head() else {
            return e;
        };
        if name != ind {
            return e;
        }
        let (_, targs) = self.ctx.unfold_apps(t);
        let np = usize::from(rec.num_params);
        if targs.len() < np {
            return e;
        }
        let c = self.ctx.konst(rec.rules[0].ctor, levels);
        let nc = self.ctx.apps(c, &targs[..np]);
        let nt = self.infer(nc, true);
        if self.def_eq(t, nt) { nc } else { e }
    }

    pub(crate) fn expose_ctor_when_structure(
        &mut self,
        ind: crate::term::ptr::NamePtr<'t>,
        e: ExprPtr<'t>,
    ) -> ExprPtr<'t> {
        let Some((i, c)) = self.structure_like(ind) else {
            return e;
        };
        if let Expr::Const { name, .. } = *e.head()
            && matches!(self.declar(name), Some(Declar::Ctor(_)))
        {
            return e;
        }
        let t = self.infer(e, true);
        let t = self.whnf(t);
        let Expr::Const { name, levels, .. } = *t.head() else {
            return e;
        };
        if name != ind {
            return e;
        }
        if self.is_prop(t) {
            return e;
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
        r
    }

    pub(crate) fn nat_to_ctor(&mut self, n: BigUintPtr<'t>) -> ExprPtr<'t> {
        if n.is_zero() {
            return self.konst0(self.names.nat_zero);
        }
        let s = self.konst0(self.names.nat_succ);
        let p = self.ctx.nat_lit(n.as_ref() - 1u32);
        self.ctx.app(s, p)
    }

    pub(crate) fn str_to_ctor(&mut self, s: StringPtr<'t>) -> ExprPtr<'t> {
        let z = self.ctx.zero();
        let l0 = self.ctx.levels(&[z]);
        let ch = self.konst0(self.names.char);
        let of_nat = self.konst0(self.names.char_of_nat);
        let (Some(nil), Some(cons)) = (self.names.list_nil, self.names.list_cons) else {
            crate::reject!("missing builtin constant")
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
        let f = self.konst0(self.names.string_of_list);
        self.ctx.app(f, out)
    }

    fn nat_val(&mut self, e: ExprPtr<'t>) -> Option<BigUint> {
        let w = self.whnf(e);
        match *w {
            Expr::NatLit { n, .. } => Some(n.as_ref().clone()),
            Expr::Const { name, .. } if Some(name) == self.names.nat_zero => Some(BigUint::zero()),
            _ => None,
        }
    }

    pub(crate) fn reduce_nat(&mut self, e: ExprPtr<'t>) -> Option<ExprPtr<'t>> {
        if e.has_local() {
            return None;
        }
        let Expr::App { fun, arg, .. } = *e else {
            return None;
        };
        let nargs = e.num_args();
        if nargs > 2 {
            return None;
        }
        let Expr::Const { name, .. } = *e.head() else {
            return None;
        };
        let op = name.nat_red()?;
        if nargs == 1 {
            let r = match op {
                NatRed::Succ => self.nat_val(arg)? + 1u32,
                NatRed::Log2 => {
                    let n = self.nat_val(arg)?;
                    BigUint::from(n.bits().saturating_sub(1))
                }
                _ => return None,
            };
            return Some(self.ctx.nat_lit(r));
        }
        let Expr::App { arg: a, .. } = *fun else {
            return None;
        };
        if matches!(op, NatRed::Succ | NatRed::Log2) {
            return None;
        }
        let x = self.nat_val(a)?;
        let y = self.nat_val(arg)?;
        let b = |tc: &mut Self, v: bool| {
            let n = if v {
                tc.names.bool_true
            } else {
                tc.names.bool_false
            };
            tc.konst0(n)
        };
        let r = match op {
            NatRed::Add => x + y,
            NatRed::Sub => {
                if x > y {
                    x - y
                } else {
                    BigUint::zero()
                }
            }
            NatRed::Mul => x * y,
            NatRed::Div => {
                if y.is_zero() {
                    y
                } else {
                    x / y
                }
            }
            NatRed::Mod => {
                if y.is_zero() {
                    x
                } else {
                    x % y
                }
            }
            NatRed::Gcd => x.gcd(&y),
            NatRed::Beq => return Some(b(self, x == y)),
            NatRed::Ble => return Some(b(self, x <= y)),
            NatRed::Land => x & y,
            NatRed::Lor => x | y,
            NatRed::Xor => x ^ y,
            NatRed::Shl => x << y.to_u64().filter(|&k| k <= BIG_EXP)?,
            NatRed::Shr => match y.to_u64() {
                Some(k) => x >> k,
                None => BigUint::zero(),
            },
            NatRed::Pow => x.pow(u32::try_from(y.to_u64().filter(|&k| k <= BIG_EXP)?).ok()?),
            NatRed::Succ | NatRed::Log2 => return None,
        };
        Some(self.ctx.nat_lit(r))
    }
}
