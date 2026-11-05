use super::Tc;
use super::env::Decls;
use crate::kernel;
use crate::term::FxHashSet;
use crate::term::decl::{Constructor, Declar, Inductive, Recursor};
use crate::term::expr::Expr;
use crate::term::intern::Block;
use crate::term::outcome::R;
use crate::term::ptr::{ExprPtr, LevelPtr, LevelsPtr, NamePtr};
use crate::value_checker::RecCheck;
use crate::{ensure, reject};
use std::ops::Range;

mod recursor;

fn spine(mut e: ExprPtr<'_>) -> (ExprPtr<'_>, Vec<ExprPtr<'_>>) {
    let mut args = Vec::new();
    while let Expr::App { fun, arg, .. } = *e {
        args.push(arg);
        e = fun;
    }
    args.reverse();
    (e, args)
}

fn local_ty(x: ExprPtr<'_>) -> ExprPtr<'_> {
    match *x {
        Expr::Local { ty, .. } => ty,
        _ => unreachable!(),
    }
}

/// The block's types followed by the auxiliary types Lean would add for nested occurrences.
/// An auxiliary member is a local standing for `J Ds` applied to the block parameters, so the
/// expanded block is checked in place and the local is restored to `J Ds` in recursor terms.
struct Family<'t> {
    names: Vec<NamePtr<'t>>,
    aux: Vec<ExprPtr<'t>>,
    apps: Vec<ExprPtr<'t>>,
    num_indices: Vec<usize>,
    levels: LevelsPtr<'t>,
    params: Vec<ExprPtr<'t>>,
}

impl<'t> Family<'t> {
    fn occurs(&self, e: ExprPtr<'t>) -> bool {
        fn go<'t>(f: &Family<'t>, e: ExprPtr<'t>, seen: &mut FxHashSet<ExprPtr<'t>>) -> bool {
            if !seen.insert(e) {
                return false;
            }
            match *e {
                Expr::Const { name, .. } => f.names.contains(&name),
                Expr::Local { .. } => f.aux.contains(&e),
                Expr::App { fun, arg, .. } => go(f, fun, seen) || go(f, arg, seen),
                Expr::Lam { ty, body, .. } | Expr::Pi { ty, body, .. } => {
                    go(f, ty, seen) || go(f, body, seen)
                }
                Expr::Let { data, .. } => {
                    go(f, data.ty, seen) || go(f, data.val, seen) || go(f, data.body, seen)
                }
                Expr::Proj { e, .. } => go(f, e, seen),
                _ => false,
            }
        }
        go(self, e, &mut FxHashSet::default())
    }

    fn application(&self, e: ExprPtr<'t>) -> Option<(usize, Vec<ExprPtr<'t>>)> {
        let (head, args) = spine(e);
        let (i, np) = match *head {
            Expr::Const { name, levels, .. } => {
                let i = self.names.iter().position(|&n| n == name)?;
                let np = self.params.len();
                if levels != self.levels || args.len() < np || args[..np] != self.params[..] {
                    return None;
                }
                (i, np)
            }
            Expr::Local { .. } => {
                let k = self.aux.iter().position(|&a| a == head)?;
                (self.names.len() + k, 0)
            }
            _ => return None,
        };
        if args.len() != np + self.num_indices[i] {
            return None;
        }
        let indices = args[np..].to_vec();
        (!indices.iter().any(|&e| self.occurs(e))).then_some((i, indices))
    }
}

struct Nested<'t> {
    ind: Inductive<'t>,
    levels: LevelsPtr<'t>,
    ds: Vec<ExprPtr<'t>>,
    indices: Vec<ExprPtr<'t>>,
}

struct Shape<'t> {
    name: NamePtr<'t>,
    head: ExprPtr<'t>,
    fields: Vec<ExprPtr<'t>>,
    levels: Vec<LevelPtr<'t>>,
    indices: Vec<ExprPtr<'t>>,
    owner: usize,
}

struct RecField<'t> {
    field: ExprPtr<'t>,
    locals: Vec<ExprPtr<'t>>,
    owner: usize,
    indices: Vec<ExprPtr<'t>>,
}

struct Members<'t> {
    types: Vec<Inductive<'t>>,
    ctors: Vec<Constructor<'t>>,
    recs: Vec<Recursor<'t>>,
}

struct Spec<'t> {
    fam: Family<'t>,
    types: Vec<Inductive<'t>>,
    indices: Vec<Vec<ExprPtr<'t>>>,
    shapes: Vec<Shape<'t>>,
}

struct Elim<'t> {
    level: LevelPtr<'t>,
    uparams: LevelsPtr<'t>,
    k: bool,
}

struct Premises<'t> {
    motives: Vec<ExprPtr<'t>>,
    majors: Vec<ExprPtr<'t>>,
    minors: Vec<ExprPtr<'t>>,
    recursive_fields: Vec<Vec<RecField<'t>>>,
}

/// Constructor checking state shared across the block's members.
struct Ctors<'t> {
    result_level: LevelPtr<'t>,
    zero: bool,
    recursive: bool,
    reflexive: bool,
    nested: Vec<Nested<'t>>,
}

impl<'t, 'a: 't> Tc<'t, 'a> {
    fn members<T>(&mut self, r: Range<u32>, pick: impl Fn(Declar<'t>) -> Option<T>) -> R<Vec<T>> {
        let declars: &[Declar<'t>] = &self.ctx.store.declars[r.start as usize..r.end as usize];
        let mut out = Vec::with_capacity(declars.len());
        for &d in declars {
            let Some(member) = pick(d) else {
                reject!(self, "malformed inductive block")
            };
            out.push(member);
        }
        Ok(out)
    }

    fn sort_of(&mut self, e: ExprPtr<'t>) -> R<LevelPtr<'t>> {
        let s = self.infer(e, false)?;
        self.ensure_sort(s)
    }

    fn level_of(&mut self, e: ExprPtr<'t>) -> R<LevelPtr<'t>> {
        let s = self.infer(e, true)?;
        self.ensure_sort(s)
    }

    /// Pi bodies stay unsubstituted until a non-Pi needs whnf, so a binder costs its domain only.
    fn telescope(&mut self, e: ExprPtr<'t>) -> R<(Vec<ExprPtr<'t>>, ExprPtr<'t>)> {
        let mut e = self.whnf(e)?;
        let mut xs = Vec::new();
        let mut open = 0;
        loop {
            if let Expr::Pi { ty, body, .. } = *e {
                let ty = self.inst(ty, &xs[xs.len() - open..])?;
                let ty = self.binder_ty(ty);
                xs.push(self.fresh_local(ty));
                open += 1;
                e = body;
            } else if open > 0 {
                let b = self.inst(e, &xs[xs.len() - open..])?;
                e = self.whnf(b)?;
                open = 0;
            } else {
                return Ok((xs, e));
            }
        }
    }

    /// Lean opens binders without their `outParam`, `optParam` and `autoParam` gadgets, so the
    /// recursor it generates has none; ours must match it binder for binder.
    fn binder_ty(&self, mut ty: ExprPtr<'t>) -> ExprPtr<'t> {
        let n = &self.ctx.store.names;
        loop {
            let (head, args) = (ty.head(), ty.num_args());
            let Some(c) = head.const_name() else {
                return ty;
            };
            let keep = if args == 1 && (Some(c) == n.out_param || Some(c) == n.semi_out_param) {
                0
            } else if args == 2 && (Some(c) == n.opt_param || Some(c) == n.auto_param) {
                1
            } else {
                return ty;
            };
            let mut e = ty;
            for _ in 0..keep {
                let Expr::App { fun, .. } = *e else {
                    unreachable!()
                };
                e = fun;
            }
            let Expr::App { arg, .. } = *e else {
                unreachable!()
            };
            ty = arg;
        }
    }

    fn open_params(
        &mut self,
        mut ty: ExprPtr<'t>,
        count: u16,
        params: &mut Vec<ExprPtr<'t>>,
    ) -> R<ExprPtr<'t>> {
        for _ in 0..count {
            let w = self.whnf(ty)?;
            let Expr::Pi { ty: d, body, .. } = *w else {
                reject!(self, "missing inductive parameter")
            };
            let d = self.binder_ty(d);
            let x = self.fresh_local(d);
            ty = self.inst1(body, x)?;
            params.push(x);
        }
        Ok(ty)
    }

    fn consume_params(&mut self, mut ty: ExprPtr<'t>, params: &[ExprPtr<'t>]) -> R<ExprPtr<'t>> {
        for &x in params {
            let w = self.whnf(ty)?;
            let Expr::Pi { ty: d, body, .. } = *w else {
                reject!(self, "missing inductive parameter")
            };
            ensure!(
                self,
                self.def_eq(d, local_ty(x))?,
                "inductive parameter type mismatch"
            );
            ty = self.inst1(body, x)?;
        }
        Ok(ty)
    }

    fn instantiate_params(
        &mut self,
        mut ty: ExprPtr<'t>,
        count: u16,
        ds: &[ExprPtr<'t>],
    ) -> R<ExprPtr<'t>> {
        for _ in 0..count {
            let Expr::Pi { body, .. } = *ty else {
                reject!(self, "missing nested inductive parameter")
            };
            ty = body;
        }
        self.inst(ty, ds)
    }

    /// Auxiliary locals back to the nested applications they stand for.
    fn restore(&mut self, fam: &Family<'t>, e: ExprPtr<'t>) -> R<ExprPtr<'t>> {
        if fam.aux.is_empty() {
            return Ok(e);
        }
        let a = self.ctx.abstract_locals(e, &fam.aux);
        self.inst(a, &fam.apps)
    }

    fn bind(
        &mut self,
        fam: &Family<'t>,
        xs: &[ExprPtr<'t>],
        body: ExprPtr<'t>,
        lam: bool,
    ) -> R<ExprPtr<'t>> {
        self.bind_after(fam, &[], xs, body, lam)
    }

    fn binder_types(&mut self, fam: &Family<'t>, xs: &[ExprPtr<'t>]) -> R<Vec<ExprPtr<'t>>> {
        let mut out = Vec::with_capacity(xs.len());
        for i in 0..xs.len() {
            let t = self.restore(fam, local_ty(xs[i]))?;
            out.push(self.ctx.abstract_locals(t, &xs[..i]));
        }
        Ok(out)
    }

    fn bind_after(
        &mut self,
        fam: &Family<'t>,
        pre: &[(ExprPtr<'t>, ExprPtr<'t>)],
        xs: &[ExprPtr<'t>],
        body: ExprPtr<'t>,
        lam: bool,
    ) -> R<ExprPtr<'t>> {
        let all: Vec<_> = pre.iter().map(|p| p.0).chain(xs.iter().copied()).collect();
        let body = self.restore(fam, body)?;
        let mut b = self.ctx.abstract_locals(body, &all);
        for i in (0..all.len()).rev() {
            let t = match pre.get(i) {
                Some(&(_, t)) => t,
                None => {
                    let t = self.restore(fam, local_ty(all[i]))?;
                    self.ctx.abstract_locals(t, &all[..i])
                }
            };
            b = if lam {
                self.ctx.lam(t, b)
            } else {
                self.ctx.pi(t, b)
            };
        }
        Ok(b)
    }

    fn positive(&mut self, f: &Family<'t>, ty: ExprPtr<'t>) -> R<()> {
        let ty = self.whnf(ty)?;
        if !f.occurs(ty) {
            return Ok(());
        }
        match *ty {
            Expr::Pi { ty: d, body, .. } => {
                ensure!(self, !f.occurs(d), "negative inductive occurrence");
                let x = self.fresh_local(d);
                let b = self.inst1(body, x)?;
                self.positive(f, b)
            }
            _ => {
                ensure!(
                    self,
                    f.application(ty).is_some(),
                    "invalid recursive inductive occurrence"
                );
                Ok(())
            }
        }
    }

    fn recursive_field(&mut self, f: &Family<'t>, x: ExprPtr<'t>) -> R<Option<RecField<'t>>> {
        let (locals, r) = self.telescope(local_ty(x))?;
        Ok(f.application(r).map(|(owner, indices)| RecField {
            field: x,
            locals,
            owner,
            indices,
        }))
    }

    pub(crate) fn native_block(&self, b: Block) -> bool {
        (b.start..b.types_end).all(|i| matches!(self.ctx.store.declars[i as usize], Declar::Ind(_)))
    }

    pub(crate) fn nested_block(&self, b: Block) -> bool {
        matches!(self.ctx.store.declars[b.start as usize], Declar::Ind(t) if t.num_nested > 0)
    }

    pub(crate) fn check_block(&mut self, b: Block) -> R<()> {
        let Members { types, ctors, recs } = self.block_members(b)?;
        let ups = types[0].info.uparams;
        ensure!(
            self,
            kernel::InductiveType::distinct_params(&ups[..]),
            "duplicate universe parameter"
        );
        self.uparams = ups;
        self.limit = b.start;
        let (mut fam, result_level, mut indices) = self.check_types(&types)?;
        self.limit = b.types_end;
        let zero = self.is_zero(result_level)?;
        let (shapes, nested) = self.check_ctors(&mut fam, &types, &ctors, result_level, zero)?;
        indices.extend(nested.into_iter().map(|n| n.indices));
        let spec = Spec {
            fam,
            types,
            indices,
            shapes,
        };
        let elim = self.elim(&spec, &recs, result_level, zero)?;
        self.uparams = elim.uparams;
        self.limit = b.ctors_end;
        let premises = self.premises(&spec, elim.level)?;
        self.check_recursors(b, &spec, &recs, &elim, &premises)
    }

    fn block_members(&mut self, b: Block) -> R<Members<'t>> {
        for i in b.start..b.end {
            ensure!(
                self,
                self.ctx.store.declars[i as usize].name().decl_idx() == Some(i),
                "duplicate inductive declaration name"
            );
        }
        let types = self.members(b.start..b.types_end, |d| match d {
            Declar::Ind(t) => Some(t),
            _ => None,
        })?;
        let ctors = self.members(b.types_end..b.ctors_end, |d| match d {
            Declar::Ctor(c) => Some(c),
            _ => None,
        })?;
        let recs = self.members(b.ctors_end..b.end, |d| match d {
            Declar::Rec(r) => Some(r),
            _ => None,
        })?;
        ensure!(self, !types.is_empty(), "empty inductive block");
        Ok(Members { types, ctors, recs })
    }

    fn check_types(
        &mut self,
        types: &[Inductive<'t>],
    ) -> R<(Family<'t>, LevelPtr<'t>, Vec<Vec<ExprPtr<'t>>>)> {
        let (ups, np) = (types[0].info.uparams, types[0].num_params);
        let mut fam = Family {
            names: types.iter().map(|t| t.info.name).collect(),
            aux: Vec::new(),
            apps: Vec::new(),
            num_indices: types.iter().map(|t| usize::from(t.num_indices)).collect(),
            levels: ups,
            params: Vec::new(),
        };
        let mut result_level = self.ctx.zero();
        let mut indices = Vec::new();
        let wf: Vec<_> = types.iter().map(|t| RecCheck::Sort(t.info.ty)).collect();
        let types_wf = self.vc_reject(&wf)?.is_none();
        for (i, t) in types.iter().enumerate() {
            ensure!(
                self,
                t.info.uparams == ups
                    && t.num_params == np
                    && t.num_nested == types[0].num_nested
                    && t.all == &fam.names[..],
                "inconsistent mutual inductive parameters"
            );
            if !types_wf {
                self.sort_of(t.info.ty)?;
            }
            let rest = if i == 0 {
                self.open_params(t.info.ty, np, &mut fam.params)?
            } else {
                self.consume_params(t.info.ty, &fam.params)?
            };
            let (is, r) = self.telescope(rest)?;
            ensure!(
                self,
                is.len() == usize::from(t.num_indices),
                "incorrect inductive index count"
            );
            let Expr::Sort { level, .. } = *r else {
                reject!(self, "inductive type does not end in a sort")
            };
            if i == 0 {
                result_level = level;
            } else {
                ensure!(
                    self,
                    self.level_eq(result_level, level)?,
                    "mutual inductive universe mismatch"
                );
            }
            indices.push(is);
        }
        if !types_wf {
            return Err(self.disagree());
        }
        Ok((fam, result_level, indices))
    }

    /// Constructors member by member in Lean's order: the block's types, then each auxiliary
    /// type as its nested occurrence was found, so motives and minors line up with the export.
    fn check_ctors(
        &mut self,
        fam: &mut Family<'t>,
        types: &[Inductive<'t>],
        ctors: &[Constructor<'t>],
        result_level: LevelPtr<'t>,
        zero: bool,
    ) -> R<(Vec<Shape<'t>>, Vec<Nested<'t>>)> {
        let (ups, np) = (fam.levels, types[0].num_params);
        let wf: Vec<_> = ctors.iter().map(|c| RecCheck::Sort(c.info.ty)).collect();
        let ctors_wf = self.vc_reject(&wf)?.is_none();
        let expand = types[0].num_nested > 0;
        let mut shapes = Vec::new();
        let mut cs = Ctors {
            result_level,
            zero,
            recursive: false,
            reflexive: false,
            nested: Vec::new(),
        };
        let mut owner = 0;
        while owner < types.len() + cs.nested.len() {
            if let Some(t) = types.get(owner) {
                for (index, &name) in t.ctors.iter().enumerate() {
                    let Some(&c) = ctors.iter().find(|c| c.info.name == name) else {
                        reject!(self, "missing constructor")
                    };
                    ensure!(
                        self,
                        c.induct == t.info.name
                            && usize::from(c.cidx) == index
                            && c.info.uparams == ups
                            && c.num_params == np,
                        "incorrect constructor metadata"
                    );
                    if !ctors_wf {
                        self.sort_of(c.info.ty)?;
                    }
                    let mut rest = self.consume_params(c.info.ty, &fam.params)?;
                    if expand {
                        rest = self.expand(fam, &mut cs, rest)?;
                    }
                    let k = self.ctx.konst(name, ups);
                    let head = self.ctx.apps(k, &fam.params);
                    let s = self.shape(fam, &mut cs, rest, name, head, owner)?;
                    ensure!(
                        self,
                        s.fields.len() == usize::from(c.num_fields),
                        "incorrect constructor field count"
                    );
                    shapes.push(s);
                }
            } else {
                let n = &cs.nested[owner - types.len()];
                let (ind, levels, ds) = (n.ind, n.levels, n.ds.clone());
                for &name in ind.ctors {
                    let Some(Declar::Ctor(c)) = self.declar(name) else {
                        reject!(self, "missing nested constructor")
                    };
                    let ty = self.ctx.declar_type(&Declar::Ctor(c), levels);
                    let rest = self.instantiate_params(ty, ind.num_params, &ds)?;
                    let rest = self.expand(fam, &mut cs, rest)?;
                    let k = self.ctx.konst(name, levels);
                    let head = self.ctx.apps(k, &ds);
                    let s = self.shape(fam, &mut cs, rest, name, head, owner)?;
                    ensure!(
                        self,
                        s.fields.len() == usize::from(c.num_fields),
                        "incorrect constructor field count"
                    );
                    shapes.push(s);
                }
            }
            owner += 1;
        }
        let originals = shapes.iter().filter(|s| s.owner < types.len()).count();
        ensure!(self, originals == ctors.len(), "extraneous constructor");
        ensure!(
            self,
            types[0].num_nested == cs.nested.len(),
            "incorrect nested inductive count"
        );
        for t in types {
            ensure!(
                self,
                t.is_rec == cs.recursive && t.is_reflexive == cs.reflexive,
                "incorrect inductive recursion metadata"
            );
        }
        if !ctors_wf {
            return Err(self.disagree());
        }
        Ok((shapes, cs.nested))
    }

    fn shape(
        &mut self,
        fam: &Family<'t>,
        cs: &mut Ctors<'t>,
        rest: ExprPtr<'t>,
        name: NamePtr<'t>,
        head: ExprPtr<'t>,
        owner: usize,
    ) -> R<Shape<'t>> {
        let (fields, ret) = self.telescope(rest)?;
        let mut levels = Vec::with_capacity(fields.len());
        for &x in &fields {
            let ty = local_ty(x);
            let l = self.level_of(ty)?;
            levels.push(l);
            ensure!(
                self,
                cs.zero || self.leq(l, cs.result_level)?,
                "constructor field universe exceeds inductive universe"
            );
            self.tick()?;
            self.positive(fam, ty)?;
            let has = fam.occurs(ty);
            cs.recursive |= has;
            cs.reflexive |= has && ty.is_pi();
        }
        let Some((i, indices)) = fam.application(ret) else {
            reject!(self, "invalid constructor return type")
        };
        ensure!(
            self,
            i == owner,
            "constructor returns the wrong inductive type"
        );
        Ok(Shape {
            name,
            head,
            fields,
            levels,
            indices,
            owner,
        })
    }

    /// Lean's `replace_all_nested`: outermost applications first, a replaced one not descended.
    fn expand(
        &mut self,
        fam: &mut Family<'t>,
        cs: &mut Ctors<'t>,
        e: ExprPtr<'t>,
    ) -> R<ExprPtr<'t>> {
        if !fam.occurs(e) {
            return Ok(e);
        }
        match *e {
            Expr::App { fun, arg, .. } => {
                if let Some(r) = self.nested_occurrence(fam, cs, e)? {
                    return Ok(r);
                }
                let f = self.expand(fam, cs, fun)?;
                let a = self.expand(fam, cs, arg)?;
                Ok(self.ctx.app(f, a))
            }
            Expr::Pi { ty, body, .. } => {
                let t = self.expand(fam, cs, ty)?;
                let b = self.expand(fam, cs, body)?;
                Ok(self.ctx.pi(t, b))
            }
            Expr::Lam { ty, body, .. } => {
                let t = self.expand(fam, cs, ty)?;
                let b = self.expand(fam, cs, body)?;
                Ok(self.ctx.lam(t, b))
            }
            Expr::Let { data, .. } => {
                let t = self.expand(fam, cs, data.ty)?;
                let v = self.expand(fam, cs, data.val)?;
                let b = self.expand(fam, cs, data.body)?;
                Ok(self.ctx.let_(t, v, b, data.nondep))
            }
            Expr::Proj {
                name, idx, e: s, ..
            } => {
                let s = self.expand(fam, cs, s)?;
                Ok(self.ctx.proj(name, idx, s))
            }
            _ => Ok(e),
        }
    }

    fn nested_occurrence(
        &mut self,
        fam: &mut Family<'t>,
        cs: &mut Ctors<'t>,
        e: ExprPtr<'t>,
    ) -> R<Option<ExprPtr<'t>>> {
        let (head, args) = spine(e);
        let Expr::Const { name, levels, .. } = *head else {
            return Ok(None);
        };
        if fam.names.contains(&name) {
            return Ok(None);
        }
        let Some(Declar::Ind(j)) = self.declar(name) else {
            return Ok(None);
        };
        let np = usize::from(j.num_params);
        if args.len() < np {
            return Ok(None);
        }
        let ds = &args[..np];
        if !ds.iter().any(|&a| fam.occurs(a)) {
            return Ok(None);
        }
        ensure!(
            self,
            ds.iter().all(|a| a.closed()),
            "nested inductive parameters contain constructor-local variables"
        );
        let key = self.ctx.apps(head, ds);
        let k = match fam.apps.iter().position(|&a| a.same(key)) {
            Some(k) => k,
            None => self.add_nested(fam, cs, j, levels, ds)?,
        };
        Ok(Some(self.ctx.apps(fam.aux[k], &args[np..])))
    }

    /// Every type of the nested family becomes a member, in its order, as Lean adds them.
    fn add_nested(
        &mut self,
        fam: &mut Family<'t>,
        cs: &mut Ctors<'t>,
        j: Inductive<'t>,
        levels: LevelsPtr<'t>,
        ds: &[ExprPtr<'t>],
    ) -> R<usize> {
        ensure!(
            self,
            levels.len() == j.info.uparams.len(),
            "nested inductive universe argument count mismatch"
        );
        let mut own = None;
        for &name in j.all {
            let Some(Declar::Ind(t)) = self.declar(name) else {
                reject!(self, "invalid nested mutual family")
            };
            ensure!(
                self,
                t.num_params == j.num_params && t.info.uparams == j.info.uparams,
                "invalid nested mutual family"
            );
            let ty = self.ctx.declar_type(&Declar::Ind(t), levels);
            let ty = self.instantiate_params(ty, t.num_params, ds)?;
            let (indices, r) = self.telescope(ty)?;
            ensure!(
                self,
                indices.len() == usize::from(t.num_indices),
                "incorrect nested inductive index count"
            );
            let Expr::Sort { level, .. } = *r else {
                reject!(self, "nested inductive type does not end in a sort")
            };
            ensure!(
                self,
                self.level_eq(cs.result_level, level)?,
                "nested inductive universe mismatch"
            );
            if name == j.info.name {
                own = Some(fam.aux.len());
            }
            let k = self.ctx.konst(name, levels);
            let app = self.ctx.apps(k, ds);
            fam.aux.push(self.fresh_local(ty));
            fam.apps.push(app);
            fam.num_indices.push(indices.len());
            cs.nested.push(Nested {
                ind: t,
                levels,
                ds: ds.to_vec(),
                indices,
            });
        }
        let Some(own) = own else {
            reject!(self, "invalid nested mutual family")
        };
        Ok(own)
    }
}
