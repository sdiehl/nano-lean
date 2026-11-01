use super::Tc;
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

struct Family<'t> {
    names: Vec<NamePtr<'t>>,
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
        let Expr::Const { name, levels, .. } = *head else {
            return None;
        };
        let i = self.names.iter().position(|&n| n == name)?;
        let np = self.params.len();
        if levels != self.levels
            || args.len() != np + self.num_indices[i]
            || args[..np] != self.params[..]
        {
            return None;
        }
        let indices = args[np..].to_vec();
        (!indices.iter().any(|&e| self.occurs(e))).then_some((i, indices))
    }
}

struct Shape<'t> {
    ctor: Constructor<'t>,
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

    fn bind(&mut self, xs: &[ExprPtr<'t>], body: ExprPtr<'t>, lam: bool) -> ExprPtr<'t> {
        self.bind_after(&[], xs, body, lam)
    }

    fn binder_types(&mut self, xs: &[ExprPtr<'t>]) -> Vec<ExprPtr<'t>> {
        (0..xs.len())
            .map(|i| self.ctx.abstract_locals(local_ty(xs[i]), &xs[..i]))
            .collect()
    }

    fn bind_after(
        &mut self,
        pre: &[(ExprPtr<'t>, ExprPtr<'t>)],
        xs: &[ExprPtr<'t>],
        body: ExprPtr<'t>,
        lam: bool,
    ) -> ExprPtr<'t> {
        let all: Vec<_> = pre.iter().map(|p| p.0).chain(xs.iter().copied()).collect();
        let mut b = self.ctx.abstract_locals(body, &all);
        for i in (0..all.len()).rev() {
            let t = match pre.get(i) {
                Some(&(_, t)) => t,
                None => self.ctx.abstract_locals(local_ty(all[i]), &all[..i]),
            };
            b = if lam {
                self.ctx.lam(t, b)
            } else {
                self.ctx.pi(t, b)
            };
        }
        b
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
        (b.start..b.types_end).all(
            |i| matches!(self.ctx.store.declars[i as usize], Declar::Ind(t) if t.num_nested == 0),
        )
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
        let (fam, result_level, indices) = self.check_types(&types)?;
        self.limit = b.types_end;
        let zero = self.is_zero(result_level)?;
        let shapes = self.check_ctors(&fam, &types, &ctors, result_level, zero)?;
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
                t.info.uparams == ups && t.num_params == np && t.all == &fam.names[..],
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

    fn check_ctors(
        &mut self,
        fam: &Family<'t>,
        types: &[Inductive<'t>],
        ctors: &[Constructor<'t>],
        result_level: LevelPtr<'t>,
        zero: bool,
    ) -> R<Vec<Shape<'t>>> {
        let (ups, np) = (fam.levels, types[0].num_params);
        let wf: Vec<_> = ctors.iter().map(|c| RecCheck::Sort(c.info.ty)).collect();
        let ctors_wf = self.vc_reject(&wf)?.is_none();
        let mut shapes = Vec::new();
        let (mut recursive, mut reflexive) = (false, false);
        for (owner, t) in types.iter().enumerate() {
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
                let rest = self.consume_params(c.info.ty, &fam.params)?;
                let (fields, ret) = self.telescope(rest)?;
                ensure!(
                    self,
                    fields.len() == usize::from(c.num_fields),
                    "incorrect constructor field count"
                );
                let mut levels = Vec::with_capacity(fields.len());
                for &x in &fields {
                    let ty = local_ty(x);
                    let l = self.level_of(ty)?;
                    levels.push(l);
                    ensure!(
                        self,
                        zero || self.leq(l, result_level)?,
                        "constructor field universe exceeds inductive universe"
                    );
                    self.tick()?;
                    self.positive(fam, ty)?;
                    let has = fam.occurs(ty);
                    recursive |= has;
                    reflexive |= has && ty.is_pi();
                }
                let Some((i, args)) = fam.application(ret) else {
                    reject!(self, "invalid constructor return type")
                };
                ensure!(
                    self,
                    i == owner,
                    "constructor returns the wrong inductive type"
                );
                shapes.push(Shape {
                    ctor: c,
                    fields,
                    levels,
                    indices: args,
                    owner,
                });
            }
        }
        ensure!(self, shapes.len() == ctors.len(), "extraneous constructor");
        for t in types {
            ensure!(
                self,
                t.is_rec == recursive && t.is_reflexive == reflexive,
                "incorrect inductive recursion metadata"
            );
        }
        if !ctors_wf {
            return Err(self.disagree());
        }
        Ok(shapes)
    }
}
