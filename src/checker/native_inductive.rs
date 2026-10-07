//! Native validation of non-nested inductive blocks, following the existing
//! kernel's reconstruction: generate the expected recursors and compare.

use super::Tc;
use crate::term::FxHashSet;
use crate::term::decl::{Constructor, Declar, Inductive, Recursor};
use crate::term::expr::Expr;
use crate::term::intern::Block;
use crate::term::level::Level;
use crate::term::ptr::{ExprPtr, LevelPtr, LevelsPtr, NamePtr};
use crate::{ensure, reject};

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
                Expr::Local { ty, .. } => go(f, ty, seen),
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
    indices: Vec<ExprPtr<'t>>,
    owner: usize,
}

impl<'t, 'a: 't> Tc<'t, 'a> {
    fn sort_of(&mut self, e: ExprPtr<'t>) -> LevelPtr<'t> {
        let s = self.infer(e, false);
        self.ensure_sort(s)
    }

    fn telescope(&mut self, e: ExprPtr<'t>) -> (Vec<ExprPtr<'t>>, ExprPtr<'t>) {
        let mut e = self.whnf(e);
        let mut xs = Vec::new();
        while let Expr::Pi { ty, body, .. } = *e {
            let x = self.fresh_local(ty);
            let b = self.ctx.inst(body, &[x]);
            e = self.whnf(b);
            xs.push(x);
        }
        (xs, e)
    }

    fn consume_params(&mut self, mut ty: ExprPtr<'t>, params: &[ExprPtr<'t>]) -> ExprPtr<'t> {
        for &x in params {
            let w = self.whnf(ty);
            let Expr::Pi { ty: d, body, .. } = *w else {
                reject!("missing inductive parameter")
            };
            ensure!(
                self.def_eq(d, local_ty(x)),
                "inductive parameter type mismatch"
            );
            ty = self.ctx.inst(body, &[x]);
        }
        ty
    }

    /// Bind `xs` around `body`, the last becoming the innermost binder.
    fn bind(&mut self, xs: &[ExprPtr<'t>], body: ExprPtr<'t>, lam: bool) -> ExprPtr<'t> {
        let mut b = self.ctx.abstract_locals(body, xs);
        for i in (0..xs.len()).rev() {
            let t = self.ctx.abstract_locals(local_ty(xs[i]), &xs[..i]);
            b = if lam {
                self.ctx.lam(t, b)
            } else {
                self.ctx.pi(t, b)
            };
        }
        b
    }

    fn positive(&mut self, f: &Family<'t>, ty: ExprPtr<'t>) {
        let ty = self.whnf(ty);
        if !f.occurs(ty) {
            return;
        }
        match *ty {
            Expr::Pi { ty: d, body, .. } => {
                ensure!(!f.occurs(d), "negative inductive occurrence");
                let x = self.fresh_local(d);
                let b = self.ctx.inst(body, &[x]);
                self.positive(f, b)
            }
            _ => ensure!(
                f.application(ty).is_some(),
                "invalid recursive inductive occurrence"
            ),
        }
    }

    fn recursive_field(
        &mut self,
        f: &Family<'t>,
        ty: ExprPtr<'t>,
    ) -> Option<(Vec<ExprPtr<'t>>, usize, Vec<ExprPtr<'t>>)> {
        let (xs, r) = self.telescope(ty);
        f.application(r).map(|(i, args)| (xs, i, args))
    }

    /// Whether every member of the block can be validated natively.
    pub(crate) fn native_block(&self, b: Block) -> bool {
        (b.start..b.types_end).all(
            |i| matches!(self.ctx.store.declars[i as usize], Declar::Ind(t) if t.num_nested == 0),
        )
    }

    pub(crate) fn check_block(&mut self, b: Block) {
        let store = self.ctx.store;
        let members = |r: std::ops::Range<u32>| r.map(|i| (i, store.declars[i as usize]));
        for (i, d) in members(b.start..b.end) {
            ensure!(
                d.name().decl_idx() == Some(i),
                "duplicate inductive declaration name"
            );
        }
        let types: Vec<Inductive<'t>> = members(b.start..b.types_end)
            .map(|(_, d)| match d {
                Declar::Ind(t) => t,
                _ => reject!("malformed inductive block"),
            })
            .collect();
        let ctors: Vec<Constructor<'t>> = members(b.types_end..b.ctors_end)
            .map(|(_, d)| match d {
                Declar::Ctor(c) => c,
                _ => reject!("malformed inductive block"),
            })
            .collect();
        let recs: Vec<Recursor<'t>> = members(b.ctors_end..b.end)
            .map(|(_, d)| match d {
                Declar::Rec(r) => r,
                _ => reject!("malformed inductive block"),
            })
            .collect();
        ensure!(!types.is_empty(), "empty inductive block");
        let first = types[0];
        let ups = first.info.uparams;
        ensure!(
            ups.iter().collect::<FxHashSet<_>>().len() == ups.len(),
            "duplicate universe parameter"
        );
        let all: Vec<_> = types.iter().map(|t| t.info.name).collect();
        let np = first.num_params;
        self.uparams = ups;
        self.limit = b.start;
        let mut fam = Family {
            names: all.clone(),
            num_indices: types.iter().map(|t| usize::from(t.num_indices)).collect(),
            levels: ups,
            params: Vec::new(),
        };
        let mut result_level = self.ctx.zero();
        let mut indices = Vec::new();
        for (i, t) in types.iter().enumerate() {
            ensure!(
                t.info.uparams == ups && t.num_params == np && t.all == &all[..],
                "inconsistent mutual inductive parameters"
            );
            self.sort_of(t.info.ty);
            let rest = if i == 0 {
                let mut rest = t.info.ty;
                for _ in 0..np {
                    let w = self.whnf(rest);
                    let Expr::Pi { ty, body, .. } = *w else {
                        reject!("missing inductive parameter")
                    };
                    let x = self.fresh_local(ty);
                    rest = self.ctx.inst(body, &[x]);
                    fam.params.push(x);
                }
                rest
            } else {
                self.consume_params(t.info.ty, &fam.params)
            };
            let (is, r) = self.telescope(rest);
            ensure!(
                is.len() == usize::from(t.num_indices),
                "incorrect inductive index count"
            );
            let Expr::Sort { level, .. } = *r else {
                reject!("inductive type does not end in a sort")
            };
            if i == 0 {
                result_level = level;
            } else {
                ensure!(
                    self.ctx.level_eq(result_level, level),
                    "mutual inductive universe mismatch"
                );
            }
            indices.push(is);
        }
        self.limit = b.types_end;
        let zero = self.ctx.is_zero(result_level);
        let mut shapes = Vec::new();
        let (mut recursive, mut reflexive) = (false, false);
        for (owner, t) in types.iter().enumerate() {
            for (index, &name) in t.ctors.iter().enumerate() {
                let Some(&c) = ctors.iter().find(|c| c.info.name == name) else {
                    reject!("missing constructor")
                };
                ensure!(
                    c.induct == t.info.name
                        && usize::from(c.cidx) == index
                        && c.info.uparams == ups
                        && c.num_params == np,
                    "incorrect constructor metadata"
                );
                self.sort_of(c.info.ty);
                let rest = self.consume_params(c.info.ty, &fam.params);
                let (fields, ret) = self.telescope(rest);
                ensure!(
                    fields.len() == usize::from(c.num_fields),
                    "incorrect constructor field count"
                );
                for &x in &fields {
                    let ty = local_ty(x);
                    let l = self.sort_of(ty);
                    ensure!(
                        zero || self.ctx.leq(l, result_level),
                        "constructor field universe exceeds inductive universe"
                    );
                    self.tick();
                    self.positive(&fam, ty);
                    let has = fam.occurs(ty);
                    recursive |= has;
                    reflexive |= has && ty.is_pi();
                }
                let Some((i, args)) = fam.application(ret) else {
                    reject!("invalid constructor return type")
                };
                ensure!(i == owner, "constructor returns the wrong inductive type");
                shapes.push(Shape {
                    ctor: c,
                    fields,
                    indices: args,
                    owner,
                });
            }
        }
        ensure!(shapes.len() == ctors.len(), "extraneous constructor");
        for t in &types {
            ensure!(
                t.is_rec == recursive && t.is_reflexive == reflexive,
                "incorrect inductive recursion metadata"
            );
        }
        let zeros: Vec<_> = ups.iter().map(|_| self.ctx.zero()).collect();
        let zeros = self.ctx.levels(&zeros);
        let at_zero = self.ctx.subst_level(result_level, ups, zeros);
        let large = if !self.ctx.is_zero(at_zero) {
            true
        } else if types.len() > 1 || shapes.len() > 1 {
            false
        } else if let Some(s) = shapes.first() {
            let mut ok = true;
            for &x in &s.fields {
                let l = self.sort_of(local_ty(x));
                ok &= self.ctx.is_zero(l) || s.indices.contains(&x);
            }
            ok
        } else {
            true
        };
        let k = zero && types.len() == 1 && shapes.len() == 1 && shapes[0].fields.is_empty();
        ensure!(recs.len() == types.len(), "incorrect recursor count");
        let rups = recs[0].info.uparams;
        let elim = if large {
            ensure!(
                rups.len() == ups.len() + 1
                    && rups[1..] == ups[..]
                    && matches!(*rups[0], Level::Param(..))
                    && !ups.contains(&rups[0]),
                "incorrect recursor universe parameters"
            );
            rups[0]
        } else {
            ensure!(rups == ups, "invalid large elimination from proposition");
            self.ctx.zero()
        };
        self.uparams = rups;
        self.limit = b.ctors_end;
        let mut motives = Vec::new();
        let mut majors = Vec::new();
        for (i, t) in types.iter().enumerate() {
            let c = self.ctx.konst(t.info.name, ups);
            let args: Vec<_> = fam.params.iter().chain(&indices[i]).copied().collect();
            let applied = self.ctx.apps(c, &args);
            let major = self.fresh_local(applied);
            let s = self.ctx.sort(elim);
            let xs: Vec<_> = indices[i].iter().copied().chain([major]).collect();
            let mty = self.bind(&xs, s, false);
            motives.push(self.fresh_local(mty));
            majors.push(major);
        }
        let mut minors = Vec::new();
        for s in &shapes {
            let c = self.ctx.konst(s.ctor.info.name, ups);
            let args: Vec<_> = fam.params.iter().chain(&s.fields).copied().collect();
            let ctor = self.ctx.apps(c, &args);
            let args: Vec<_> = s.indices.iter().copied().chain([ctor]).collect();
            let conclusion = self.ctx.apps(motives[s.owner], &args);
            let mut xs = s.fields.clone();
            for &x in &s.fields {
                if let Some((ys, owner, args)) = self.recursive_field(&fam, local_ty(x)) {
                    let term = self.ctx.apps(x, &ys);
                    let args: Vec<_> = args.into_iter().chain([term]).collect();
                    let body = self.ctx.apps(motives[owner], &args);
                    let ih = self.bind(&ys, body, false);
                    xs.push(self.fresh_local(ih));
                }
            }
            let ty = self.bind(&xs, conclusion, false);
            minors.push(self.fresh_local(ty));
        }
        let prefix: Vec<_> = fam
            .params
            .iter()
            .chain(&motives)
            .chain(&minors)
            .copied()
            .collect();
        let rec_str = self.ctx.string("rec");
        let rec_names: Vec<_> = all.iter().map(|&n| self.ctx.str_name(n, rec_str)).collect();
        for (owner, t) in types.iter().enumerate() {
            let Some(&r) = recs.iter().find(|r| r.info.name == rec_names[owner]) else {
                reject!("missing recursor")
            };
            ensure!(
                r.all == &all[..]
                    && r.info.uparams == rups
                    && r.num_params == np
                    && r.num_indices == t.num_indices
                    && usize::from(r.num_motives) == types.len()
                    && usize::from(r.num_minors) == shapes.len()
                    && r.is_k == k,
                "incorrect recursor metadata"
            );
            let tail: Vec<_> = indices[owner]
                .iter()
                .copied()
                .chain([majors[owner]])
                .collect();
            let result = self.ctx.apps(motives[owner], &tail);
            let xs: Vec<_> = prefix.iter().copied().chain(tail).collect();
            let want = self.bind(&xs, result, false);
            self.sort_of(r.info.ty);
            ensure!(self.def_eq(r.info.ty, want), "incorrect recursor type");
            let mine: Vec<_> = shapes
                .iter()
                .enumerate()
                .filter(|(_, s)| s.owner == owner)
                .collect();
            ensure!(r.rules.len() == mine.len(), "incorrect recursor rule count");
            let saved = self.limit;
            self.limit = b.end;
            for (rule, (minor, s)) in r.rules.iter().zip(mine) {
                ensure!(
                    rule.ctor == s.ctor.info.name && usize::from(rule.nfields) == s.fields.len(),
                    "incorrect recursor rule metadata"
                );
                let mut args = s.fields.clone();
                for &x in &s.fields {
                    if let Some((ys, target, idx)) = self.recursive_field(&fam, local_ty(x)) {
                        let rc = self.ctx.konst(rec_names[target], rups);
                        let term = self.ctx.apps(x, &ys);
                        let a: Vec<_> = prefix.iter().copied().chain(idx).chain([term]).collect();
                        let call = self.ctx.apps(rc, &a);
                        args.push(self.bind(&ys, call, true));
                    }
                }
                let rhs = self.ctx.apps(minors[minor], &args);
                let xs: Vec<_> = prefix.iter().chain(&s.fields).copied().collect();
                let want = self.bind(&xs, rhs, true);
                let wt = self.infer(want, false);
                let at = self.infer(rule.rhs, false);
                ensure!(self.def_eq(at, wt), "incorrect recursor computation rule");
                ensure!(
                    self.def_eq(rule.rhs, want),
                    "incorrect recursor computation rule"
                );
            }
            self.limit = saved;
        }
    }
}
