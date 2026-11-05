use super::{Elim, Premises, Spec, Tc, local_ty};
use crate::kernel;
use crate::term::decl::Recursor;
use crate::term::intern::Block;
use crate::term::level::Level;
use crate::term::outcome::{Failure, R, Stop};
use crate::term::ptr::LevelPtr;
use crate::value_checker::RecCheck;
use crate::{ensure, reject};

impl<'t, 'a: 't> Tc<'t, 'a> {
    pub(super) fn elim(
        &mut self,
        spec: &Spec<'t>,
        recs: &[Recursor<'t>],
        result_level: LevelPtr<'t>,
        zero: bool,
    ) -> R<Elim<'t>> {
        let (members, shapes, ups) = (spec.indices.len(), &spec.shapes, spec.fam.levels);
        let zeros: Vec<_> = ups.iter().map(|_| self.ctx.zero()).collect();
        let zeros = self.ctx.levels(&zeros);
        let at_zero = self.ctx.subst_level(result_level, ups, zeros);
        let positive = !self.is_zero(at_zero)?;
        let large = match kernel::Recursor::forced_elimination(positive, members, shapes.len()) {
            Some(large) => large,
            None => {
                let s = &shapes[0];
                let mut ok = true;
                for &x in &s.fields {
                    let l = self.level_of(local_ty(x))?;
                    ok &= self.is_zero(l)? || s.indices.contains(&x);
                }
                ok
            }
        };
        let k = kernel::Recursor::k_like(zero, members, shapes.iter().map(|s| s.fields.len()));
        ensure!(self, recs.len() == members, "incorrect recursor count");
        let uparams = recs[0].info.uparams;
        let level = if large {
            ensure!(
                self,
                kernel::Recursor::large_params(&uparams[..], &ups[..])
                    && matches!(*uparams[0], Level::Param(..)),
                "incorrect recursor universe parameters"
            );
            uparams[0]
        } else {
            ensure!(
                self,
                uparams == ups,
                "invalid large elimination from proposition"
            );
            self.ctx.zero()
        };
        Ok(Elim { level, uparams, k })
    }

    pub(super) fn premises(&mut self, spec: &Spec<'t>, elim: LevelPtr<'t>) -> R<Premises<'t>> {
        let (fam, ups) = (&spec.fam, spec.fam.levels);
        let mut motives = Vec::new();
        let mut majors = Vec::new();
        for (m, indices) in spec.indices.iter().enumerate() {
            let head = match spec.types.get(m) {
                Some(t) => {
                    let c = self.ctx.konst(t.info.name, ups);
                    self.ctx.apps(c, &fam.params)
                }
                None => fam.apps[m - spec.types.len()],
            };
            let applied = self.ctx.apps(head, indices);
            let major = self.fresh_local(applied);
            let s = self.ctx.sort(elim);
            let xs: Vec<_> = indices.iter().copied().chain([major]).collect();
            let mty = self.bind(fam, &xs, s, false)?;
            motives.push(self.fresh_local(mty));
            majors.push(major);
        }
        let mut minors = Vec::new();
        let mut recursive_fields = Vec::with_capacity(spec.shapes.len());
        for s in &spec.shapes {
            let ctor = self.ctx.apps(s.head, &s.fields);
            let args: Vec<_> = s.indices.iter().copied().chain([ctor]).collect();
            let conclusion = self.ctx.apps(motives[s.owner], &args);
            let mut xs = s.fields.clone();
            let mut recs = Vec::new();
            for &x in &s.fields {
                if let Some(rf) = self.recursive_field(fam, x)? {
                    let term = self.ctx.apps(x, &rf.locals);
                    let margs: Vec<_> = rf.indices.iter().copied().chain([term]).collect();
                    let body = self.ctx.apps(motives[rf.owner], &margs);
                    let ih = self.bind(fam, &rf.locals, body, false)?;
                    xs.push(self.fresh_local(ih));
                    recs.push(rf);
                }
            }
            let ty = self.bind(fam, &xs, conclusion, false)?;
            minors.push(self.fresh_local(ty));
            recursive_fields.push(recs);
        }
        Ok(Premises {
            motives,
            majors,
            minors,
            recursive_fields,
        })
    }

    pub(super) fn check_recursors(
        &mut self,
        b: Block,
        spec: &Spec<'t>,
        recs: &[Recursor<'t>],
        elim: &Elim<'t>,
        p: &Premises<'t>,
    ) -> R<()> {
        let (fam, types, shapes, all) = (&spec.fam, &spec.types, &spec.shapes, &spec.fam.names);
        let (np, rups) = (types[0].num_params, elim.uparams);
        let prefix: Vec<_> = spec
            .fam
            .params
            .iter()
            .chain(&p.motives)
            .chain(&p.minors)
            .copied()
            .collect();
        let prefix_tys = self.binder_types(fam, &prefix)?;
        let pre: Vec<_> = prefix.iter().copied().zip(prefix_tys).collect();
        let rec_str = self.ctx.string(kernel::Recursor::SUFFIX);
        let mut rec_names: Vec<_> = all.iter().map(|&n| self.ctx.str_name(n, rec_str)).collect();
        for k in 1..=spec.indices.len() - types.len() {
            let s = self
                .ctx
                .string(&format!("{}_{k}", kernel::Recursor::SUFFIX));
            rec_names.push(self.ctx.str_name(all[0], s));
        }
        for (owner, indices) in spec.indices.iter().enumerate() {
            let Some(&r) = recs.iter().find(|r| r.info.name == rec_names[owner]) else {
                reject!(self, "missing recursor")
            };
            ensure!(
                self,
                r.all == &all[..]
                    && r.info.uparams == rups
                    && r.num_params == np
                    && usize::from(r.num_indices) == indices.len()
                    && usize::from(r.num_motives) == spec.indices.len()
                    && usize::from(r.num_minors) == shapes.len()
                    && r.is_k == elim.k,
                "incorrect recursor metadata"
            );
            let tail: Vec<_> = indices.iter().copied().chain([p.majors[owner]]).collect();
            let result = self.ctx.apps(p.motives[owner], &tail);
            let want = self.bind_after(fam, &pre, &tail, result, false)?;
            self.recursor_checks(&[RecCheck::Type(r.info.ty, want)])?;
            let mine: Vec<_> = shapes
                .iter()
                .enumerate()
                .filter(|(_, s)| s.owner == owner)
                .collect();
            ensure!(
                self,
                r.rules.len() == mine.len(),
                "incorrect recursor rule count"
            );
            let saved = self.limit;
            self.limit = b.end;
            let mut checks = Vec::new();
            for (rule, (minor, s)) in r.rules.iter().zip(mine) {
                if rule.ctor != s.name || usize::from(rule.nfields) != s.fields.len() {
                    self.recursor_checks(&checks)?;
                    reject!(self, "incorrect recursor rule metadata");
                }
                let mut args = s.fields.clone();
                for rf in &p.recursive_fields[minor] {
                    let rc = self.ctx.konst(rec_names[rf.owner], rups);
                    let term = self.ctx.apps(rf.field, &rf.locals);
                    let a: Vec<_> = prefix
                        .iter()
                        .chain(&rf.indices)
                        .copied()
                        .chain([term])
                        .collect();
                    let call = self.ctx.apps(rc, &a);
                    args.push(self.bind(fam, &rf.locals, call, true)?);
                }
                let rhs = self.ctx.apps(p.minors[minor], &args);
                let want = self.bind_after(fam, &pre, &s.fields, rhs, true)?;
                checks.push(RecCheck::Rule(rule.rhs, want));
            }
            self.recursor_checks(&checks)?;
            self.limit = saved;
        }
        Ok(())
    }

    pub(super) fn vc_reject(&mut self, checks: &[RecCheck<'t>]) -> R<Option<usize>> {
        if checks.is_empty() {
            return Ok(None);
        }
        let (limits, uparams, limit) = (self.limits, self.uparams, self.limit);
        let Self {
            rec,
            ctx,
            steps_left,
            ..
        } = self;
        let r = rec.check(ctx, limits, steps_left, uparams, limit, checks);
        r.map_err(|f| self.failed(f))
    }

    /// Acceptance needs both cores, so a value-core rejection the term core overturns is internal.
    #[cold]
    pub(super) fn disagree(&mut self) -> Stop {
        self.failed(Failure::Internal(
            "the cores disagree on an inductive".into(),
        ))
    }

    /// The term checker re-decides from the first rejected obligation to keep its reason.
    fn recursor_checks(&mut self, checks: &[RecCheck<'t>]) -> R<()> {
        let Some(i) = self.vc_reject(checks)? else {
            return Ok(());
        };
        for &c in &checks[i..] {
            match c {
                RecCheck::Sort(ty) | RecCheck::Ctor(ty, ..) => {
                    self.sort_of(ty)?;
                }
                RecCheck::Type(ty, want) if !ty.same(want) => {
                    self.sort_of(ty)?;
                    ensure!(self, self.def_eq(ty, want)?, "incorrect recursor type");
                }
                RecCheck::Rule(rhs, want) if !rhs.same(want) => {
                    let wt = self.infer(want, false)?;
                    let at = self.infer(rhs, false)?;
                    ensure!(
                        self,
                        self.def_eq(at, wt)?,
                        "incorrect recursor computation rule"
                    );
                    ensure!(
                        self,
                        self.def_eq(rhs, want)?,
                        "incorrect recursor computation rule"
                    );
                }
                RecCheck::Type(..) | RecCheck::Rule(..) => {}
            }
        }
        Err(self.disagree())
    }
}
