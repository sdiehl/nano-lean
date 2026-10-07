use super::{Elim, Premises, Spec, Tc};
use crate::kernel;
use crate::term::decl::Recursor;
use crate::term::intern::Block;
use crate::term::level::Level;
use crate::term::ptr::LevelPtr;
use crate::value_checker::{RecCheck, check_recursor};
use crate::{ensure, reject};

impl<'t, 'a: 't> Tc<'t, 'a> {
    pub(super) fn elim(
        &mut self,
        spec: &Spec<'t>,
        recs: &[Recursor<'t>],
        result_level: LevelPtr<'t>,
        zero: bool,
    ) -> Elim<'t> {
        let (types, shapes, ups) = (&spec.types, &spec.shapes, spec.fam.levels);
        let zeros: Vec<_> = ups.iter().map(|_| self.ctx.zero()).collect();
        let zeros = self.ctx.levels(&zeros);
        let at_zero = self.ctx.subst_level(result_level, ups, zeros);
        let positive = !self.ctx.is_zero(at_zero);
        let large = kernel::Recursor::forced_elimination(positive, types.len(), shapes.len())
            .unwrap_or_else(|| {
                let s = &shapes[0];
                let mut ok = true;
                for (&x, &l) in s.fields.iter().zip(&s.levels) {
                    ok &= self.ctx.is_zero(l) || s.indices.contains(&x);
                }
                ok
            });
        let k = kernel::Recursor::k_like(zero, types.len(), shapes.iter().map(|s| s.fields.len()));
        ensure!(recs.len() == types.len(), "incorrect recursor count");
        let uparams = recs[0].info.uparams;
        let level = if large {
            ensure!(
                kernel::Recursor::large_params(&uparams[..], &ups[..])
                    && matches!(*uparams[0], Level::Param(..)),
                "incorrect recursor universe parameters"
            );
            uparams[0]
        } else {
            ensure!(uparams == ups, "invalid large elimination from proposition");
            self.ctx.zero()
        };
        Elim { level, uparams, k }
    }

    pub(super) fn premises(&mut self, spec: &Spec<'t>, elim: LevelPtr<'t>) -> Premises<'t> {
        let (fam, ups) = (&spec.fam, spec.fam.levels);
        let mut motives = Vec::new();
        let mut majors = Vec::new();
        for (t, indices) in spec.types.iter().zip(&spec.indices) {
            let c = self.ctx.konst(t.info.name, ups);
            let args: Vec<_> = fam.params.iter().chain(indices).copied().collect();
            let applied = self.ctx.apps(c, &args);
            let major = self.fresh_local(applied);
            let s = self.ctx.sort(elim);
            let xs: Vec<_> = indices.iter().copied().chain([major]).collect();
            let mty = self.bind(&xs, s, false);
            motives.push(self.fresh_local(mty));
            majors.push(major);
        }
        let mut minors = Vec::new();
        let mut recursive_fields = Vec::with_capacity(spec.shapes.len());
        for s in &spec.shapes {
            let c = self.ctx.konst(s.ctor.info.name, ups);
            let args: Vec<_> = fam.params.iter().chain(&s.fields).copied().collect();
            let ctor = self.ctx.apps(c, &args);
            let args: Vec<_> = s.indices.iter().copied().chain([ctor]).collect();
            let conclusion = self.ctx.apps(motives[s.owner], &args);
            let mut xs = s.fields.clone();
            let mut recs = Vec::new();
            for &x in &s.fields {
                if let Some(rf) = self.recursive_field(fam, x) {
                    let term = self.ctx.apps(x, &rf.locals);
                    let margs: Vec<_> = rf.indices.iter().copied().chain([term]).collect();
                    let body = self.ctx.apps(motives[rf.owner], &margs);
                    let ih = self.bind(&rf.locals, body, false);
                    xs.push(self.fresh_local(ih));
                    recs.push(rf);
                }
            }
            let ty = self.bind(&xs, conclusion, false);
            minors.push(self.fresh_local(ty));
            recursive_fields.push(recs);
        }
        Premises {
            motives,
            majors,
            minors,
            recursive_fields,
        }
    }

    pub(super) fn check_recursors(
        &mut self,
        b: Block,
        spec: &Spec<'t>,
        recs: &[Recursor<'t>],
        elim: &Elim<'t>,
        p: &Premises<'t>,
    ) {
        let (types, shapes, all) = (&spec.types, &spec.shapes, &spec.fam.names);
        let (np, rups) = (types[0].num_params, elim.uparams);
        let prefix: Vec<_> = spec
            .fam
            .params
            .iter()
            .chain(&p.motives)
            .chain(&p.minors)
            .copied()
            .collect();
        let prefix_tys = self.binder_types(&prefix);
        let pre: Vec<_> = prefix.iter().copied().zip(prefix_tys).collect();
        let rec_str = self.ctx.string(kernel::Recursor::SUFFIX);
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
                    && r.is_k == elim.k,
                "incorrect recursor metadata"
            );
            let tail: Vec<_> = spec.indices[owner]
                .iter()
                .copied()
                .chain([p.majors[owner]])
                .collect();
            let result = self.ctx.apps(p.motives[owner], &tail);
            let want = self.bind_after(&pre, &tail, result, false);
            self.recursor_checks(&[RecCheck::Type(r.info.ty, want)]);
            let mine: Vec<_> = shapes
                .iter()
                .enumerate()
                .filter(|(_, s)| s.owner == owner)
                .collect();
            ensure!(r.rules.len() == mine.len(), "incorrect recursor rule count");
            let saved = self.limit;
            self.limit = b.end;
            let mut checks = Vec::new();
            for (rule, (minor, s)) in r.rules.iter().zip(mine) {
                if rule.ctor != s.ctor.info.name || usize::from(rule.nfields) != s.fields.len() {
                    self.recursor_checks(&checks);
                    reject!("incorrect recursor rule metadata");
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
                    args.push(self.bind(&rf.locals, call, true));
                }
                let rhs = self.ctx.apps(p.minors[minor], &args);
                let want = self.bind_after(&pre, &s.fields, rhs, true);
                checks.push(RecCheck::Rule(rule.rhs, want));
            }
            self.recursor_checks(&checks);
            self.limit = saved;
        }
    }

    pub(super) fn vc_reject(&mut self, checks: &[RecCheck<'t>]) -> Option<usize> {
        if checks.is_empty() {
            return None;
        }
        let (limits, uparams, limit) = (self.limits, self.uparams, self.limit);
        check_recursor(
            &mut self.ctx,
            limits,
            &mut self.steps_left,
            uparams,
            limit,
            checks,
        )
        .err()
    }

    /// The term checker re-decides from the first rejected obligation to keep its reason.
    fn recursor_checks(&mut self, checks: &[RecCheck<'t>]) {
        let Some(i) = self.vc_reject(checks) else {
            return;
        };
        for &c in &checks[i..] {
            match c {
                RecCheck::Sort(ty) => {
                    self.sort_of(ty);
                }
                RecCheck::Type(ty, want) => {
                    self.sort_of(ty);
                    ensure!(self.def_eq(ty, want), "incorrect recursor type");
                }
                RecCheck::Rule(rhs, want) => {
                    let wt = self.infer(want, false);
                    let at = self.infer(rhs, false);
                    ensure!(self.def_eq(at, wt), "incorrect recursor computation rule");
                    ensure!(
                        self.def_eq(rhs, want),
                        "incorrect recursor computation rule"
                    );
                }
            }
        }
    }
}
