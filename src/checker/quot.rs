use super::Tc;
use super::env::Decls;
use crate::term::decl::{Declar, Info};
use crate::term::ptr::{ExprPtr, LevelPtr, NamePtr};
use crate::{ensure, reject};

impl<'t, 'a: 't> Tc<'t, 'a> {
    fn c(&mut self, n: Option<NamePtr<'t>>, ls: &[LevelPtr<'t>]) -> ExprPtr<'t> {
        let Some(n) = n else {
            reject!("quotient requires its builtin constants")
        };
        let ls = self.ctx.levels(ls);
        self.ctx.konst(n, ls)
    }

    fn v(&mut self, i: u16) -> ExprPtr<'t> {
        self.ctx.var(i)
    }

    fn pis(&mut self, doms: &[ExprPtr<'t>], mut body: ExprPtr<'t>) -> ExprPtr<'t> {
        for &d in doms.iter().rev() {
            body = self.ctx.pi(d, body);
        }
        body
    }

    fn rel(&mut self, i: u16) -> ExprPtr<'t> {
        let p = self.ctx.prop();
        let a = self.v(i);
        let b = self.v(i + 1);
        self.pis(&[a, b], p)
    }

    fn check_eq(&mut self) {
        let Some(eq) = self.names.eq else {
            reject!("quotient requires Eq")
        };
        let Some(Declar::Ind(i)) = self.declar(eq) else {
            reject!("quotient requires the Eq inductive")
        };
        ensure!(
            i.info.uparams.len() == 1 && i.ctors.len() == 1,
            "Eq has an unexpected shape"
        );
        let u = i.info.uparams.as_ref()[0];
        let s = self.ctx.sort(u);
        let (v0, v1, p) = (self.v(0), self.v(1), self.ctx.prop());
        let want = self.pis(&[s, v0, v1], p);
        ensure!(self.def_eq(want, i.info.ty), "Eq has an unexpected type");
        let Some(k) = self.ctor(i.ctors[0]) else {
            reject!("Eq has an unexpected shape")
        };
        let e = self.c(Some(eq), &[k.info.uparams.as_ref()[0]]);
        let (v0, v1) = (self.v(0), self.v(1));
        let b = self.ctx.apps(e, &[v1, v0, v0]);
        let s = self.ctx.sort(k.info.uparams.as_ref()[0]);
        let want = self.pis(&[s, v0], b);
        ensure!(
            self.def_eq(want, k.info.ty),
            "Eq.refl has an unexpected type"
        );
    }

    pub(crate) fn check_quot(&mut self, i: Info<'t>) {
        let prerequisites: &[Option<NamePtr<'t>>] = if Some(i.name) == self.names.quot {
            &[]
        } else if Some(i.name) == self.names.quot_mk {
            &[self.names.quot]
        } else {
            &[self.names.quot, self.names.quot_mk]
        };
        for &prerequisite in prerequisites {
            ensure!(
                prerequisite.is_some_and(|name| matches!(self.declar(name), Some(Declar::Quot(_)))),
                "missing quotient primitive"
            );
        }
        self.check_eq();
        let ps = i.uparams.as_ref();
        let n = Some(i.name);
        let nm = self.names;
        let want = if n == nm.quot && ps.len() == 1 {
            let s = self.ctx.sort(ps[0]);
            let r = self.rel(0);
            self.pis(&[s, r], s)
        } else if n == nm.quot_mk && ps.len() == 1 {
            let s = self.ctx.sort(ps[0]);
            let r = self.rel(0);
            let q = self.c(nm.quot, &[ps[0]]);
            let (v1, v2) = (self.v(1), self.v(2));
            let qt = self.ctx.apps(q, &[v2, v1]);
            self.pis(&[s, r, v1], qt)
        } else if n == nm.quot_lift && ps.len() == 2 {
            let su = self.ctx.sort(ps[0]);
            let sv = self.ctx.sort(ps[1]);
            let r = self.rel(0);
            let (v0, v1, v2, v3, v4) = (self.v(0), self.v(1), self.v(2), self.v(3), self.v(4));
            let f = self.ctx.pi(v2, v1);
            let rab = self.ctx.apps(v4, &[v1, v0]);
            let eq = self.c(nm.eq, &[ps[1]]);
            let fa = self.ctx.app(v3, v2);
            let fb = self.ctx.app(v3, v1);
            let eqt = self.ctx.apps(eq, &[v4, fa, fb]);
            let h = self.pis(&[v3, v4, rab], eqt);
            let q = self.c(nm.quot, &[ps[0]]);
            let qt = self.ctx.apps(q, &[v4, v3]);
            self.pis(&[su, r, sv, f, h, qt], v3)
        } else if n == nm.quot_ind && ps.len() == 1 {
            let s = self.ctx.sort(ps[0]);
            let r = self.rel(0);
            let p = self.ctx.prop();
            let (v0, v1, v2, v3) = (self.v(0), self.v(1), self.v(2), self.v(3));
            let q = self.c(nm.quot, &[ps[0]]);
            let q10 = self.ctx.apps(q, &[v1, v0]);
            let beta = self.ctx.pi(q10, p);
            let mk = self.c(nm.quot_mk, &[ps[0]]);
            let mka = self.ctx.apps(mk, &[v3, v2, v0]);
            let bm = self.ctx.app(v1, mka);
            let mkt = self.ctx.pi(v2, bm);
            let q32 = self.ctx.apps(q, &[v3, v2]);
            let bq = self.ctx.app(v2, v0);
            self.pis(&[s, r, beta, mkt, q32], bq)
        } else {
            reject!("unexpected quotient declaration {}", i.name.as_ref())
        };
        ensure!(
            self.def_eq(want, i.ty),
            "quotient declaration {} has an unexpected type",
            i.name.as_ref()
        );
    }
}
