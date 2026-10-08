use super::prelude::*;
use super::primitive::symbol;
use crate::term::names::{
    EQ, EQ_REFL, QUOT, QUOT_FN, QUOT_IND, QUOT_IND_MAJOR, QUOT_LIFT, QUOT_LIFT_MAJOR, QUOT_MK,
};
use crate::{Expr, Level};
use unbound::Name;

#[derive(Clone, Copy)]
enum Kind {
    Type,
    Ctor,
    Lift,
    Ind,
}

impl Kind {
    fn label(self) -> &'static str {
        match self {
            Self::Type => "type",
            Self::Ctor => "ctor",
            Self::Lift => "lift",
            Self::Ind => "ind",
        }
    }
}

struct Primitive {
    name: &'static str,
    kind: Kind,
    params: &'static [&'static str],
    prerequisites: &'static [&'static str],
}

const PRIMITIVES: [Primitive; 4] = [
    Primitive {
        name: QUOT,
        kind: Kind::Type,
        params: &["u"],
        prerequisites: &[],
    },
    Primitive {
        name: QUOT_MK,
        kind: Kind::Ctor,
        params: &["u"],
        prerequisites: &[QUOT],
    },
    Primitive {
        name: QUOT_LIFT,
        kind: Kind::Lift,
        params: &["u", "v"],
        prerequisites: &[QUOT, QUOT_MK],
    },
    Primitive {
        name: QUOT_IND,
        kind: Kind::Ind,
        params: &["u"],
        prerequisites: &[QUOT, QUOT_MK],
    },
];

pub(super) struct Eliminator {
    pub(super) major: usize,
    pub(super) function: usize,
}

fn arrow(domain: Expr, result: Expr) -> Expr {
    Expr::pi(Name::new("_"), domain, result)
}
fn telescope(locals: &[(Name<Expr>, Expr)], result: Expr) -> Expr {
    locals.iter().rev().fold(result, |body, (n, ty)| {
        Expr::pi(n.clone(), ty.clone(), body)
    })
}

fn signature(kind: Kind, params: &[String], encoded: bool) -> Expr {
    let c = |s: &str, levels| Expr::Const(symbol(s, encoded), levels);
    let u = Level::Param(params[0].clone());
    let v = params
        .get(1)
        .map(|p| Level::Param(p.clone()))
        .unwrap_or(Level::Nat(0));
    let a_ty = Name::new("A");
    let av = Expr::Var(a_ty.clone());
    let rel = Name::new("r");
    let rv = Expr::Var(rel.clone());
    let relation = arrow(av.clone(), arrow(av.clone(), Expr::Sort(Level::Nat(0))));
    let mut locals = vec![(a_ty, Expr::Sort(u.clone())), (rel, relation)];
    let quot = c(QUOT, vec![u.clone()]).app(av.clone()).app(rv.clone());
    let a = Name::new("a");
    let a_expr = Expr::Var(a.clone());
    let result = match kind {
        Kind::Type => Expr::Sort(u.clone()),
        Kind::Ctor => arrow(av.clone(), quot.clone()),
        Kind::Lift => {
            let b_ty = Name::new("B");
            let bv = Expr::Var(b_ty.clone());
            let f = Name::new("f");
            let fv = Expr::Var(f.clone());
            locals.push((b_ty, Expr::Sort(v.clone())));
            locals.push((f, arrow(av.clone(), bv.clone())));
            let b = Name::new("b");
            let b_expr = Expr::Var(b.clone());
            let eq = c(EQ, vec![v])
                .app(bv.clone())
                .app(fv.clone().app(a_expr.clone()))
                .app(fv.app(b_expr.clone()));
            let respects = telescope(
                &[(a, av.clone()), (b, av.clone())],
                arrow(rv.app(a_expr).app(b_expr), eq),
            );
            arrow(respects, arrow(quot, bv))
        }
        Kind::Ind => {
            let motive = Name::new("motive");
            let mv = Expr::Var(motive.clone());
            locals.push((motive, arrow(quot.clone(), Expr::Sort(Level::Nat(0)))));
            let mk = c(QUOT_MK, vec![u]).app(av.clone()).app(rv).app(a_expr);
            let minor = Expr::pi(a, av, mv.clone().app(mk));
            let q = Name::new("q");
            arrow(minor, Expr::pi(q.clone(), quot, mv.app(Expr::Var(q))))
        }
    };
    telescope(&locals, result)
}

pub fn primitives() -> Vec<(&'static str, &'static str, Vec<String>, Expr)> {
    PRIMITIVES
        .iter()
        .map(|p| {
            let params: Vec<String> = p
                .params
                .iter()
                .map(std::string::ToString::to_string)
                .collect();
            let ty = signature(p.kind, &params, false);
            (p.name, p.kind.label(), params, ty)
        })
        .collect()
}

impl Environment {
    pub fn init_quotient(&mut self) -> Result<()> {
        for (name, kind, params, ty) in primitives() {
            self.declare_quotient(name.into(), params, ty, kind)?;
        }
        Ok(())
    }

    pub fn declare_quotient(
        &mut self,
        name: String,
        params: Vec<String>,
        ty: Expr,
        kind: &str,
    ) -> Result<()> {
        let primitive = PRIMITIVES
            .iter()
            .find(|p| p.kind.label() == kind)
            .ok_or_else(|| Error::Rejected("invalid quotient kind".into()))?;
        let encoded = name.starts_with('[');
        let sym = |s: &str| symbol(s, encoded);
        if name != sym(primitive.name) || params.len() != primitive.params.len() {
            return Err(Error::Rejected(
                "incorrect quotient name or universe parameter count".into(),
            ));
        }
        for dependency in primitive.prerequisites {
            if !self.quotients.contains(&sym(dependency)) {
                return Err(Error::Rejected(
                    "missing validated quotient primitive".into(),
                ));
            }
        }
        self.validate_quotient_equality(encoded)?;
        let expected = signature(primitive.kind, &params, encoded);
        let mut tc = Checker::new(self);
        tc.uparams = params.iter().cloned().collect();
        tc.sort(&ty)?;
        if !tc.conv(&ty, &expected)? {
            return Err(Error::Rejected(
                "incorrect quotient primitive signature".into(),
            ));
        }
        self.declare(name.clone(), params, ty, None, false)?;
        self.quotients.insert(name);
        Ok(())
    }

    fn validate_quotient_equality(&self, encoded: bool) -> Result<()> {
        let eq_name = symbol(EQ, encoded);
        let refl_name = symbol(EQ_REFL, encoded);
        let bad = || {
            Error::Rejected(
                "quotient requires the standard Eq inductive and Eq.refl constructor".into(),
            )
        };
        let eq = self.inductives.get(&eq_name).ok_or_else(bad)?;
        let refl = self.constructors.get(&refl_name).ok_or_else(bad)?;
        if eq.params.len() != 1
            || eq.num_params != 2
            || eq.num_indices != 1
            || eq.constructors != [refl_name]
            || refl.params.len() != 1
            || refl.inductive != eq_name
        {
            return Err(bad());
        }
        let a_ty = Name::new("A");
        let av = Expr::Var(a_ty.clone());
        let expected = Expr::pi(
            a_ty.clone(),
            Expr::Sort(Level::Param(eq.params[0].clone())),
            arrow(av.clone(), arrow(av.clone(), Expr::Sort(Level::Nat(0)))),
        );
        let mut tc = Checker::new(self);
        tc.uparams = eq.params.iter().cloned().collect();
        if !tc.conv(&eq.ty, &expected)? {
            return Err(bad());
        }
        let u = Level::Param(refl.params[0].clone());
        let a = Name::new("a");
        let value = Expr::Var(a.clone());
        let expected = telescope(
            &[(a_ty, Expr::Sort(u.clone())), (a, av.clone())],
            Expr::Const(eq_name, vec![u])
                .app(av)
                .app(value.clone())
                .app(value),
        );
        let mut tc = Checker::new(self);
        tc.uparams = refl.params.iter().cloned().collect();
        if !tc.conv(&refl.ty, &expected)? {
            return Err(bad());
        }
        Ok(())
    }
}

impl Checker<'_> {
    pub(super) fn quotient_eliminator(&self, name: &str) -> Option<Eliminator> {
        if !self.env.quotients.contains(name) {
            return None;
        }
        if *name == self.builtin_name(QUOT_LIFT) {
            Some(Eliminator {
                major: QUOT_LIFT_MAJOR,
                function: QUOT_FN,
            })
        } else if *name == self.builtin_name(QUOT_IND) {
            Some(Eliminator {
                major: QUOT_IND_MAJOR,
                function: QUOT_FN,
            })
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn quotient_does_not_accept_an_axiom_in_place_of_equality() {
        let mut env = Environment::new();
        env.axiom(EQ, Expr::Sort(Level::Nat(1))).unwrap();
        let error = env
            .declare_quotient(
                QUOT.into(),
                vec!["u".into()],
                Expr::Sort(Level::Nat(1)),
                "type",
            )
            .unwrap_err();
        assert!(error.to_string().contains("standard Eq"));
        assert!(env.infer(&Expr::constant(QUOT)).is_err());
    }
}
