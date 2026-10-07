#[cfg(test)]
use super::inductive::spine;
use super::{Checker, Environment, Error, Result};
use crate::{Expr, Level};
use unbound::Name;

fn symbol(path: &str, encoded: bool) -> String {
    if encoded {
        serde_json::to_string(&path.split('.').collect::<Vec<_>>()).unwrap()
    } else {
        path.into()
    }
}
fn arrow(domain: Expr, result: Expr) -> Expr {
    Expr::pi(Name::new("_"), domain, result)
}
fn telescope(locals: &[(Name<Expr>, Expr)], result: Expr) -> Expr {
    locals.iter().rev().fold(result, |body, (n, ty)| {
        Expr::pi(n.clone(), ty.clone(), body)
    })
}

/// The type the kernel expects for a quotient primitive.
fn signature(kind: &str, params: &[String], encoded: bool) -> Expr {
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
    let quot = c("Quot", vec![u.clone()]).app(av.clone()).app(rv.clone());
    let a = Name::new("a");
    let a_expr = Expr::Var(a.clone());
    let result = match kind {
        "type" => Expr::Sort(u.clone()),
        "ctor" => arrow(av.clone(), quot.clone()),
        "lift" => {
            let b_ty = Name::new("B");
            let bv = Expr::Var(b_ty.clone());
            let f = Name::new("f");
            let fv = Expr::Var(f.clone());
            locals.push((b_ty, Expr::Sort(v.clone())));
            locals.push((f, arrow(av.clone(), bv.clone())));
            let b = Name::new("b");
            let b_expr = Expr::Var(b.clone());
            let eq = c("Eq", vec![v])
                .app(bv.clone())
                .app(fv.clone().app(a_expr.clone()))
                .app(fv.app(b_expr.clone()));
            let respects = telescope(
                &[(a, av.clone()), (b, av.clone())],
                arrow(rv.app(a_expr).app(b_expr), eq),
            );
            arrow(respects, arrow(quot, bv))
        }
        "ind" => {
            let motive = Name::new("motive");
            let mv = Expr::Var(motive.clone());
            locals.push((motive, arrow(quot.clone(), Expr::Sort(Level::Nat(0)))));
            let mk = c("Quot.mk", vec![u]).app(av.clone()).app(rv).app(a_expr);
            let minor = Expr::pi(a, av, mv.clone().app(mk));
            let q = Name::new("q");
            arrow(minor, Expr::pi(q.clone(), quot, mv.app(Expr::Var(q))))
        }
        _ => unreachable!(),
    };
    telescope(&locals, result)
}

/// Lean's `init_quot` primitives: name, kind, universe parameters and type.
pub fn primitives() -> Vec<(&'static str, &'static str, Vec<String>, Expr)> {
    [
        ("Quot", "type", &["u"][..]),
        ("Quot.mk", "ctor", &["u"]),
        ("Quot.lift", "lift", &["u", "v"]),
        ("Quot.ind", "ind", &["u"]),
    ]
    .into_iter()
    .map(|(name, kind, params)| {
        let params: Vec<String> = params.iter().map(|p| p.to_string()).collect();
        let ty = signature(kind, &params, false);
        (name, kind, params, ty)
    })
    .collect()
}

impl Environment {
    /// Declare the quotient primitives, as Lean's `init_quot` does.
    pub fn init_quotient(&mut self) -> Result<()> {
        for (name, kind, params, ty) in primitives() {
            self.declare_quotient(name.into(), params, ty, kind)?;
        }
        Ok(())
    }

    /// Validate the exported primitive against a signature constructed by the checker.
    pub fn declare_quotient(
        &mut self,
        name: String,
        params: Vec<String>,
        ty: Expr,
        kind: &str,
    ) -> Result<()> {
        let (path, arity, prerequisites): (&str, usize, &[&str]) = match kind {
            "type" => ("Quot", 1, &[]),
            "ctor" => ("Quot.mk", 1, &["Quot"]),
            "lift" => ("Quot.lift", 2, &["Quot", "Quot.mk"]),
            "ind" => ("Quot.ind", 1, &["Quot", "Quot.mk"]),
            _ => return Err(Error("invalid quotient kind".into())),
        };
        let encoded = name.starts_with('[');
        let sym = |s: &str| symbol(s, encoded);
        if name != sym(path) || params.len() != arity {
            return Err(Error(
                "incorrect quotient name or universe parameter count".into(),
            ));
        }
        for dependency in prerequisites {
            if !self.quotients.contains(&sym(dependency)) {
                return Err(Error("missing validated quotient primitive".into()));
            }
        }
        self.validate_quotient_equality(encoded)?;
        let expected = signature(kind, &params, encoded);
        let mut tc = Checker::new(self);
        tc.uparams = params.iter().cloned().collect();
        tc.sort(&ty)?;
        if !tc.conv(&ty, &expected)? {
            return Err(Error("incorrect quotient primitive signature".into()));
        }
        self.declare(name.clone(), params, ty, None, false)?;
        self.quotients.insert(name);
        Ok(())
    }

    fn validate_quotient_equality(&self, encoded: bool) -> Result<()> {
        let eq_name = symbol("Eq", encoded);
        let refl_name = symbol("Eq.refl", encoded);
        let bad =
            || Error("quotient requires the standard Eq inductive and Eq.refl constructor".into());
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
    #[cfg(test)]
    pub(super) fn reduce_quotient(&mut self, head: &Expr, args: &[Expr]) -> Result<Option<Expr>> {
        let Expr::Const(name, levels) = head else {
            return Ok(None);
        };
        if !self.env.quotients.contains(name) {
            return Ok(None);
        }
        let (major, function) = if *name == self.builtin_name("Quot.lift") {
            (5, 3)
        } else if *name == self.builtin_name("Quot.ind") {
            (4, 3)
        } else {
            return Ok(None);
        };
        self.level_arguments(&self.decl(name)?.params, levels)?;
        if args.len() <= major {
            return Ok(None);
        }
        let value = self.whnf(&args[major])?;
        let (constructor, fields) = spine(&value);
        if !matches!(constructor, Expr::Const(ref n, _) if *n == self.builtin_name("Quot.mk") && self.env.quotients.contains(n))
            || fields.len() != 3
        {
            return Ok(None);
        }
        let result = args[function].clone().app(fields[2].clone());
        Ok(Some(
            args[major + 1..].iter().cloned().fold(result, Expr::app),
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::Declaration;
    use unbound::Alpha;

    #[test]
    fn quotient_reduction_preserves_trailing_arguments_and_requires_registered_primitives() {
        for (name, major) in [("Quot.lift", 5), ("Quot.ind", 4)] {
            let mut env = Environment::new();
            // This isolates reduction; exported signatures are checked in integration tests.
            env.declarations.insert(
                name.into(),
                std::rc::Rc::new(Declaration {
                    order: 0,
                    params: vec![],
                    ty: Expr::Sort(Level::Nat(0)),
                    value: None,
                    relevance: Default::default(),
                }),
            );
            let f = Expr::constant("minor");
            let value = Expr::constant("value");
            let mk = Expr::constant("Quot.mk")
                .app(Expr::constant("A"))
                .app(Expr::constant("r"))
                .app(value.clone());
            let mut args = vec![Expr::constant("argument"); major + 1];
            args[3] = f.clone();
            args[major] = mk;
            args.push(Expr::constant("extra"));
            let head = Expr::constant(name);
            assert!(
                Checker::new(&env)
                    .reduce_quotient(&head, &args)
                    .unwrap()
                    .is_none()
            );
            env.quotients.extend([name.into(), "Quot.mk".into()]);
            env.declarations.insert(
                "Quot.mk".into(),
                std::rc::Rc::new(Declaration {
                    order: 0,
                    params: vec![],
                    ty: Expr::Sort(Level::Nat(0)),
                    value: None,
                    relevance: Default::default(),
                }),
            );
            let expected = f.app(value).app(Expr::constant("extra"));
            assert!(
                Checker::new(&env)
                    .reduce_quotient(&head, &args)
                    .unwrap()
                    .unwrap()
                    .aeq(&expected)
            );
            assert!(
                Checker::new(&env)
                    .reduce_quotient(&head, &args[..major])
                    .unwrap()
                    .is_none()
            );
            args[major] = Expr::Sort(Level::Nat(0));
            assert!(
                Checker::new(&env)
                    .reduce_quotient(&head, &args)
                    .unwrap()
                    .is_none()
            );
        }
    }

    #[test]
    fn quotient_does_not_accept_an_axiom_in_place_of_equality() {
        let mut env = Environment::new();
        env.axiom("Eq", Expr::Sort(Level::Nat(1))).unwrap();
        let error = env
            .declare_quotient(
                "Quot".into(),
                vec!["u".into()],
                Expr::Sort(Level::Nat(1)),
                "type",
            )
            .unwrap_err();
        assert!(error.0.contains("standard Eq"));
        assert!(env.infer(&Expr::constant("Quot")).is_err());
    }
}
