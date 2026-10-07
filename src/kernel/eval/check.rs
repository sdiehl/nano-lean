use super::*;
use crate::{syntax::Binder, term::names::*};
use rustc_hash::FxHashSet;
mod conv;
mod summary;
#[cfg(test)]
mod tests;

#[derive(Clone)]
enum Type {
    Term(Thunk),
    Pi(Rc<InferredPi>),
}

struct InferredPi {
    id: usize,
    domain: Thunk,
    body: Body,
    closed: bool,
}
impl Drop for InferredPi {
    fn drop(&mut self) {
        let mut next = self.body.constant.take();
        while let Some(Type::Pi(pi)) = next {
            match Rc::try_unwrap(pi) {
                Ok(mut pi) => next = pi.body.constant.take(),
                Err(_) => break,
            }
        }
    }
}
#[derive(Clone)]
struct Body {
    expr: Shared<Expr>,
    context: Option<Rc<Frame>>,
    infer: bool,
    constant: Option<Type>,
}
enum View {
    Pi(Thunk, Body),
    Value(Value),
}
impl Type {
    fn id(&self) -> usize {
        match self {
            Self::Term(t) => t.id,
            Self::Pi(p) => p.id,
        }
    }
}

struct Session<'b, 'a> {
    ev: Evaluator<'b, 'a>,
    inferred: HashMap<(usize, bool), Type>,
    variables: HashMap<Name<Expr>, Thunk>,
    equal: HashMap<(usize, usize, bool), bool>,
    sorts: HashMap<usize, Level>,
    relevance_active: FxHashSet<(String, Vec<Level>)>,
    proof_status: HashMap<usize, Option<bool>>,
    previous_semantic: bool,
}
impl Drop for Session<'_, '_> {
    fn drop(&mut self) {
        self.ev.tc.semantic = self.previous_semantic;
    }
}

impl Checker<'_> {
    pub(in crate::kernel) fn semantic_infer(&mut self, e: &Expr) -> Result<Expr> {
        let checking = self.checking;
        let mut s = Session::new(self);
        let e = s.ev.term(e.clone(), None);
        let ty = s.infer(&e, checking)?;
        s.quote_type(&ty)
    }
    pub(in crate::kernel) fn semantic_sort(&mut self, e: &Expr) -> Result<Level> {
        let checking = self.checking;
        let mut s = Session::new(self);
        let e = s.ev.term(e.clone(), None);
        s.sort(&e, checking)
    }
    pub(in crate::kernel) fn semantic_check(&mut self, e: &Expr, expected: &Expr) -> Result<()> {
        let mut s = Session::new(self);
        let e = s.ev.term(e.clone(), None);
        let expected = s.ev.term(expected.clone(), None);
        let actual = s.infer(&e, true)?;
        s.check_type(&actual, &expected)
    }
    pub(in crate::kernel) fn semantic_conv(&mut self, a: &Expr, b: &Expr) -> Result<bool> {
        let mut s = Session::new(self);
        let a = Type::Term(s.ev.term(a.clone(), None));
        let b = Type::Term(s.ev.term(b.clone(), None));
        s.conv(&a, &b, false)
    }
    pub(in crate::kernel) fn semantic_def_eq(&mut self, a: &Expr, b: &Expr) -> Result<bool> {
        let mut s = Session::new(self);
        let a = s.ev.term(a.clone(), None);
        let b = s.ev.term(b.clone(), None);
        let ta = s.infer(&a, true)?;
        let tb = s.infer(&b, true)?;
        Ok(s.conv(&ta, &tb, true)? && s.conv_terms(&a, &b, false)?)
    }
}

impl<'b, 'a> Session<'b, 'a> {
    fn new(tc: &'b mut Checker<'a>) -> Self {
        let previous_semantic = tc.semantic;
        tc.semantic = false;
        let mut ev = Evaluator::new(tc);
        // A session spans binder scopes, so a proof from another scope must not be reused.
        ev.reuse_proofs = false;
        let variables = ev
            .tc
            .locals
            .clone()
            .into_iter()
            .map(|(n, t)| (n, ev.term(t, None)))
            .collect();
        Self {
            ev,
            inferred: HashMap::default(),
            variables,
            equal: HashMap::default(),
            sorts: HashMap::default(),
            relevance_active: FxHashSet::default(),
            proof_status: HashMap::default(),
            previous_semantic,
        }
    }
    fn fresh(&mut self, domain: &Thunk) -> Thunk {
        let name = Name::new("_");
        self.variables.insert(name.clone(), domain.clone());
        self.ev.variables.push((name.clone(), domain.clone()));
        self.ev.term(Expr::Var(name), None)
    }
    fn child(&mut self, expr: &Shared<Expr>, parent: &Thunk) -> Thunk {
        self.ev.term_at(expr.clone(), parent.context.clone(), 0)
    }
    fn closed_type(&mut self, ty: &Type) -> bool {
        match ty {
            Type::Pi(p) => p.closed,
            Type::Term(t) => {
                let id = self.ev.tc.cache.shared(&t.expr);
                t.context.is_none() && self.ev.tc.cache.is_closed(id)
            }
        }
    }
    fn apply_body(&mut self, body: &Body, arg: &Thunk) -> Result<Type> {
        if let Some(ty) = &body.constant {
            return Ok(ty.clone());
        }
        let frame = self.ev.frame(arg.clone(), body.context.clone());
        let term = self.ev.term_at(body.expr.clone(), Some(frame), 0);
        if body.infer {
            self.infer(&term, false)
        } else {
            Ok(Type::Term(term))
        }
    }
    fn body(&self, binder: &Binder, context: Option<Rc<Frame>>, infer: bool) -> Body {
        Body {
            expr: binder.body().clone(),
            context,
            infer,
            constant: None,
        }
    }
    fn view(&mut self, ty: &Type, unfold: bool) -> Result<View> {
        match ty {
            Type::Pi(p) => Ok(View::Pi(p.domain.clone(), p.body.clone())),
            Type::Term(t) => {
                let v = self.ev.eval(t, unfold)?;
                if let Expr::Pi(d, b) = &v.head {
                    let d = self.ev.term_at(d.clone(), v.context.clone(), 0);
                    Ok(View::Pi(d, self.body(b, v.context.clone(), false)))
                } else {
                    Ok(View::Value(v))
                }
            }
        }
    }
    fn quote_type(&mut self, ty: &Type) -> Result<Expr> {
        grow(|| self.quote_type_core(ty))
    }
    fn quote_type_core(&mut self, ty: &Type) -> Result<Expr> {
        match ty {
            Type::Term(t) => Ok(self.ev.quote(t, 0)),
            Type::Pi(p) => {
                let x = self.fresh(&p.domain);
                let Expr::Var(n) = &*x.expr else {
                    unreachable!()
                };
                let body = self.apply_body(&p.body, &x)?;
                let body = self.quote_type(&body)?;
                Ok(Expr::pi(n.clone(), self.ev.quote(&p.domain, 0), body))
            }
        }
    }
    fn sort(&mut self, e: &Thunk, checking: bool) -> Result<Level> {
        let ty = self.infer(e, checking)?;
        match self.view(&ty, true)? {
            View::Value(v) if v.args.is_empty() => match &v.head {
                Expr::Sort(u) => Ok(u.clone()),
                _ => Err(Error("expected a type".into())),
            },
            _ => Err(Error("expected a type".into())),
        }
    }
    fn type_sort(&mut self, ty: &Type) -> Result<Level> {
        if let Some(level) = self.sorts.get(&ty.id()) {
            return Ok(level.clone());
        }
        let level = grow(|| self.type_sort_core(ty))?;
        self.sorts.insert(ty.id(), level.clone());
        Ok(level)
    }
    fn type_sort_core(&mut self, ty: &Type) -> Result<Level> {
        match ty {
            Type::Term(t) => self.sort(t, false),
            Type::Pi(p) => {
                let u = self.sort(&p.domain, false)?;
                let x = self.fresh(&p.domain);
                let body = self.apply_body(&p.body, &x)?;
                Ok(Level::imax(u, self.type_sort(&body)?))
            }
        }
    }
    fn check_type(&mut self, actual: &Type, expected: &Thunk) -> Result<()> {
        if self.conv(actual, &Type::Term(expected.clone()), true)? {
            return Ok(());
        }
        let actual = self.quote_type(actual)?;
        let expected = self.ev.quote(expected, 0);
        Err(Error(format!(
            "type mismatch:\n  expected: {expected}\n  inferred: {actual}"
        )))
    }
    fn infer(&mut self, e: &Thunk, checking: bool) -> Result<Type> {
        let key = (e.id, checking);
        if let Some(ty) = self.inferred.get(&key) {
            return Ok(ty.clone());
        }
        if !checking && let Some(ty) = self.inferred.get(&(e.id, true)) {
            return Ok(ty.clone());
        }
        let ty = grow(|| self.infer_core(e, checking))?;
        self.inferred.insert(key, ty.clone());
        Ok(ty)
    }
    fn infer_core(&mut self, e: &Thunk, checking: bool) -> Result<Type> {
        self.ev.tc.tick()?;
        let ty = match &*e.expr {
            Expr::Nat(_) => self.ev.tc.literal_type(NAT)?,
            Expr::Str(_) => self.ev.tc.literal_type(STRING)?,
            Expr::Sort(u) => {
                self.ev.tc.valid_level(u)?;
                Expr::Sort(u.clone().succ()?)
            }
            Expr::Const(n, us) => {
                let d = self.ev.tc.decl(n)?;
                let subst = self.ev.tc.level_arguments(&d.params, us)?;
                self.ev.tc.substitute_levels(&d.ty, &subst)?
            }
            Expr::Var(n) => {
                return self
                    .variables
                    .get(n)
                    .cloned()
                    .map(Type::Term)
                    .ok_or_else(|| Error(format!("unbound variable: {n}")));
            }
            Expr::Pi(d, b) | Expr::Lam(d, b) => {
                let domain = self.child(d, e);
                let is_pi = matches!(&*e.expr, Expr::Pi(..));
                let u = if checking || is_pi {
                    self.sort(&domain, checking)?
                } else {
                    Level::Nat(0)
                };
                let mut body = self.body(b, e.context.clone(), !is_pi);
                if is_pi || checking {
                    let x = self.fresh(&domain);
                    let frame = self.ev.frame(x, e.context.clone());
                    let opened = self.ev.term_at(b.body().clone(), Some(frame), 0);
                    if is_pi {
                        let v = self.sort(&opened, checking)?;
                        return Ok(Type::Term(
                            self.ev.term(Expr::Sort(Level::imax(u, v)), None),
                        ));
                    }
                    let result = self.infer(&opened, true)?;
                    if self.closed_type(&result) {
                        body.constant = Some(result);
                        body.context = None;
                    }
                }
                let closed =
                    self.closed_type(&Type::Term(domain.clone())) && body.constant.is_some();
                let id = self.ev.state.next_term;
                self.ev.state.next_term += 1;
                return Ok(Type::Pi(Rc::new(InferredPi {
                    id,
                    domain,
                    body,
                    closed,
                })));
            }
            Expr::App(..) => {
                let mut head = e.clone();
                let mut args = Vec::new();
                while let Expr::App(f, a) = &*head.expr {
                    args.push(self.child(a, &head));
                    head = self.child(f, &head);
                }
                let mut ty = self.infer(&head, checking)?;
                for arg in args.into_iter().rev() {
                    let View::Pi(domain, body) = self.view(&ty, true)? else {
                        return Err(Error("expected a function".into()));
                    };
                    if checking {
                        let actual = self.infer(&arg, true)?;
                        self.check_type(&actual, &domain)?;
                    }
                    ty = self.apply_body(&body, &arg)?;
                }
                return Ok(ty);
            }
            Expr::Let(t, v, b) => {
                let ty = self.child(t, e);
                let value = self.child(v, e);
                if checking {
                    self.sort(&ty, true)?;
                    let actual = self.infer(&value, true)?;
                    self.check_type(&actual, &ty)?;
                }
                let frame = self.ev.frame(value, e.context.clone());
                let body = self.ev.term_at(b.body().clone(), Some(frame), 0);
                return self.infer(&body, checking);
            }
            Expr::Proj(n, i, source) => {
                let source = self.child(source, e);
                return self.projection_type(n, *i, &source, checking);
            }
        };
        Ok(Type::Term(self.ev.term(ty, None)))
    }
    fn app(&mut self, f: &Thunk, a: &Thunk) -> Thunk {
        self.ev.apply(f, a)
    }
    fn projection(&mut self, name: &str, index: usize, source: &Thunk) -> Thunk {
        let context = self.ev.frame(source.clone(), None);
        self.ev.term(
            Expr::Proj(
                name.into(),
                index,
                Shared::new(Expr::Var(Name::bound(0, 0))),
            ),
            Some(context),
        )
    }
    fn projection_type(
        &mut self,
        name: &str,
        index: usize,
        source: &Thunk,
        checking: bool,
    ) -> Result<Type> {
        let ty = self.infer(source, checking)?;
        let View::Value(v) = self.view(&ty, true)? else {
            return Err(Error("projection from non-inductive type".into()));
        };
        let Expr::Const(n, levels) = &v.head else {
            return Err(Error("projection from non-inductive type".into()));
        };
        if n != name {
            return Err(Error("projection type name mismatch".into()));
        }
        let info = self
            .ev
            .tc
            .env
            .inductives
            .get(name)
            .ok_or_else(|| Error("projection from non-inductive type".into()))?;
        if info.constructors.len() != 1 || v.args.len() != info.num_params + info.num_indices {
            return Err(Error(
                "projection requires a single-constructor inductive".into(),
            ));
        }
        let ctor = self.ev.tc.env.constructors[&info.constructors[0]].clone();
        if index >= ctor.num_fields {
            return Err(Error("projection field out of range".into()));
        }
        let subst = self.ev.tc.level_arguments(&ctor.params, levels)?;
        let expr = self.ev.tc.substitute_levels(&ctor.ty, &subst)?;
        let mut field = Type::Term(self.ev.term(expr, None));
        for arg in v.args.iter().take(ctor.num_params) {
            let View::Pi(_, body) = self.view(&field, true)? else {
                return Err(Error("invalid constructor telescope".into()));
            };
            field = self.apply_body(&body, arg)?;
        }
        let prop = self.type_sort(&ty)?.equivalent(&Level::Nat(0))?;
        for i in 0..=index {
            let View::Pi(domain, body) = self.view(&field, true)? else {
                return Err(Error("invalid projection telescope".into()));
            };
            let body_id = self.ev.tc.cache.id(&body.expr);
            let dependent = match self.ev.tc.cache.bound_support(body_id) {
                Some(bits) => bits.first().is_some_and(|w| w & 1 != 0),
                None => {
                    // The support bitmap omits very deep indices, so test free variables exactly.
                    let (name, opened) = bind(Name::<Expr>::new("_"), body.expr.clone()).unbind();
                    opened.fv().contains(&name.to_any().unwrap())
                }
            };
            if prop
                && (i == index || dependent)
                && !self.sort(&domain, false)?.equivalent(&Level::Nat(0))?
            {
                return Err(Error("projection eliminates proposition into data".into()));
            }
            if i == index {
                return Ok(Type::Term(domain));
            }
            let arg = self.projection(name, i, source);
            field = self.apply_body(&body, &arg)?;
        }
        unreachable!()
    }
}
