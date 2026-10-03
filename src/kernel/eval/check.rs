//! Type inference and conversion over suspended terms. A lambda's type stores
//! an inference closure; applying it extends the environment without opening or
//! substituting syntax. Quotation is reserved for public results, errors, and
//! adapters to the existing neutral projection and recursor reduction rules.
use super::*;

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
        // A semantic session spans several binder scopes. Proof equality is
        // handled by conversion, never by replacing a proof with a variable
        // from another scope during evaluation.
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
    fn body(
        &self,
        binder: &crate::syntax::Binder,
        context: Option<Rc<Frame>>,
        infer: bool,
    ) -> Body {
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
                    Ok(View::Pi(d, self.body(b, v.context, false)))
                } else {
                    Ok(View::Value(v))
                }
            }
        }
    }
    fn quote_type(&mut self, ty: &Type) -> Result<Expr> {
        stacker::maybe_grow(256 * 1024, 16 * 1024 * 1024, || self.quote_type_core(ty))
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
            View::Value(Value {
                head: Expr::Sort(u),
                args,
                ..
            }) if args.is_empty() => Ok(u),
            _ => Err(Error("expected a type".into())),
        }
    }
    fn type_sort(&mut self, ty: &Type) -> Result<Level> {
        if let Some(level) = self.sorts.get(&ty.id()) {
            return Ok(level.clone());
        }
        let level = stacker::maybe_grow(256 * 1024, 16 * 1024 * 1024, || self.type_sort_core(ty))?;
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
        let ty = stacker::maybe_grow(256 * 1024, 16 * 1024 * 1024, || {
            self.infer_core(e, checking)
        })?;
        self.inferred.insert(key, ty.clone());
        Ok(ty)
    }
    fn infer_core(&mut self, e: &Thunk, checking: bool) -> Result<Type> {
        self.ev.tc.tick()?;
        let ty = match &*e.expr {
            Expr::Nat(_) => self.ev.tc.literal_type("Nat")?,
            Expr::Str(_) => self.ev.tc.literal_type("String")?,
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
        let Expr::Const(n, levels) = v.head else {
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
        let subst = self.ev.tc.level_arguments(&ctor.params, &levels)?;
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
                    // The compact support bitmap omits very deep indices.
                    // Preserve the exact projection rule in that rare case.
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

    fn conv(&mut self, a: &Type, b: &Type, types: bool) -> Result<bool> {
        if a.id() == b.id() {
            return Ok(true);
        }
        let key = (a.id().min(b.id()), a.id().max(b.id()), types);
        if let Some(result) = self.equal.get(&key) {
            return Ok(*result);
        }
        let result =
            stacker::maybe_grow(256 * 1024, 16 * 1024 * 1024, || self.conv_core(a, b, types))?;
        self.equal.insert(key, result);
        Ok(result)
    }
    fn conv_terms(&mut self, a: &Thunk, b: &Thunk, types: bool) -> Result<bool> {
        self.conv(&Type::Term(a.clone()), &Type::Term(b.clone()), types)
    }
    fn conv_core(&mut self, a: &Type, b: &Type, types: bool) -> Result<bool> {
        self.ev.tc.tick()?;
        #[cfg(feature = "profile")]
        crate::profile::count("semantic_conversions");
        if !types && let (Type::Term(at), Type::Term(bt)) = (a, b) {
            let ta = self.infer(at, false)?;
            if self.type_sort(&ta)?.equivalent(&Level::Nat(0))? {
                let tb = self.infer(bt, false)?;
                return self.conv(&ta, &tb, true);
            }
        }
        let av = self.view(a, false)?;
        let bv = self.view(b, false)?;
        match (&av, &bv) {
            (View::Pi(ad, ab), View::Pi(bd, bb)) => {
                if !self.conv_terms(ad, bd, true)? {
                    return Ok(false);
                }
                let x = self.fresh(ad);
                let at = self.apply_body(ab, &x)?;
                let bt = self.apply_body(bb, &x)?;
                return self.conv(&at, &bt, true);
            }
            (View::Value(av), View::Value(bv)) if self.congruent(av, bv)? => return Ok(true),
            _ => {}
        }
        // Unfold the newer declaration first, keeping arguments suspended.
        let da = self.delta(&av)?;
        let db = self.delta(&bv)?;
        match (da, db) {
            (Some((ao, at)), Some((bo, bt))) => {
                return if ao > bo {
                    self.conv(&at, b, types)
                } else if bo > ao {
                    self.conv(a, &bt, types)
                } else {
                    self.conv(&at, &bt, types)
                };
            }
            (Some((_, at)), None) => return self.conv(&at, b, types),
            (None, Some((_, bt))) => return self.conv(a, &bt, types),
            _ => {}
        }
        let (View::Value(av), View::Value(bv)) = (av, bv) else {
            return Ok(false);
        };
        let (Type::Term(at), Type::Term(bt)) = (a, b) else {
            return Ok(false);
        };
        if let Expr::Nat(n) = &av.head {
            return self.nat_eq(&n.0, &bv);
        }
        if let Expr::Nat(n) = &bv.head {
            return self.nat_eq(&n.0, &av);
        }
        if let Expr::Str(s) = &av.head {
            let expanded = self.ev.tc.string_constructor(s)?;
            let expanded = self.ev.term(expanded, None);
            return self.conv_terms(&expanded, bt, false);
        }
        if let Expr::Str(s) = &bv.head {
            let expanded = self.ev.tc.string_constructor(s)?;
            let expanded = self.ev.term(expanded, None);
            return self.conv_terms(at, &expanded, false);
        }
        if let Expr::Lam(d, binder) = &av.head {
            let domain = self.ev.term_at(d.clone(), av.context.clone(), 0);
            let bty = self.infer(bt, false)?;
            if let View::Pi(bdomain, _) = self.view(&bty, true)? {
                if !self.conv_terms(&domain, &bdomain, true)? {
                    return Ok(false);
                }
                let x = self.fresh(&domain);
                let body = self.body(binder, av.context.clone(), false);
                let lhs = self.apply_body(&body, &x)?;
                let rhs = Type::Term(self.app(bt, &x));
                return self.conv(&lhs, &rhs, false);
            }
        }
        if matches!(bv.head, Expr::Lam(..)) {
            return self.conv(b, a, types);
        }
        if !types {
            let ta = self.infer(at, false)?;
            if let View::Value(tv) = self.view(&ta, true)?
                && let Expr::Const(n, _) = tv.head
                && self.ev.tc.structure(&n).is_some_and(|c| c.num_fields == 0)
            {
                let tb = self.infer(bt, false)?;
                return self.conv(&ta, &tb, true);
            }
            if self.eta(at, bt, &bv)? || self.eta(bt, at, &av)? {
                return Ok(true);
            }
        }
        Ok(false)
    }
    fn congruent(&mut self, a: &Value, b: &Value) -> Result<bool> {
        if a.args.len() != b.args.len() {
            return Ok(false);
        }
        let heads = match (&a.head, &b.head) {
            (Expr::Sort(a), Expr::Sort(b)) => a.equivalent(b)?,
            (Expr::Nat(a), Expr::Nat(b)) => a == b,
            (Expr::Str(a), Expr::Str(b)) => a == b,
            (Expr::Var(a), Expr::Var(b)) => a == b,
            (Expr::Const(an, au), Expr::Const(bn, bu)) if an == bn && au.len() == bu.len() => {
                let mut equal = true;
                for (a, b) in au.iter().zip(bu) {
                    if !a.equivalent(b)? {
                        equal = false;
                        break;
                    }
                }
                equal
            }
            (Expr::Proj(an, ai, ae), Expr::Proj(bn, bi, be)) if an == bn && ai == bi => {
                let ae = self.ev.term_at(ae.clone(), a.context.clone(), 0);
                let be = self.ev.term_at(be.clone(), b.context.clone(), 0);
                self.conv_terms(&ae, &be, false)?
            }
            (Expr::Lam(ad, ab), Expr::Lam(bd, bb)) => {
                let ad = self.ev.term_at(ad.clone(), a.context.clone(), 0);
                let bd = self.ev.term_at(bd.clone(), b.context.clone(), 0);
                if !self.conv_terms(&ad, &bd, true)? {
                    return Ok(false);
                }
                let x = self.fresh(&ad);
                let ab = self.body(ab, a.context.clone(), false);
                let bb = self.body(bb, b.context.clone(), false);
                let at = self.apply_body(&ab, &x)?;
                let bt = self.apply_body(&bb, &x)?;
                self.conv(&at, &bt, false)?
            }
            _ => false,
        };
        if !heads {
            return Ok(false);
        }
        for (a, b) in a.args.iter().zip(&b.args) {
            if !self.conv_terms(a, b, false)? {
                return Ok(false);
            }
        }
        Ok(true)
    }
    fn delta(&mut self, view: &View) -> Result<Option<(usize, Type)>> {
        let View::Value(v) = view else {
            return Ok(None);
        };
        let Expr::Const(n, us) = &v.head else {
            return Ok(None);
        };
        let d = self.ev.tc.decl(n)?;
        let Some(body) = &d.value else {
            return Ok(None);
        };
        let subst = self.ev.tc.level_arguments(&d.params, us)?;
        let body = self.ev.tc.substitute_levels(body, &subst)?;
        let mut term = self.ev.term(body, None);
        for arg in &v.args {
            term = self.app(&term, arg);
        }
        Ok(Some((d.order, Type::Term(term))))
    }
    fn nat_eq(&mut self, n: &num_bigint::BigUint, value: &Value) -> Result<bool> {
        use num_traits::{One, Zero};
        let mut n = n.clone();
        let mut value = value.clone();
        loop {
            match &value.head {
                Expr::Nat(m) => return Ok(value.args.is_empty() && n == m.0),
                Expr::Const(c, us)
                    if us.is_empty() && *c == self.ev.tc.builtin_name("Nat.zero") =>
                {
                    return Ok(value.args.is_empty() && n.is_zero());
                }
                Expr::Const(c, us)
                    if us.is_empty()
                        && *c == self.ev.tc.builtin_name("Nat.succ")
                        && value.args.len() == 1
                        && !n.is_zero() =>
                {
                    n -= num_bigint::BigUint::one();
                    value = self.ev.eval(&value.args[0], true)?;
                }
                _ => return Ok(false),
            }
        }
    }
    fn eta(&mut self, a: &Thunk, b: &Thunk, bv: &Value) -> Result<bool> {
        let Expr::Const(n, _) = &bv.head else {
            return Ok(false);
        };
        let Some(ctor) = self.ev.tc.env.constructors.get(n).cloned() else {
            return Ok(false);
        };
        if self.ev.tc.structure(&ctor.inductive).is_none()
            || bv.args.len() != ctor.num_params + ctor.num_fields
        {
            return Ok(false);
        }
        let at = self.infer(a, false)?;
        let bt = self.infer(b, false)?;
        if !self.conv(&at, &bt, true)? {
            return Ok(false);
        }
        for (i, field) in bv.args[ctor.num_params..].iter().enumerate() {
            let proj = self.projection(&ctor.inductive, i, a);
            if !self.conv_terms(&proj, field, false)? {
                return Ok(false);
            }
        }
        Ok(true)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::{parse_expr, run};

    fn expr(source: &str) -> Expr {
        parse_expr(source).unwrap()
    }

    #[test]
    fn dependent_inference_and_conversion_keep_closures() {
        let mut env = Environment::new();
        run("axiom A : Type; axiom a : A; axiom B : (forall (x : A), Type); axiom f : (forall (x : A), B x)", &mut env).unwrap();
        let mut tc = Checker::new(&env);
        let mut s = Session::new(&mut tc);
        let value = s.ev.term(expr("fun (T : Type) => fun (x : T) => x"), None);
        let expected =
            s.ev.term(expr("forall (T : Type), forall (x : T), T"), None);
        let actual = s.infer(&value, true).unwrap();
        s.check_type(&actual, &expected).unwrap();
        let value =
            s.ev.term(expr("(fun (g : (forall (x : A), B x)) => g a) f"), None);
        let expected = s.ev.term(expr("B a"), None);
        let actual = s.infer(&value, true).unwrap();
        s.check_type(&actual, &expected).unwrap();
        assert!(s.ev.state.quoted.is_empty());
    }

    #[test]
    fn unchecked_inference_does_not_validate_discarded_arguments() {
        let mut env = Environment::new();
        run("axiom A : Type; axiom a : A", &mut env).unwrap();
        let mut tc = Checker::new(&env);
        let mut s = Session::new(&mut tc);
        for source in ["(fun (x : A) => a) Type", "let x : A := Type in a"] {
            let value = s.ev.term(expr(source), None);
            assert!(s.infer(&value, false).is_ok());
            assert!(s.infer(&value, true).is_err());
        }
    }

    #[test]
    fn inference_closures_do_not_capture_sibling_binders() {
        let env = Environment::new();
        for source in [
            "fun (T : Type) => fun (x : T) => x",
            "fun (T : Type) => fun (U : Type) => fun (x : T) => fun (y : U) => x",
            "fun (T : Type) => let U : Type := T in fun (x : U) => x",
        ] {
            let e = expr(source);
            let actual = env.infer(&e).unwrap();
            let mut legacy = Checker::new(&env);
            legacy.semantic = false;
            let expected = legacy.infer(&e).unwrap();
            assert!(actual.fv().is_empty());
            assert!(legacy.conv(&actual, &expected).unwrap());
            env.check(&e, &actual).unwrap();
        }
    }

    #[test]
    fn semantic_conversion_agrees_with_syntax_kernel() {
        let mut env = Environment::new();
        run("axiom A : Type; axiom a : A; axiom b : A; axiom P : Prop; axiom p : P; axiom q : P; axiom f : (forall (x : A), A); def id : (forall (x : A), A) := fun (x : A) => x", &mut env).unwrap();
        let terms = [
            "a",
            "b",
            "id a",
            "let x : A := a in x",
            "f a",
            "p",
            "q",
            "f",
            "fun (x : A) => f x",
            "fun (x : A) => x",
            "fun (x : A) => a",
        ];
        for a in terms.map(expr) {
            for b in terms.map(expr) {
                let mut legacy = Checker::new(&env);
                legacy.semantic = false;
                let ta = legacy.infer(&a).unwrap();
                let tb = legacy.infer(&b).unwrap();
                let expected = legacy.conv(&ta, &tb).unwrap() && legacy.conv(&a, &b).unwrap();
                assert_eq!(env.def_eq(&a, &b).unwrap(), expected, "{a} vs {b}");
            }
        }
    }
}
