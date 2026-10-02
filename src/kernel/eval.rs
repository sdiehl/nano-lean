use super::*;
use std::{cell::OnceCell, rc::Rc};

type Thunk = Rc<Term>;
struct Term {
    id: usize,
    expr: Shared<Expr>,
    context: Option<Rc<Frame>>,
    normal: [OnceCell<Value>; 2],
    canonical: OnceCell<usize>,
}
struct Frame {
    id: usize,
    value: Thunk,
    parent: Option<Rc<Frame>>,
}
struct Closure {
    expr: Shared<Expr>,
    context: Option<Rc<Frame>>,
}
impl Closure {
    fn closed(expr: Expr) -> Self {
        Self {
            expr: Shared::new(expr),
            context: None,
        }
    }
}
#[derive(Clone)]
struct Value {
    head: Expr,
    context: Option<Rc<Frame>>,
    args: Vec<Thunk>,
}

struct Instance {
    declaration: Rc<Declaration>,
    substitution: BTreeMap<String, Level>,
}
/// Call-by-need evaluation keeps recursive arguments and proofs suspended.
/// Only the final weak-head value is converted back to the binding representation.
struct Evaluator<'b, 'a> {
    tc: &'b mut Checker<'a>,
    instances: HashMap<usize, Rc<Instance>>,
    bodies: HashMap<usize, Shared<Expr>>,
    rules: HashMap<(usize, usize), Shared<Expr>>,
    next_term: usize,
    next_frame: usize,
    nodes: HashMap<(usize, Vec<usize>), Thunk>,
    old_nodes: HashMap<(usize, Vec<usize>), Thunk>,
    closed: HashMap<usize, Thunk>,
    proofs: HashMap<usize, Thunk>,
    proposition_heads: HashMap<String, Option<usize>>,
    quoted: HashMap<(usize, usize), Expr>,
    applications: HashMap<(usize, Vec<usize>, bool), Value>,
    old_applications: HashMap<(usize, Vec<usize>, bool), Value>,
}

impl<'a> Checker<'a> {
    pub(super) fn whnf_core(&mut self, expr: &Expr, unfold: bool) -> Result<Expr> {
        let mut evaluator = Evaluator {
            tc: self,
            instances: HashMap::default(),
            bodies: HashMap::default(),
            rules: HashMap::default(),
            next_term: 0,
            next_frame: 1,
            nodes: HashMap::default(),
            old_nodes: HashMap::default(),
            closed: HashMap::default(),
            proofs: HashMap::default(),
            proposition_heads: HashMap::default(),
            quoted: HashMap::default(),
            applications: HashMap::default(),
            old_applications: HashMap::default(),
        };
        let root = evaluator.term(expr.clone(), None);
        let value = evaluator.eval(&root, unfold)?;
        Ok(evaluator.quote_value(&value))
    }
}

impl Evaluator<'_, '_> {
    fn term(&mut self, expr: Expr, context: Option<Rc<Frame>>) -> Thunk {
        let id = self.tc.cache.id(&expr);
        self.term_with_id(Shared::new(expr), context, 0, id)
    }
    fn term_at(
        &mut self,
        expr: Shared<Expr>,
        context: Option<Rc<Frame>>,
        quote_depth: usize,
    ) -> Thunk {
        let id = self.tc.cache.shared(&expr);
        self.term_with_id(expr, context, quote_depth, id)
    }
    fn term_with_id(
        &mut self,
        expr: Shared<Expr>,
        mut context: Option<Rc<Frame>>,
        quote_depth: usize,
        id: usize,
    ) -> Thunk {
        if quote_depth == 0
            && let Expr::Var(n) = &*expr
            && let Some((mut d, 0)) = n.coordinates()
        {
            let mut frame = context.clone();
            while let Some(f) = frame {
                if d == 0 {
                    return f.value.clone();
                }
                d -= 1;
                frame = f.parent.clone();
            }
        }
        if !self.tc.cache.has_loose_id(id) {
            context = None;
        }
        let mut dependencies = Vec::new();
        if quote_depth > 0 {
            dependencies.extend([
                usize::MAX,
                context.as_ref().map_or(0, |f| f.id),
                quote_depth,
            ]);
        } else if let Some(bits) = self.tc.cache.bound_support(id) {
            let mut frame = context.clone();
            let mut depth = 0;
            for (i, word) in bits.iter().enumerate() {
                let mut word = *word;
                while word != 0 {
                    let d = i * 64 + word.trailing_zeros() as usize;
                    while depth < d {
                        frame = frame.and_then(|f| f.parent.clone());
                        depth += 1;
                    }
                    dependencies.push(frame.as_ref().map_or(usize::MAX, |f| {
                        f.value.canonical.get().copied().unwrap_or(f.value.id)
                    }));
                    word &= word - 1;
                }
            }
        } else {
            dependencies.extend([usize::MAX, context.as_ref().map_or(0, |f| f.id)]);
        }
        if context.is_none()
            && let Some(t) = self.closed.get(&id)
        {
            return t.clone();
        }
        let key = (id, dependencies);
        if let Some(t) = self.nodes.get(&key) {
            return t.clone();
        }
        if let Some(t) = self.old_nodes.get(&key).cloned() {
            self.nodes.insert(key, t.clone());
            return t;
        }
        if self.nodes.len() >= 262_144 {
            self.old_nodes = std::mem::take(&mut self.nodes);
        }
        let value = Rc::new(Term {
            id: self.next_term,
            expr,
            context,
            normal: [OnceCell::new(), OnceCell::new()],
            canonical: OnceCell::new(),
        });
        self.next_term += 1;
        if value.context.is_none() {
            self.closed.insert(id, value.clone());
        }
        self.nodes.insert(key, value.clone());
        value
    }
    fn frame(&mut self, value: Thunk, parent: Option<Rc<Frame>>) -> Rc<Frame> {
        let f = Rc::new(Frame {
            id: self.next_frame,
            value,
            parent,
        });
        self.next_frame += 1;
        f
    }
    // Reusing a proof of the identical instantiated proposition is justified by
    // proof irrelevance. We never erase its type or invent a proof inhabitant.
    fn proposition(&mut self, domain: &Thunk) -> bool {
        let mut head = domain.clone();
        let mut arity = 0;
        while let Expr::App(f, _) = &*head.expr {
            arity += 1;
            head = self.term_at(f.clone(), head.context.clone(), 0);
        }
        let Expr::Const(name, _) = &*head.expr else {
            return false;
        };
        if let Some(expected) = self.proposition_heads.get(name) {
            return *expected == Some(arity);
        }
        let Some(d) = self.tc.env.declarations.get(name) else {
            return false;
        };
        let mut ty = &d.ty;
        let mut expected = 0;
        while let Expr::Pi(_, b) = ty {
            expected += 1;
            ty = b.body();
        }
        let expected = if matches!(ty, Expr::Sort(Level::Nat(0))) {
            Some(expected)
        } else {
            None
        };
        self.proposition_heads.insert(name.clone(), expected);
        expected == Some(arity)
    }
    fn eval(&mut self, term: &Thunk, unfold: bool) -> Result<Value> {
        if let Some(value) = term.normal[usize::from(unfold)].get() {
            return Ok(value.clone());
        }
        let result =
            stacker::maybe_grow(256 * 1024, 16 * 1024 * 1024, || self.steps(term, unfold))?;
        if result.args.is_empty()
            && result.context.is_none()
            && matches!(result.head, Expr::Nat(_) | Expr::Const(..))
        {
            let canonical = self.term(result.head.clone(), None);
            let _ = term.canonical.set(canonical.id);
        }
        let _ = term.normal[usize::from(unfold)].set(result.clone());
        Ok(result)
    }
    fn steps(&mut self, term: &Thunk, unfold: bool) -> Result<Value> {
        let mut visited = Vec::new();
        let result = self.steps_core(term, unfold, &mut visited)?;
        for (head, args) in visited {
            let key = (
                head,
                args.iter()
                    .map(|a: &Thunk| a.canonical.get().copied().unwrap_or(a.id))
                    .collect(),
                unfold,
            );
            if self.applications.len() >= 524_288 {
                self.old_applications = std::mem::take(&mut self.applications);
            }
            self.applications.insert(key, result.clone());
        }
        Ok(result)
    }
    fn steps_core(
        &mut self,
        term: &Thunk,
        unfold: bool,
        visited: &mut Vec<(usize, Vec<Thunk>)>,
    ) -> Result<Value> {
        let mut current = Closure {
            expr: term.expr.clone(),
            context: term.context.clone(),
        };
        let mut pending: Vec<Thunk> = Vec::new();
        loop {
            self.tc.tick()?;
            match &*current.expr {
                Expr::App(f, a) => {
                    pending.push(self.term_at(a.clone(), current.context.clone(), 0));
                    current.expr = f.clone();
                    continue;
                }
                Expr::Lam(domain, b) if !pending.is_empty() => {
                    let mut arg = pending.pop().unwrap();
                    let domain = self.term_at(domain.clone(), current.context.clone(), 0);
                    if self.proposition(&domain) {
                        arg = self.proofs.entry(domain.id).or_insert(arg).clone();
                    }
                    let frame = self.frame(arg, current.context.clone());
                    current = Closure {
                        expr: b.body().clone(),
                        context: Some(frame),
                    };
                    continue;
                }
                Expr::Let(_, v, b) => {
                    let value = self.term_at(v.clone(), current.context.clone(), 0);
                    let frame = self.frame(value, current.context.clone());
                    current = Closure {
                        expr: b.body().clone(),
                        context: Some(frame),
                    };
                    continue;
                }
                Expr::Var(n) => {
                    let mut resolved = None;
                    if let Some((mut depth, 0)) = n.coordinates() {
                        let mut frame = current.context.clone();
                        while let Some(f) = frame {
                            if depth == 0 {
                                resolved = Some(f.value.clone());
                                break;
                            }
                            depth -= 1;
                            frame = f.parent.clone();
                        }
                    } else if let Some(v) = self.tc.definitions.get(n) {
                        resolved = Some(self.term(v.clone(), None));
                    }
                    if let Some(value) = resolved {
                        let v = self.eval(&value, unfold)?;
                        pending.extend(v.args.iter().rev().cloned());
                        current = Closure {
                            expr: Shared::new(v.head),
                            context: v.context,
                        };
                        continue;
                    }
                }
                Expr::Proj(name, index, source) => {
                    let source = self.term_at(source.clone(), current.context.clone(), 0);
                    let value = self.eval(&source, true)?;
                    if let Expr::Const(c, _) = &value.head
                        && let Some(info) = self.tc.env.constructors.get(c)
                        && info.inductive == *name
                        && *index < info.num_fields
                        && value.args.len() == info.num_params + info.num_fields
                    {
                        let next = value.args[info.num_params + index].clone();
                        current = Closure {
                            expr: next.expr.clone(),
                            context: next.context.clone(),
                        };
                        continue;
                    }
                    // String representations and neutral projections use the same checked fallback.
                    let source = self.quote_value(&value);
                    let source = if let Expr::Str(s) = source {
                        let e = self.tc.string_constructor(&s)?;
                        self.tc.whnf(&e)?
                    } else {
                        source
                    };
                    let (head, args) = inductive::spine(&source);
                    if let Expr::Const(c, _) = head
                        && let Some(info) = self.tc.env.constructors.get(&c)
                        && info.inductive == *name
                        && *index < info.num_fields
                        && args.len() == info.num_params + info.num_fields
                    {
                        current = Closure::closed(args[info.num_params + index].clone());
                        continue;
                    }
                    let head = Expr::Proj(name.clone(), *index, Shared::new(source));
                    return Ok(Value {
                        head,
                        context: None,
                        args: pending.into_iter().rev().collect(),
                    });
                }
                Expr::Const(name, levels) => {
                    let head_id = self.tc.cache.shared(&current.expr);
                    let key = (
                        head_id,
                        pending
                            .iter()
                            .map(|a| a.canonical.get().copied().unwrap_or(a.id))
                            .collect(),
                        unfold,
                    );
                    if let Some(value) = self.applications.get(&key) {
                        return Ok(value.clone());
                    }
                    if let Some(value) = self.old_applications.get(&key).cloned() {
                        self.applications.insert(key, value.clone());
                        return Ok(value);
                    }
                    if visited.len() < 256 {
                        visited.push((head_id, pending.clone()));
                    }
                    let instance = if let Some(instance) = self.instances.get(&head_id) {
                        instance.clone()
                    } else {
                        let declaration = self.tc.decl(name)?;
                        let substitution = self.tc.level_arguments(&declaration.params, levels)?;
                        let instance = Rc::new(Instance {
                            declaration,
                            substitution,
                        });
                        self.instances.insert(head_id, instance.clone());
                        instance
                    };
                    let d = &instance.declaration;
                    let subst = &instance.substitution;
                    let arity = primitive_arity(name);
                    if levels.is_empty() && arity == Some(pending.len()) {
                        let mut args = Vec::new();
                        for arg in pending.iter().rev() {
                            let v = self.eval(arg, true)?;
                            let e = if let Expr::Const(n, us) = &v.head
                                && *n == self.tc.builtin_name("Nat.zero")
                                && us.is_empty()
                                && v.args.is_empty()
                            {
                                Expr::nat(0u32)
                            } else if matches!(v.head, Expr::Nat(_)) && v.args.is_empty() {
                                v.head
                            } else {
                                break;
                            };
                            args.push(e);
                        }
                        if args.len() == pending.len()
                            && let Some(value) = self.tc.reduce_primitive(&current.expr, &args)?
                        {
                            current = Closure::closed(value);
                            pending.clear();
                            continue;
                        }
                    }
                    if unfold && let Some(value) = &d.value {
                        let body = if let Some(body) = self.bodies.get(&head_id) {
                            body.clone()
                        } else {
                            let body = Shared::new(self.tc.substitute_levels(value, subst)?);
                            self.bodies.insert(head_id, body.clone());
                            body
                        };
                        current = Closure {
                            expr: body,
                            context: None,
                        };
                        continue;
                    }
                    if let Some(rec) = self.tc.env.recursors.get(name).cloned() {
                        let major_pos =
                            rec.num_params + rec.num_motives + rec.num_minors + rec.num_indices;
                        if pending.len() > major_pos {
                            let major = pending[pending.len() - 1 - major_pos].clone();
                            let mut value = self.eval(&major, true)?;
                            let reduced_key = (
                                head_id,
                                pending
                                    .iter()
                                    .map(|a| a.canonical.get().copied().unwrap_or(a.id))
                                    .collect(),
                                unfold,
                            );
                            if let Some(cached) = self
                                .applications
                                .get(&reduced_key)
                                .or_else(|| self.old_applications.get(&reduced_key))
                            {
                                return Ok(cached.clone());
                            }
                            if let Expr::Nat(n) = &value.head {
                                let ctor = self.tc.nat_constructor(&n.0);
                                let (head, args) = inductive::spine(&ctor);
                                value = Value {
                                    head,
                                    context: None,
                                    args: args.into_iter().map(|e| self.term(e, None)).collect(),
                                };
                            } else if let Expr::Str(s) = &value.head {
                                let e = self.tc.string_constructor(s)?;
                                let t = self.term(e, None);
                                value = self.eval(&t, true)?;
                            }
                            if let Expr::Const(c, _) = &value.head
                                && let Some((rule_index, rule)) = rec
                                    .rules
                                    .iter()
                                    .enumerate()
                                    .find(|(_, r)| r.constructor == *c)
                                && let Some(ctor) = self.tc.env.constructors.get(c)
                                && value.args.len() == ctor.num_params + rule.num_fields
                            {
                                let prefix = rec.num_params + rec.num_motives + rec.num_minors;
                                let mut args = pending
                                    .iter()
                                    .rev()
                                    .take(prefix)
                                    .cloned()
                                    .collect::<Vec<_>>();
                                args.extend(value.args.iter().skip(ctor.num_params).cloned());
                                args.extend(pending.iter().rev().skip(major_pos + 1).cloned());
                                let key = (head_id, rule_index);
                                let rhs = if let Some(rhs) = self.rules.get(&key) {
                                    rhs.clone()
                                } else {
                                    let rhs =
                                        Shared::new(self.tc.substitute_levels(&rule.rhs, subst)?);
                                    self.rules.insert(key, rhs.clone());
                                    rhs
                                };
                                current = Closure {
                                    expr: rhs,
                                    context: None,
                                };
                                pending = args.into_iter().rev().collect();
                                continue;
                            }
                            let args = pending
                                .iter()
                                .rev()
                                .map(|a| self.quote(a, 0))
                                .collect::<Vec<_>>();
                            if let Some(e) = self.tc.reduce_recursor(&current.expr, &args)? {
                                current = Closure::closed(e);
                                pending.clear();
                                continue;
                            }
                        }
                    }
                    if self.tc.env.quotients.contains(name) {
                        let info = if *name == self.tc.builtin_name("Quot.lift") {
                            Some((5, 3))
                        } else if *name == self.tc.builtin_name("Quot.ind") {
                            Some((4, 3))
                        } else {
                            None
                        };
                        if let Some((major, function)) = info
                            && pending.len() > major
                        {
                            let value = self.eval(&pending[pending.len() - 1 - major], true)?;
                            if matches!(&value.head, Expr::Const(n, _) if *n == self.tc.builtin_name("Quot.mk"))
                                && value.args.len() == 3
                            {
                                let next = pending[pending.len() - 1 - function].clone();
                                current = Closure {
                                    expr: next.expr.clone(),
                                    context: next.context.clone(),
                                };
                                pending.truncate(pending.len() - 1 - major);
                                pending.push(value.args[2].clone());
                                continue;
                            }
                        }
                    }
                }
                _ => {}
            }
            return Ok(Value {
                head: (*current.expr).clone(),
                context: current.context.clone(),
                args: pending.into_iter().rev().collect(),
            });
        }
    }
    fn quote_value(&mut self, value: &Value) -> Expr {
        let head = self.term(value.head.clone(), value.context.clone());
        let mut result = self.quote(&head, 0);
        for arg in &value.args {
            result = result.app(self.quote(arg, 0));
        }
        result
    }
    fn quote(&mut self, term: &Thunk, depth: usize) -> Expr {
        if term.context.is_none() {
            return (*term.expr).clone();
        }
        let key = (term.id, depth);
        if let Some(e) = self.quoted.get(&key) {
            return e.clone();
        }
        let result = match &*term.expr {
            Expr::Var(n) => {
                if let Some((d, slot)) = n.coordinates() {
                    if d < depth {
                        (*term.expr).clone()
                    } else {
                        let mut rest = d - depth;
                        let mut frame = term.context.clone();
                        loop {
                            match frame {
                                Some(f) if rest == 0 && slot == 0 => break self.quote(&f.value, 0),
                                Some(f) => {
                                    rest = rest.saturating_sub(1);
                                    frame = f.parent.clone();
                                }
                                None => break Expr::Var(Name::bound(depth + rest, slot)),
                            }
                        }
                    }
                } else {
                    (*term.expr).clone()
                }
            }
            Expr::App(f, a) => {
                let f = self.term_at(f.clone(), term.context.clone(), depth);
                let a = self.term_at(a.clone(), term.context.clone(), depth);
                self.quote(&f, depth).app(self.quote(&a, depth))
            }
            Expr::Proj(n, i, e) => {
                let e = self.term_at(e.clone(), term.context.clone(), depth);
                Expr::Proj(n.clone(), *i, Shared::new(self.quote(&e, depth)))
            }
            Expr::Pi(t, b) | Expr::Lam(t, b) => {
                let t = self.term_at(t.clone(), term.context.clone(), depth);
                let body = self.term_at(b.body().clone(), term.context.clone(), depth + 1);
                let t = Shared::new(self.quote(&t, depth));
                let b = bind(
                    b.pattern().clone(),
                    Shared::new(self.quote(&body, depth + 1)),
                );
                if matches!(*term.expr, Expr::Pi(..)) {
                    Expr::Pi(t, b)
                } else {
                    Expr::Lam(t, b)
                }
            }
            Expr::Let(t, v, b) => {
                let t = self.term_at(t.clone(), term.context.clone(), depth);
                let v = self.term_at(v.clone(), term.context.clone(), depth);
                let body = self.term_at(b.body().clone(), term.context.clone(), depth + 1);
                Expr::Let(
                    Shared::new(self.quote(&t, depth)),
                    Shared::new(self.quote(&v, depth)),
                    bind(
                        b.pattern().clone(),
                        Shared::new(self.quote(&body, depth + 1)),
                    ),
                )
            }
            _ => (*term.expr).clone(),
        };
        self.quoted.insert(key, result.clone());
        result
    }
}

fn primitive_arity(name: &str) -> Option<usize> {
    let name = name.strip_prefix("Nat.").or_else(|| {
        name.strip_prefix("[\"Nat\",\"")
            .and_then(|n| n.strip_suffix("\"]"))
    })?;
    match name {
        "succ" => Some(1),
        "add" | "sub" | "mul" | "pow" | "div" | "mod" | "gcd" | "beq" | "ble" | "land" | "lor"
        | "xor" | "shiftLeft" | "shiftRight" => Some(2),
        _ => None,
    }
}
