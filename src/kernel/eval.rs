use super::*;
use std::{cell::OnceCell, rc::Rc};
mod check;

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
    value: Option<Thunk>,
    parent: Option<Rc<Frame>>,
}
// Closures form deep acyclic graphs. Release uniquely owned edges iteratively
// so evaluator cleanup does not consume one stack frame per suspended call.
enum Edge {
    Term(Thunk),
    Frame(Rc<Frame>),
}
impl Term {
    fn detach(&mut self, pending: &mut Vec<Edge>) {
        pending.extend(self.context.take().map(Edge::Frame));
        for normal in &mut self.normal {
            if let Some(value) = normal.take() {
                pending.extend(value.context.map(Edge::Frame));
                pending.extend(value.args.into_iter().map(Edge::Term));
            }
        }
    }
}
impl Frame {
    fn value(&self) -> &Thunk {
        self.value.as_ref().expect("live frame has a value")
    }
    fn detach(&mut self, pending: &mut Vec<Edge>) {
        pending.extend(self.value.take().map(Edge::Term));
        pending.extend(self.parent.take().map(Edge::Frame));
    }
}
fn release(mut pending: Vec<Edge>) {
    while let Some(edge) = pending.pop() {
        match edge {
            Edge::Term(term) => {
                if let Ok(mut term) = Rc::try_unwrap(term) {
                    term.detach(&mut pending);
                }
            }
            Edge::Frame(frame) => {
                if let Ok(mut frame) = Rc::try_unwrap(frame) {
                    frame.detach(&mut pending);
                }
            }
        }
    }
}
impl Drop for Term {
    fn drop(&mut self) {
        let mut pending = Vec::new();
        self.detach(&mut pending);
        release(pending);
    }
}
impl Drop for Frame {
    fn drop(&mut self) {
        let mut pending = Vec::new();
        self.detach(&mut pending);
        release(pending);
    }
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
    state: State,
    variables: Vec<(Name<Expr>, Thunk)>,
    synced_variables: usize,
    initial_locals: usize,
    initial_scope: usize,
    reuse_proofs: bool,
}
pub(super) struct State {
    // Proof reuse can select a local hypothesis even for a closed proposition.
    // Reuse is therefore limited to requests with no local hypotheses or let
    // definitions, within the same Checker. Otherwise a local proof could escape
    // through the syntax cache even before the local scope changes.
    scope: usize,
    instances: HashMap<usize, Rc<Instance>>,
    bodies: HashMap<usize, Shared<Expr>>,
    rules: HashMap<(usize, usize), Shared<Expr>>,
    next_term: usize,
    next_frame: usize,
    nodes: HashMap<(usize, Vec<usize>), Thunk>,
    old_nodes: HashMap<(usize, Vec<usize>), Thunk>,
    closed: HashMap<usize, Thunk>,
    proofs: HashMap<usize, Thunk>,
    active: rustc_hash::FxHashSet<usize>,
    proposition_heads: HashMap<String, Option<usize>>,
    quoted: HashMap<(usize, usize), Expr>,
    applications: HashMap<(usize, Vec<usize>, bool), Value>,
    old_applications: HashMap<(usize, Vec<usize>, bool), Value>,
}

impl Default for State {
    fn default() -> Self {
        Self {
            scope: 0,
            instances: HashMap::default(),
            bodies: HashMap::default(),
            rules: HashMap::default(),
            next_term: 0,
            next_frame: 1,
            nodes: HashMap::default(),
            old_nodes: HashMap::default(),
            closed: HashMap::default(),
            proofs: HashMap::default(),
            active: rustc_hash::FxHashSet::default(),
            proposition_heads: HashMap::default(),
            quoted: HashMap::default(),
            applications: HashMap::default(),
            old_applications: HashMap::default(),
        }
    }
}

impl Drop for Evaluator<'_, '_> {
    fn drop(&mut self) {
        self.tc.locals.truncate(self.initial_locals);
        self.tc.scope = self.initial_scope;
        // Retain small semantic graphs across WHNF requests in one declaration.
        // Large reductions are released at the request boundary.
        if self.variables.is_empty()
            && self.tc.locals.is_empty()
            && self.tc.definitions.is_empty()
            && self.state.next_term < 8192
            && self.state.next_frame < 16384
            && self.state.applications.len() + self.state.old_applications.len() < 8192
            && self.state.quoted.len() < 8192
        {
            self.tc.evaluation = std::mem::take(&mut self.state);
        }
    }
}

impl<'a> Checker<'a> {
    pub(super) fn whnf_core(&mut self, expr: &Expr, unfold: bool) -> Result<Expr> {
        #[cfg(feature = "profile")]
        let _whnf = crate::profile::span("whnf");
        let mut evaluator = Evaluator::new(self);
        let root = evaluator.term(expr.clone(), None);
        let value = evaluator.eval(&root, unfold)?;
        Ok(evaluator.quote_value(&value))
    }
}

impl<'b, 'a> Evaluator<'b, 'a> {
    fn new(tc: &'b mut Checker<'a>) -> Self {
        #[cfg(feature = "profile")]
        crate::profile::count("evaluators");
        let mut state = std::mem::take(&mut tc.evaluation);
        if state.scope != tc.scope || !tc.locals.is_empty() || !tc.definitions.is_empty() {
            state = State::default();
        }
        state.scope = tc.scope;
        #[cfg(feature = "profile")]
        if state.next_term == 0 {
            crate::profile::count("evaluation_sessions");
        }
        let initial_locals = tc.locals.len();
        let initial_scope = tc.scope;
        let reuse_proofs = tc.semantic;
        Self {
            tc,
            state,
            variables: Vec::new(),
            synced_variables: 0,
            initial_locals,
            initial_scope,
            reuse_proofs,
        }
    }
    // Register typed semantic variables only at a legacy reduction boundary.
    // Inference and conversion otherwise keep binder domains in closures.
    fn sync_variables(&mut self) {
        while self.synced_variables < self.variables.len() {
            let (name, ty) = self.variables[self.synced_variables].clone();
            let ty = self.quote(&ty, 0);
            self.tc.locals.push((name, ty));
            self.tc.scope = self.tc.next_scope;
            self.tc.next_scope += 1;
            self.synced_variables += 1;
        }
    }
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
                    return f.value().clone();
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
        } else if let Some(bits) = self.tc.cache.bound_support(id)
            && bits.iter().map(|w| w.count_ones() as usize).sum::<usize>() <= 64
        {
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
                        f.value().canonical.get().copied().unwrap_or(f.value().id)
                    }));
                    word &= word - 1;
                }
            }
        } else {
            // Wide lexical environments use their persistent frame identity.
            // Copying every captured ID into every subterm's key makes deeply
            // nested binders retain a quadratic amount of key storage.
            dependencies.extend([usize::MAX, context.as_ref().map_or(0, |f| f.id)]);
        }
        if context.is_none()
            && let Some(t) = self.state.closed.get(&id)
        {
            return t.clone();
        }
        let key = (id, dependencies);
        if let Some(t) = self.state.nodes.get(&key) {
            return t.clone();
        }
        if let Some(t) = self.state.old_nodes.get(&key).cloned() {
            self.state.nodes.insert(key, t.clone());
            return t;
        }
        if self.state.nodes.len() >= 262_144 {
            self.state.old_nodes = std::mem::take(&mut self.state.nodes);
        }
        let value = Rc::new(Term {
            id: self.state.next_term,
            expr,
            context,
            normal: [OnceCell::new(), OnceCell::new()],
            canonical: OnceCell::new(),
        });
        #[cfg(feature = "profile")]
        crate::profile::count("terms");
        self.state.next_term += 1;
        if value.context.is_none() {
            self.state.closed.insert(id, value.clone());
        }
        self.state.nodes.insert(key, value.clone());
        value
    }
    fn frame(&mut self, value: Thunk, parent: Option<Rc<Frame>>) -> Rc<Frame> {
        #[cfg(feature = "profile")]
        crate::profile::count("frames");
        let f = Rc::new(Frame {
            id: self.state.next_frame,
            value: Some(value),
            parent,
        });
        self.state.next_frame += 1;
        f
    }
    fn apply(&mut self, function: &Thunk, argument: &Thunk) -> Thunk {
        let function = self.frame(function.clone(), None);
        let context = self.frame(argument.clone(), Some(function));
        self.term(
            Expr::Var(Name::bound(1, 0)).app(Expr::Var(Name::bound(0, 0))),
            Some(context),
        )
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
        if let Some(expected) = self.state.proposition_heads.get(name) {
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
        self.state.proposition_heads.insert(name.clone(), expected);
        expected == Some(arity)
    }
    fn eval(&mut self, term: &Thunk, unfold: bool) -> Result<Value> {
        if let Some(value) = term.normal[usize::from(unfold)].get() {
            return Ok(value.clone());
        }
        let newly_active = self.state.active.insert(term.id);
        let result = stacker::maybe_grow(256 * 1024, 16 * 1024 * 1024, || self.steps(term, unfold));
        if newly_active {
            self.state.active.remove(&term.id);
        }
        let result = result?;
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
            if self.state.applications.len() >= 524_288 {
                self.state.old_applications = std::mem::take(&mut self.state.applications);
            }
            self.state.applications.insert(key, result.clone());
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
                    if self.reuse_proofs && self.proposition(&domain) {
                        let canonical = self
                            .state
                            .proofs
                            .entry(domain.id)
                            .or_insert_with(|| arg.clone());
                        // Reusing a proof currently being evaluated would make
                        // its body refer back to itself and prevent reduction.
                        if !self.state.active.contains(&canonical.id) {
                            arg = canonical.clone();
                        }
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
                                resolved = Some(f.value().clone());
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
                    if let Some(value) = self.state.applications.get(&key) {
                        return Ok(value.clone());
                    }
                    if let Some(value) = self.state.old_applications.get(&key).cloned() {
                        self.state.applications.insert(key, value.clone());
                        return Ok(value);
                    }
                    if visited.len() < 256 {
                        visited.push((head_id, pending.clone()));
                    }
                    let instance = if let Some(instance) = self.state.instances.get(&head_id) {
                        instance.clone()
                    } else {
                        let declaration = self.tc.decl(name)?;
                        let substitution = self.tc.level_arguments(&declaration.params, levels)?;
                        let instance = Rc::new(Instance {
                            declaration,
                            substitution,
                        });
                        self.state.instances.insert(head_id, instance.clone());
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
                        let body = if let Some(body) = self.state.bodies.get(&head_id) {
                            body.clone()
                        } else {
                            let body = Shared::new(self.tc.substitute_levels(value, subst)?);
                            self.state.bodies.insert(head_id, body.clone());
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
                        // Empty eliminators have no computation rule; forcing
                        // their impossible proof argument cannot reduce them.
                        if pending.len() > major_pos && !rec.rules.is_empty() {
                            if rec.k {
                                self.sync_variables();
                                let args = pending
                                    .iter()
                                    .rev()
                                    .map(|a| self.quote(a, 0))
                                    .collect::<Vec<_>>();
                                if let Some(e) =
                                    self.tc.reduce_neutral_recursor(&current.expr, &args)?
                                {
                                    current = Closure::closed(e);
                                    pending.clear();
                                    continue;
                                }
                            }
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
                                .state
                                .applications
                                .get(&reduced_key)
                                .or_else(|| self.state.old_applications.get(&reduced_key))
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
                                let rhs = if let Some(rhs) = self.state.rules.get(&key) {
                                    rhs.clone()
                                } else {
                                    let rhs =
                                        Shared::new(self.tc.substitute_levels(&rule.rhs, subst)?);
                                    self.state.rules.insert(key, rhs.clone());
                                    rhs
                                };
                                current = Closure {
                                    expr: rhs,
                                    context: None,
                                };
                                pending = args.into_iter().rev().collect();
                                continue;
                            }
                            self.sync_variables();
                            let args = pending
                                .iter()
                                .rev()
                                .map(|a| self.quote(a, 0))
                                .collect::<Vec<_>>();
                            if let Some(e) =
                                self.tc.reduce_neutral_recursor(&current.expr, &args)?
                            {
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
        #[cfg(feature = "profile")]
        let _quote = crate::profile::span("quote");
        enum Work {
            Visit(Thunk, usize),
            Finish(Thunk, usize),
        }
        let mut work = vec![Work::Visit(term.clone(), depth)];
        let mut values: Vec<Expr> = Vec::new();
        while let Some(next) = work.pop() {
            match next {
                Work::Visit(term, depth) => {
                    #[cfg(feature = "profile")]
                    crate::profile::count("quote_visits");
                    // Quoting a forced numeral's original suspended arithmetic
                    // can expand an enormous predecessor/successor history.
                    if let Some(value) = term.normal.iter().filter_map(OnceCell::get).find(|v| {
                        v.context.is_none()
                            && v.args.is_empty()
                            && matches!(v.head, Expr::Nat(_) | Expr::Str(_))
                    }) {
                        values.push(value.head.clone());
                        continue;
                    }
                    if term.context.is_none() {
                        values.push((*term.expr).clone());
                        continue;
                    }
                    if let Some(e) = self.state.quoted.get(&(term.id, depth)) {
                        values.push(e.clone());
                        continue;
                    }
                    let mut children = Vec::new();
                    let immediate = match &*term.expr {
                        Expr::Var(n) => {
                            if let Some((d, slot)) = n.coordinates().filter(|&(d, _)| d >= depth) {
                                let mut rest = d - depth;
                                let mut frame = term.context.clone();
                                loop {
                                    match frame {
                                        Some(f) if rest == 0 && slot == 0 => {
                                            children.push((f.value().clone(), 0));
                                            break None;
                                        }
                                        Some(f) => {
                                            rest = rest.saturating_sub(1);
                                            frame = f.parent.clone();
                                        }
                                        None => {
                                            break Some(Expr::Var(Name::bound(depth + rest, slot)));
                                        }
                                    }
                                }
                            } else {
                                Some((*term.expr).clone())
                            }
                        }
                        Expr::App(f, a) => {
                            children.push((
                                self.term_at(f.clone(), term.context.clone(), depth),
                                depth,
                            ));
                            children.push((
                                self.term_at(a.clone(), term.context.clone(), depth),
                                depth,
                            ));
                            None
                        }
                        Expr::Proj(_, _, e) => {
                            children.push((
                                self.term_at(e.clone(), term.context.clone(), depth),
                                depth,
                            ));
                            None
                        }
                        Expr::Pi(t, b) | Expr::Lam(t, b) => {
                            children.push((
                                self.term_at(t.clone(), term.context.clone(), depth),
                                depth,
                            ));
                            children.push((
                                self.term_at(b.body().clone(), term.context.clone(), depth + 1),
                                depth + 1,
                            ));
                            None
                        }
                        Expr::Let(t, v, b) => {
                            children.push((
                                self.term_at(t.clone(), term.context.clone(), depth),
                                depth,
                            ));
                            children.push((
                                self.term_at(v.clone(), term.context.clone(), depth),
                                depth,
                            ));
                            children.push((
                                self.term_at(b.body().clone(), term.context.clone(), depth + 1),
                                depth + 1,
                            ));
                            None
                        }
                        _ => Some((*term.expr).clone()),
                    };
                    if let Some(result) = immediate {
                        self.state.quoted.insert((term.id, depth), result.clone());
                        values.push(result);
                    } else {
                        work.push(Work::Finish(term, depth));
                        work.extend(
                            children
                                .into_iter()
                                .rev()
                                .map(|(term, depth)| Work::Visit(term, depth)),
                        );
                    }
                }
                Work::Finish(term, depth) => {
                    #[cfg(feature = "profile")]
                    crate::profile::count("quote_rebuilds");
                    let last = values.pop().expect("quoted child");
                    let result = match &*term.expr {
                        Expr::Var(_) => last,
                        Expr::App(_, _) => values.pop().expect("quoted function").app(last),
                        Expr::Proj(n, i, _) => Expr::Proj(n.clone(), *i, Shared::new(last)),
                        Expr::Pi(_, b) | Expr::Lam(_, b) => {
                            let ty = Shared::new(values.pop().expect("quoted domain"));
                            let body = bind(b.pattern().clone(), Shared::new(last));
                            if matches!(*term.expr, Expr::Pi(..)) {
                                Expr::Pi(ty, body)
                            } else {
                                Expr::Lam(ty, body)
                            }
                        }
                        Expr::Let(_, _, b) => {
                            let value = Shared::new(values.pop().expect("quoted value"));
                            let ty = Shared::new(values.pop().expect("quoted type"));
                            Expr::Let(ty, value, bind(b.pattern().clone(), Shared::new(last)))
                        }
                        _ => unreachable!("only compound terms schedule children"),
                    };
                    self.state.quoted.insert((term.id, depth), result.clone());
                    values.push(result);
                }
            }
        }
        values.pop().expect("quoted root")
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reused_evaluation_does_not_export_local_proofs() {
        let mut env = Environment::new();
        crate::parser::run("axiom P : Prop; axiom p : P", &mut env).unwrap();
        let mut checker = Checker::new(&env);
        let p = Expr::constant("P");
        let x = Name::new("x");
        let identity = Expr::lam(x.clone(), p.clone(), Expr::Var(x));
        let closed = identity.clone().app(Expr::constant("p"));
        let h = Name::new("h");
        checker
            .local(h.clone(), p.clone(), |tc| {
                let first = identity.clone().app(Expr::Var(h.clone()));
                assert!(tc.whnf(&first)?.aeq(&Expr::Var(h)));
                // A previously used local proof must not be substituted into
                // this closed term and escape through the syntax WHNF cache.
                assert!(tc.whnf(&closed)?.aeq(&Expr::constant("p")));
                Ok(())
            })
            .unwrap();
        let result = checker.whnf(&closed).unwrap();
        assert!(checker.infer(&result).unwrap().aeq(&p));
    }

    #[test]
    fn reused_evaluation_preserves_unfolding_modes() {
        let mut env = Environment::new();
        crate::parser::run("axiom A : Type; axiom a : A; def d : A := a", &mut env).unwrap();
        let mut checker = Checker::new(&env);
        let d = Expr::constant("d");
        assert!(checker.whnf_mode(&d, false).unwrap().aeq(&d));
        assert!(checker.whnf(&d).unwrap().aeq(&Expr::constant("a")));
        assert!(checker.whnf_mode(&d, false).unwrap().aeq(&d));
    }

    #[test]
    fn quote_reuses_a_forced_numeric_result() {
        let env = Environment::new();
        let mut checker = Checker::new(&env);
        let mut evaluator = Evaluator::new(&mut checker);
        let predecessor = evaluator.term(Expr::nat(604_799_999u64), None);
        let frame = evaluator.frame(predecessor, None);
        let suspended = evaluator.term(
            Expr::Const("Nat.succ".into(), vec![]).app(Expr::Var(Name::bound(0, 0))),
            Some(frame),
        );
        assert!(
            suspended.normal[1]
                .set(Value {
                    head: Expr::nat(604_800_000u64),
                    context: None,
                    args: vec![],
                })
                .is_ok()
        );
        assert!(matches!(evaluator.quote(&suspended, 0),
            Expr::Nat(n) if n.0 == 604_800_000u64.into()));
    }

    #[test]
    fn quote_deep_closure_chain_uses_bounded_stack() {
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                let env = Environment::new();
                let mut checker = Checker::new(&env);
                let mut evaluator = Evaluator::new(&mut checker);
                let mut term = evaluator.term(Expr::Sort(Level::Nat(0)), None);
                let var = Shared::new(Expr::Var(Name::bound(0, 0)));
                for id in 1..100_000 {
                    term = Rc::new(Term {
                        id,
                        expr: var.clone(),
                        context: Some(Rc::new(Frame {
                            id,
                            value: Some(term),
                            parent: None,
                        })),
                        normal: [OnceCell::new(), OnceCell::new()],
                        canonical: OnceCell::new(),
                    });
                }
                assert!(matches!(
                    evaluator.quote(&term, 0),
                    Expr::Sort(Level::Nat(0))
                ));
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn deep_closure_graph_cleanup_uses_bounded_stack() {
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                let expr = Shared::new(Expr::Sort(Level::Nat(0)));
                let mut context = None;
                for id in 0..100_000 {
                    let term = Rc::new(Term {
                        id,
                        expr: expr.clone(),
                        context: context.clone(),
                        normal: [OnceCell::new(), OnceCell::new()],
                        canonical: OnceCell::new(),
                    });
                    context = Some(Rc::new(Frame {
                        id,
                        value: Some(term),
                        parent: context,
                    }));
                }
                drop(context);
            })
            .unwrap()
            .join()
            .unwrap();
    }
}
