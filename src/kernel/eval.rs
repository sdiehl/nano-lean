use super::inductive;
use super::prelude::*;
use rustc_hash::FxHashSet;
use std::{
    cell::OnceCell,
    rc::{Rc, Weak},
};
mod check;
mod quote;
mod reduce;
mod release;
mod relevance;
pub(super) use relevance::Summary;

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
struct Closure {
    expr: Shared<Expr>,
    context: Option<Rc<Frame>>,
}
impl Term {
    fn key(&self) -> usize {
        self.canonical.get().copied().unwrap_or(self.id)
    }
}
impl Closure {
    fn of(term: &Term) -> Self {
        Self {
            expr: term.expr.clone(),
            context: term.context.clone(),
        }
    }
    fn closed(expr: Expr) -> Self {
        Self {
            expr: Shared::new(expr),
            context: None,
        }
    }
}
type Value = Rc<ValueData>;
struct ValueData {
    id: usize,
    head: Expr,
    context: Option<Rc<Frame>>,
    args: Vec<Thunk>,
}

struct Instance {
    declaration: Rc<Declaration>,
    substitution: BTreeMap<String, Level>,
}
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
    // Only without locals, or a reused local proof could escape through the syntax cache.
    scope: usize,
    instances: HashMap<usize, Rc<Instance>>,
    bodies: HashMap<usize, Shared<Expr>>,
    rules: HashMap<(usize, usize), Shared<Expr>>,
    next_term: usize,
    next_frame: usize,
    next_value: usize,
    frames: HashMap<(usize, usize), Weak<Frame>>,
    values: HashMap<(usize, usize, Vec<usize>), Weak<ValueData>>,
    nodes: HashMap<(usize, Vec<usize>), Thunk>,
    old_nodes: HashMap<(usize, Vec<usize>), Thunk>,
    closed: HashMap<usize, Thunk>,
    proofs: HashMap<usize, Thunk>,
    active: FxHashSet<usize>,
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
            next_value: 0,
            frames: HashMap::default(),
            values: HashMap::default(),
            nodes: HashMap::default(),
            old_nodes: HashMap::default(),
            closed: HashMap::default(),
            proofs: HashMap::default(),
            active: FxHashSet::default(),
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
            let mut frame = context.as_deref();
            while let Some(f) = frame {
                if d == 0 {
                    return f.value().clone();
                }
                d -= 1;
                frame = f.parent.as_deref();
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
            let mut frame = context.as_deref();
            let mut depth = 0;
            for (i, word) in bits.iter().enumerate() {
                let mut word = *word;
                while word != 0 {
                    let d = i * 64 + word.trailing_zeros() as usize;
                    while depth < d {
                        frame = frame.and_then(|f| f.parent.as_deref());
                        depth += 1;
                    }
                    dependencies.push(frame.map_or(usize::MAX, |f| f.value().key()));
                    word &= word - 1;
                }
            }
        } else {
            // Frame identity avoids quadratic key storage under deep binders.
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
        // Deep extensions are usually unique, so hashing them costs more than it shares.
        let key = parent
            .as_ref()
            .is_none_or(|f| f.parent.is_none())
            .then(|| (value.id, parent.as_ref().map_or(0, |f| f.id)));
        if let Some(frame) = key
            .as_ref()
            .and_then(|k| self.state.frames.get(k))
            .and_then(Weak::upgrade)
        {
            #[cfg(feature = "profile")]
            crate::profile::count("frame_intern_hits");
            return frame;
        }
        #[cfg(feature = "profile")]
        crate::profile::count("frames");
        let f = Rc::new(Frame {
            id: self.state.next_frame,
            value: Some(value),
            parent,
        });
        self.state.next_frame += 1;
        if let Some(key) = key {
            if self.state.frames.len() >= 16_384 {
                self.state.frames.clear();
            }
            self.state.frames.insert(key, Rc::downgrade(&f));
        }
        f
    }
    fn value(&mut self, head: Expr, mut context: Option<Rc<Frame>>, args: Vec<Thunk>) -> Value {
        // Weak entries share live reductions without keeping dead graphs alive.
        let key = (args.len() <= 64).then(|| {
            let id = self.tc.cache.id(&head);
            if !self.tc.cache.has_loose_id(id) {
                context = None;
            }
            (
                id,
                context.as_ref().map_or(0, |f| f.id),
                args.iter().map(|a| a.id).collect(),
            )
        });
        if let Some(value) = key
            .as_ref()
            .and_then(|k| self.state.values.get(k))
            .and_then(Weak::upgrade)
        {
            #[cfg(feature = "profile")]
            crate::profile::count("value_intern_hits");
            return value;
        }
        let value = Rc::new(ValueData {
            id: self.state.next_value,
            head,
            context,
            args,
        });
        self.state.next_value += 1;
        if let Some(key) = key {
            if self.state.values.len() >= 16_384 {
                self.state.values.clear();
            }
            self.state.values.insert(key, Rc::downgrade(&value));
        }
        value
    }
    fn apply(&mut self, function: &Thunk, argument: &Thunk) -> Thunk {
        let function = self.frame(function.clone(), None);
        let context = self.frame(argument.clone(), Some(function));
        self.term(
            Expr::Var(Name::bound(1, 0)).app(Expr::Var(Name::bound(0, 0))),
            Some(context),
        )
    }
    // Sound by proof irrelevance for the identical instantiated proposition.
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
}

#[cfg(test)]
mod tests;
