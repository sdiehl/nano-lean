use super::*;

/// Structural keys ignore binder hints, but retain every bound-variable index.
#[derive(PartialEq, Eq, Hash)]
enum Key {
    Nat(crate::syntax::Natural),
    Str(String),
    Var(Name<Expr>),
    Sort(Level),
    Const(String, Vec<Level>),
    App(usize, usize),
    Proj(String, usize, usize),
    Pi(usize, usize),
    Lam(usize, usize),
    Let(usize, usize, usize),
}

#[derive(Default)]
pub(super) struct Cache {
    nodes: HashMap<Key, usize>,
    pointers: HashMap<usize, (Shared<Expr>, usize)>,
    open: Vec<bool>,
    loose: Vec<Option<usize>>,
    bound: Vec<Vec<u64>>,
    wide: Vec<bool>,
    contexts: HashMap<Vec<usize>, usize>,
    opened: HashMap<(usize, usize, usize), Expr>,
    pub universes: HashMap<(usize, Vec<(String, Level)>), Expr>,
    pub inferred: HashMap<(usize, usize, bool), Expr>,
    pub reduced: HashMap<(usize, usize, bool), Expr>,
    pub equal: HashMap<(usize, usize, usize), bool>,
}

impl Cache {
    pub fn shared(&mut self, e: &Shared<Expr>) -> usize {
        let ptr = e.as_ptr() as usize;
        if let Some((_, id)) = self.pointers.get(&ptr) {
            return *id;
        }
        let id = self.id(e);
        self.pointers.insert(ptr, (e.clone(), id));
        id
    }

    pub fn id(&mut self, e: &Expr) -> usize {
        let key = match e {
            Expr::Nat(n) => Key::Nat(n.clone()),
            Expr::Str(s) => Key::Str(s.clone()),
            Expr::Var(n) => Key::Var(n.clone()),
            Expr::Sort(u) => Key::Sort(u.clone()),
            Expr::Const(n, us) => Key::Const(n.clone(), us.clone()),
            Expr::App(f, a) => Key::App(self.shared(f), self.shared(a)),
            Expr::Proj(n, i, e) => Key::Proj(n.clone(), *i, self.shared(e)),
            Expr::Pi(t, b) => Key::Pi(self.shared(t), self.shared(b.body())),
            Expr::Lam(t, b) => Key::Lam(self.shared(t), self.shared(b.body())),
            Expr::Let(t, v, b) => Key::Let(self.shared(t), self.shared(v), self.shared(b.body())),
        };
        if let Some(id) = self.nodes.get(&key) {
            return *id;
        }
        let open = match &key {
            Key::Var(n) => n.is_free(),
            Key::App(a, b) | Key::Pi(a, b) | Key::Lam(a, b) => self.open[*a] || self.open[*b],
            Key::Proj(_, _, e) => self.open[*e],
            Key::Let(a, b, c) => self.open[*a] || self.open[*b] || self.open[*c],
            _ => false,
        };
        let loose = match &key {
            Key::Var(n) => n.coordinates().map(|(depth, _)| depth),
            Key::App(a, b) => self.loose[*a].max(self.loose[*b]),
            Key::Pi(a, b) | Key::Lam(a, b) => {
                self.loose[*a].max(self.loose[*b].and_then(|n| n.checked_sub(1)))
            }
            Key::Proj(_, _, e) => self.loose[*e],
            Key::Let(a, b, c) => self.loose[*a]
                .max(self.loose[*b])
                .max(self.loose[*c].and_then(|n| n.checked_sub(1))),
            _ => None,
        };
        let mut bound = Vec::new();
        let mut merge = |bits: &[u64], under: bool| {
            bound.resize(bound.len().max(bits.len()), 0);
            for (i, word) in bits.iter().enumerate() {
                if under {
                    bound[i] |= word >> 1;
                    if i > 0 {
                        bound[i - 1] |= word << 63;
                    }
                } else {
                    bound[i] |= word;
                }
            }
        };
        match &key {
            Key::Var(n) => {
                if let Some((d, _)) = n.coordinates()
                    && d < 4096
                {
                    bound.resize(d / 64 + 1, 0);
                    bound[d / 64] |= 1 << (d % 64);
                }
            }
            Key::App(a, b) => {
                merge(&self.bound[*a], false);
                merge(&self.bound[*b], false);
            }
            Key::Pi(a, b) | Key::Lam(a, b) => {
                merge(&self.bound[*a], false);
                merge(&self.bound[*b], true);
            }
            Key::Proj(_, _, a) => merge(&self.bound[*a], false),
            Key::Let(a, b, c) => {
                merge(&self.bound[*a], false);
                merge(&self.bound[*b], false);
                merge(&self.bound[*c], true);
            }
            _ => {}
        }
        while bound.last() == Some(&0) {
            bound.pop();
        }
        let wide = match &key {
            Key::Var(n) => n.coordinates().is_some_and(|(d, _)| d >= 4096),
            Key::App(a, b) | Key::Pi(a, b) | Key::Lam(a, b) => self.wide[*a] || self.wide[*b],
            Key::Let(a, b, c) => self.wide[*a] || self.wide[*b] || self.wide[*c],
            Key::Proj(_, _, a) => self.wide[*a],
            _ => false,
        };
        let id = self.open.len();
        self.wide.push(wide);
        self.bound.push(bound);
        self.loose.push(loose);
        self.open.push(open);
        self.nodes.insert(key, id);
        id
    }

    pub fn bound_support(&self, id: usize) -> Option<&[u64]> {
        if self.wide[id] {
            None
        } else {
            Some(&self.bound[id])
        }
    }
    pub fn has_loose_id(&self, id: usize) -> bool {
        self.loose[id].is_some()
    }
    pub fn has_loose(&mut self, e: &Expr) -> bool {
        let id = self.id(e);
        self.loose[id].is_some()
    }

    /// Open only the subterm needed by inference, preserving the surrounding DAG.
    pub fn open_at(
        &mut self,
        e: &Expr,
        context: &[Name<Expr>],
        depth: usize,
        scope: usize,
    ) -> Expr {
        let id = self.id(e);
        if context.is_empty() || self.loose[id].is_none_or(|n| n < depth) {
            return e.clone();
        }
        let key = (id, depth, scope);
        if let Some(value) = self.opened.get(&key) {
            return value.clone();
        }
        let value = match e {
            Expr::Var(n) => match n.coordinates() {
                Some((d, 0)) if d >= depth && d - depth < context.len() => {
                    Expr::Var(context[context.len() - 1 - (d - depth)].clone())
                }
                _ => e.clone(),
            },
            Expr::App(f, a) => self
                .open_at(f, context, depth, scope)
                .app(self.open_at(a, context, depth, scope)),
            Expr::Proj(n, i, e) => Expr::Proj(
                n.clone(),
                *i,
                Shared::new(self.open_at(e, context, depth, scope)),
            ),
            Expr::Pi(t, b) | Expr::Lam(t, b) => {
                let t = Shared::new(self.open_at(t, context, depth, scope));
                let b = bind(
                    b.pattern().clone(),
                    Shared::new(self.open_at(b.body(), context, depth + 1, scope)),
                );
                if matches!(e, Expr::Pi(..)) {
                    Expr::Pi(t, b)
                } else {
                    Expr::Lam(t, b)
                }
            }
            Expr::Let(t, v, b) => Expr::Let(
                Shared::new(self.open_at(t, context, depth, scope)),
                Shared::new(self.open_at(v, context, depth, scope)),
                bind(
                    b.pattern().clone(),
                    Shared::new(self.open_at(b.body(), context, depth + 1, scope)),
                ),
            ),
            _ => e.clone(),
        };
        self.opened.insert(key, value.clone());
        value
    }

    pub fn context_key(&mut self, id: usize, context: &[Name<Expr>], scope: usize) -> usize {
        let mut names = Vec::new();
        for (i, word) in self.bound[id].iter().enumerate() {
            let mut bits = *word;
            while bits != 0 {
                let d = i * 64 + bits.trailing_zeros() as usize;
                names.push(
                    context
                        .len()
                        .checked_sub(d + 1)
                        .and_then(|j| context[j].index())
                        .unwrap_or(usize::MAX),
                );
                bits &= bits - 1;
            }
        }
        if self.wide[id] && self.loose[id].is_some() {
            names.extend([usize::MAX, scope]);
        }
        let next = self.contexts.len();
        *self.contexts.entry(names).or_insert(next)
    }

    pub fn scope(&self, id: usize, scope: usize) -> usize {
        // Free names are globally fresh and have immutable types/values within a checker.
        // Extending a context therefore cannot change an already inferred open term.
        if self.loose[id].is_some() { scope } else { 0 }
    }
}
