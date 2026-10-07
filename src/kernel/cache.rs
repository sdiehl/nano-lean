use super::*;
use crate::syntax::Natural;

enum BoundSupport {
    Inline(u64),
    Wide(Box<[u64]>),
}

impl BoundSupport {
    fn as_slice(&self) -> &[u64] {
        match self {
            Self::Inline(0) => &[],
            Self::Inline(bits) => std::slice::from_ref(bits),
            Self::Wide(bits) => bits,
        }
    }

    fn include(&mut self, index: usize, word: u64) {
        if word == 0 {
            return;
        }
        match self {
            Self::Inline(bits) if index == 0 => *bits |= word,
            Self::Wide(bits) if index < bits.len() => bits[index] |= word,
            _ => {
                let mut bits = self.as_slice().to_vec();
                bits.resize(index + 1, 0);
                bits[index] |= word;
                *self = Self::Wide(bits.into_boxed_slice());
            }
        }
    }

    fn merge(&mut self, other: &Self, under_binder: bool) {
        for (i, &word) in other.as_slice().iter().enumerate() {
            if under_binder {
                self.include(i, word >> 1);
                if i > 0 {
                    self.include(i - 1, word << 63);
                }
            } else {
                self.include(i, word);
            }
        }
    }
}

#[derive(PartialEq, Eq, Hash)]
enum Key {
    Nat(Natural),
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
    bound: Vec<BoundSupport>,
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
        // Clearing drops addresses too, so allocator reuse cannot leave stale IDs.
        if self.pointers.len() >= 262_144 {
            self.pointers.clear();
        }
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
        let mut bound = BoundSupport::Inline(0);
        match &key {
            Key::Var(n) => {
                if let Some((d, _)) = n.coordinates()
                    && d < 4096
                {
                    bound.include(d / 64, 1 << (d % 64));
                }
            }
            Key::App(a, b) => {
                bound.merge(&self.bound[*a], false);
                bound.merge(&self.bound[*b], false);
            }
            Key::Pi(a, b) | Key::Lam(a, b) => {
                bound.merge(&self.bound[*a], false);
                bound.merge(&self.bound[*b], true);
            }
            Key::Proj(_, _, a) => bound.merge(&self.bound[*a], false),
            Key::Let(a, b, c) => {
                bound.merge(&self.bound[*a], false);
                bound.merge(&self.bound[*b], false);
                bound.merge(&self.bound[*c], true);
            }
            _ => {}
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
            Some(self.bound[id].as_slice())
        }
    }
    pub fn has_loose_id(&self, id: usize) -> bool {
        self.loose[id].is_some()
    }
    pub fn is_closed(&self, id: usize) -> bool {
        !self.open[id] && self.loose[id].is_none()
    }
    pub fn has_loose(&mut self, e: &Expr) -> bool {
        let id = self.id(e);
        self.loose[id].is_some()
    }

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
        for (i, word) in self.bound[id].as_slice().iter().enumerate() {
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
        // Free names are globally fresh, so extending a context cannot change an inferred term.
        if self.loose[id].is_some() { scope } else { 0 }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn support_shifts_across_word_boundaries_without_losing_variables() {
        let mut cache = Cache::default();
        for depth in [0, 1, 63, 64, 65, 127, 128, 4095, 4096] {
            let body = Expr::Var(Name::bound(depth, 0));
            let id = cache.id(&body);
            if depth < 4096 {
                let mut expected = vec![0; depth / 64 + 1];
                expected[depth / 64] = 1 << (depth % 64);
                assert_eq!(cache.bound_support(id), Some(expected.as_slice()));
            } else {
                assert!(cache.bound_support(id).is_none());
            }
            let lambda = Expr::Lam(
                Shared::new(Expr::Sort(Level::Nat(0))),
                bind(Name::new("x"), Shared::new(body)),
            );
            let id = cache.id(&lambda);
            if depth == 0 {
                assert_eq!(cache.bound_support(id), Some([].as_slice()));
                assert!(!cache.has_loose_id(id));
            } else if depth < 4096 {
                let mut expected = vec![0; (depth - 1) / 64 + 1];
                expected[(depth - 1) / 64] = 1 << ((depth - 1) % 64);
                assert_eq!(cache.bound_support(id), Some(expected.as_slice()));
                if depth <= 64 {
                    assert!(matches!(cache.bound[id], BoundSupport::Inline(_)));
                }
            } else {
                assert!(cache.bound_support(id).is_none());
            }
        }
    }

    #[test]
    fn support_union_preserves_inline_and_wide_captures() {
        let mut a = BoundSupport::Inline(1 | (1 << 63));
        let mut b = BoundSupport::Inline(0);
        b.include(1, 3);
        a.merge(&b, true);
        assert_eq!(a.as_slice(), &[1 | (1 << 63), 1]);
        let mut closed = BoundSupport::Inline(0);
        closed.merge(&BoundSupport::Inline(1), true);
        assert!(matches!(closed, BoundSupport::Inline(0)));
    }
}
