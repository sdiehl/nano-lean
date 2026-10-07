use super::*;

impl<'b, 'a> Evaluator<'b, 'a> {
    pub(super) fn quote_value(&mut self, value: &Value) -> Expr {
        let head = self.term(value.head.clone(), value.context.clone());
        let mut result = self.quote(&head, 0);
        for arg in &value.args {
            result = result.app(self.quote(arg, 0));
        }
        result
    }
    pub(super) fn quote(&mut self, term: &Thunk, depth: usize) -> Expr {
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
                    // Quoting the suspended arithmetic can expand an enormous successor chain.
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
