use super::{Closure, Evaluator, Instance, Thunk, Value, inductive};
use crate::kernel::prelude::*;
use crate::kernel::{primitive::NatOp, quotient::Eliminator};
use crate::term::names::{NAT_ZERO, QUOT_MK, QUOT_MK_ARITY};
use std::mem::take;

const VISITED_LIMIT: usize = 256;
const APPLICATION_LIMIT: usize = 524_288;

fn application_key(head: usize, args: &[Thunk], unfold: bool) -> (usize, Vec<usize>, bool) {
    (head, args.iter().map(|a| a.key()).collect(), unfold)
}

impl<'a> Checker<'a> {
    pub(in crate::kernel) fn whnf_core(&mut self, expr: &Expr, unfold: bool) -> Result<Expr> {
        #[cfg(feature = "profile")]
        let _whnf = crate::profile::span("whnf");
        let mut evaluator = Evaluator::new(self);
        let root = evaluator.term(expr.clone(), None);
        let value = evaluator.eval(&root, unfold)?;
        Ok(evaluator.quote_value(&value))
    }
}

impl<'b, 'a> Evaluator<'b, 'a> {
    pub(super) fn eval(&mut self, term: &Thunk, unfold: bool) -> Result<Value> {
        if let Some(value) = term.normal[usize::from(unfold)].get() {
            return Ok(value.clone());
        }
        let newly_active = self.state.active.insert(term.id);
        let result = grow(|| self.steps(term, unfold));
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
        term.normal[usize::from(unfold)].set(result.clone()).ok();
        Ok(result)
    }
    fn steps(&mut self, term: &Thunk, unfold: bool) -> Result<Value> {
        let mut visited = Vec::new();
        let result = self.steps_core(term, unfold, &mut visited)?;
        for (head, args) in visited {
            let key = application_key(head, &args, unfold);
            if self.state.applications.len() >= APPLICATION_LIMIT {
                self.state.old_applications = take(&mut self.state.applications);
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
        let mut current = Closure::of(term);
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
                    let mut arg = pending.pop().expect("guarded nonempty");
                    let domain = self.term_at(domain.clone(), current.context.clone(), 0);
                    if self.reuse_proofs && self.proposition(&domain) {
                        let canonical = self
                            .state
                            .proofs
                            .entry(domain.id)
                            .or_insert_with(|| arg.clone());
                        // An active proof would refer back to itself and block reduction.
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
                        let mut frame = current.context.as_deref();
                        while let Some(f) = frame {
                            if depth == 0 {
                                resolved = Some(f.value().clone());
                                break;
                            }
                            depth -= 1;
                            frame = f.parent.as_deref();
                        }
                    } else if let Some(v) = self.tc.definitions.get(n) {
                        resolved = Some(self.term(v.clone(), None));
                    }
                    if let Some(value) = resolved {
                        let v = self.eval(&value, unfold)?;
                        pending.extend(v.args.iter().rev().cloned());
                        current = Closure {
                            expr: Shared::new(v.head.clone()),
                            context: v.context.clone(),
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
                        current = Closure::of(&value.args[info.num_params + index]);
                        continue;
                    }
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
                    return Ok(self.value(head, None, pending.into_iter().rev().collect()));
                }
                Expr::Const(name, levels) => {
                    let head_id = self.tc.cache.shared(&current.expr);
                    let key = application_key(head_id, &pending, unfold);
                    if let Some(value) = self.state.applications.get(&key) {
                        return Ok(value.clone());
                    }
                    if let Some(value) = self.state.old_applications.get(&key).cloned() {
                        self.state.applications.insert(key, value.clone());
                        return Ok(value);
                    }
                    if visited.len() < VISITED_LIMIT {
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
                    let arity = NatOp::parse(name).map(NatOp::arity);
                    if levels.is_empty() && arity == Some(pending.len()) {
                        let mut args = Vec::new();
                        for arg in pending.iter().rev() {
                            let v = self.eval(arg, true)?;
                            let e = if let Expr::Const(n, us) = &v.head
                                && *n == self.tc.builtin_name(NAT_ZERO)
                                && us.is_empty()
                                && v.args.is_empty()
                            {
                                Expr::nat(0u32)
                            } else if matches!(v.head, Expr::Nat(_)) && v.args.is_empty() {
                                v.head.clone()
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
                        // Empty eliminators have no rule, so forcing their major cannot help.
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
                            let reduced_key = application_key(head_id, &pending, unfold);
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
                                let args = args.into_iter().map(|e| self.term(e, None)).collect();
                                value = self.value(head, None, args);
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
                    if let Some(Eliminator { major, function }) = self.tc.quotient_eliminator(name)
                        && pending.len() > major
                    {
                        let value = self.eval(&pending[pending.len() - 1 - major], true)?;
                        if matches!(&value.head, Expr::Const(n, _) if *n == self.tc.builtin_name(QUOT_MK))
                            && value.args.len() == QUOT_MK_ARITY
                        {
                            current = Closure::of(&pending[pending.len() - 1 - function]);
                            pending.truncate(pending.len() - 1 - major);
                            pending.push(value.args[QUOT_MK_ARITY - 1].clone());
                            continue;
                        }
                    }
                }
                _ => {}
            }
            return Ok(self.value(
                (*current.expr).clone(),
                current.context.clone(),
                pending.into_iter().rev().collect(),
            ));
        }
    }
}
