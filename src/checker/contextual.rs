//! Infer under binders without copying the remaining body at each binder.
use super::Tc;
use crate::term::{expr::Expr, ptr::ExprPtr};
use crate::{ensure, reject};
use std::rc::Rc;

impl<'t, 'a: 't> Tc<'t, 'a> {
    pub(super) fn support(&mut self, e: ExprPtr<'t>) -> Rc<[u16]> {
        if e.closed() {
            return Rc::from([]);
        }
        if let Some(s) = self.support_cache.get(&e) {
            return s.clone();
        }
        let mut slots = Vec::new();
        match *e {
            Expr::Var { idx, .. } => slots.push(idx),
            Expr::App { fun, arg, .. } => {
                slots.extend_from_slice(&self.support(fun));
                slots.extend_from_slice(&self.support(arg));
            }
            Expr::Lam { ty, body, .. } | Expr::Pi { ty, body, .. } => {
                slots.extend_from_slice(&self.support(ty));
                slots.extend(self.support(body).iter().filter_map(|i| i.checked_sub(1)));
            }
            Expr::Let { data, .. } => {
                slots.extend_from_slice(&self.support(data.ty));
                slots.extend_from_slice(&self.support(data.val));
                slots.extend(
                    self.support(data.body)
                        .iter()
                        .filter_map(|i| i.checked_sub(1)),
                );
            }
            Expr::Proj { e, .. } => slots.extend_from_slice(&self.support(e)),
            _ => {}
        }
        slots.sort_unstable();
        slots.dedup();
        let slots: Rc<[u16]> = slots.into();
        self.support_cache.insert(e, slots.clone());
        slots
    }

    fn infer_under(
        &mut self,
        e: ExprPtr<'t>,
        env: &mut Vec<ExprPtr<'t>>,
        only: bool,
    ) -> ExprPtr<'t> {
        if e.closed() {
            self.infer(e, only)
        } else {
            self.infer_contextual(e, env, only)
        }
    }

    pub(super) fn infer_contextual(
        &mut self,
        e: ExprPtr<'t>,
        env: &mut Vec<ExprPtr<'t>>,
        only: bool,
    ) -> ExprPtr<'t> {
        self.tick();
        let slots = self.support(e);
        let relevant: Vec<_> = slots
            .iter()
            .map(|&i| {
                *env.get(
                    env.len()
                        .checked_sub(usize::from(i) + 1)
                        .unwrap_or_else(|| reject!("unexpected bound variable")),
                )
                .unwrap_or_else(|| reject!("unexpected bound variable"))
            })
            .collect();
        let key = (e, relevant);
        if let Some(&ty) = self.open_infer_cache[0].get(&key) {
            return ty;
        }
        if only && let Some(&ty) = self.open_infer_cache[1].get(&key) {
            return ty;
        }
        let result = match *e {
            Expr::Var { idx, .. } => self.infer(env[env.len() - 1 - usize::from(idx)], only),
            Expr::App { .. } => {
                let (head, args) = self.ctx.unfold_apps(e);
                let mut ft = self.infer_under(head, env, only);
                for arg in args {
                    self.tick();
                    ft = self.ensure_pi(ft);
                    let Expr::Pi { ty, body, .. } = *ft else {
                        unreachable!()
                    };
                    if !only {
                        let actual = self.infer_under(arg, env, false);
                        ensure!(self.def_eq(actual, ty), "application type mismatch");
                    }
                    ft = if body.closed() {
                        body
                    } else {
                        let value = self.ctx.inst(arg, env);
                        self.ctx.inst1(body, value)
                    };
                }
                ft
            }
            Expr::Lam { ty, body, .. } | Expr::Pi { ty, body, .. } => {
                let domain = self.ctx.inst(ty, env);
                let sort = if matches!(*e, Expr::Pi { .. }) || !only {
                    let inferred = self.infer(domain, only);
                    Some(self.ensure_sort(inferred))
                } else {
                    None
                };
                let local = self.fresh_local(domain);
                env.push(local);
                let result = self.infer_under(body, env, only);
                env.pop();
                if matches!(*e, Expr::Pi { .. }) {
                    let level = self.ensure_sort(result);
                    let level = self.ctx.imax(sort.unwrap(), level);
                    self.ctx.sort(level)
                } else {
                    let result = self.ctx.abstract_locals(result, &[local]);
                    self.ctx.pi(domain, result)
                }
            }
            Expr::Let { data, .. } => {
                if !only {
                    let ty = self.ctx.inst(data.ty, env);
                    self.check_type(ty);
                    let actual = self.infer_under(data.val, env, false);
                    ensure!(self.def_eq(actual, ty), "let value type mismatch");
                }
                let value = self.ctx.inst(data.val, env);
                env.push(value);
                let result = self.infer_under(data.body, env, only);
                env.pop();
                result
            }
            _ => {
                let closed = self.ctx.inst(e, env);
                self.infer(closed, only)
            }
        };
        self.open_infer_cache[usize::from(only)].insert(key, result);
        result
    }
}
