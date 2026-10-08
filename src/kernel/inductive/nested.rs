use super::*;
use crate::resource::Budget;
use crate::syntax::Binder;
use rustc_hash::{FxHashMap, FxHashSet};
use std::iter;

const PARAMETER_NAME: &str = "parameter";
const NESTED_PREFIX: &str = "_nested_";
const CTOR_PREFIX: &str = "ctor_";
const REC_PREFIX: &str = "rec_";

struct Auxiliary {
    name: String,
    application: Expr,
    constructors: Vec<(String, String)>,
}

pub(super) struct NestedExpansion {
    pub block: InductiveBlock,
    original_types: usize,
    original_constructors: usize,
    params: Vec<Local>,
    auxiliaries: Vec<Auxiliary>,
}

fn auxiliary_ctor_name(auxiliary: &str, index: usize) -> String {
    append_name(auxiliary, &format!("{CTOR_PREFIX}{index}"))
}

fn auxiliary_rec_name(base: &str, index: usize) -> String {
    append_name(base, &format!("{REC_PREFIX}{}", index + 1))
}

fn instantiate_params(mut ty: Expr, args: &[Expr]) -> Result<Expr> {
    for arg in args {
        let Expr::Pi(_, body) = ty else {
            return Err(Error::Rejected("missing nested inductive parameter".into()));
        };
        ty = (*body.instantiate(arg)).clone();
    }
    Ok(ty)
}

// Opening binders keeps constructor-local variables from passing as enclosing parameters.
fn rewrite(e: &Expr, f: &mut impl FnMut(&Expr) -> Result<Option<Expr>>) -> Result<Expr> {
    if let Some(replacement) = f(e)? {
        return Ok(replacement);
    }
    Ok(match e {
        Expr::App(a, b) => rewrite(a, f)?.app(rewrite(b, f)?),
        Expr::Pi(ty, b) | Expr::Lam(ty, b) => {
            let ty = rewrite(ty, f)?;
            let (n, body) = b.unbind_ref();
            let body = rewrite(&body, f)?;
            if matches!(e, Expr::Pi(..)) {
                Expr::pi(n, ty, body)
            } else {
                Expr::lam(n, ty, body)
            }
        }
        Expr::Let(ty, v, b) => {
            let ty = rewrite(ty, f)?;
            let v = rewrite(v, f)?;
            let (n, body) = b.unbind_ref();
            Expr::let_(n, ty, v, rewrite(&body, f)?)
        }
        Expr::Proj(n, i, v) => Expr::Proj(n.clone(), *i, Shared::new(rewrite(v, f)?)),
        other => other.clone(),
    })
}

type Memo = FxHashMap<usize, Shared<Expr>>;

/// Only sound for rewrites that do not depend on the enclosing binders.
fn rewrite_closed(
    e: &Expr,
    f: &mut impl FnMut(&Expr) -> Result<Option<Expr>>,
    memo: &mut Memo,
) -> Result<Expr> {
    fn shared(
        e: &Shared<Expr>,
        f: &mut impl FnMut(&Expr) -> Result<Option<Expr>>,
        memo: &mut Memo,
    ) -> Result<Shared<Expr>> {
        let key = e.as_ptr() as usize;
        if let Some(r) = memo.get(&key) {
            return Ok(r.clone());
        }
        let r = Shared::new(rewrite_closed(e, f, memo)?);
        memo.insert(key, r.clone());
        Ok(r)
    }
    fn binder(
        b: &Binder,
        f: &mut impl FnMut(&Expr) -> Result<Option<Expr>>,
        memo: &mut Memo,
    ) -> Result<Binder> {
        Ok(bind(b.pattern().clone(), shared(b.body(), f, memo)?))
    }
    if let Some(replacement) = f(e)? {
        return Ok(replacement);
    }
    Ok(match e {
        Expr::App(a, b) => Expr::App(shared(a, f, memo)?, shared(b, f, memo)?),
        Expr::Pi(ty, b) => Expr::Pi(shared(ty, f, memo)?, binder(b, f, memo)?),
        Expr::Lam(ty, b) => Expr::Lam(shared(ty, f, memo)?, binder(b, f, memo)?),
        Expr::Let(ty, v, b) => Expr::Let(
            shared(ty, f, memo)?,
            shared(v, f, memo)?,
            binder(b, f, memo)?,
        ),
        Expr::Proj(n, i, v) => Expr::Proj(n.clone(), *i, shared(v, f, memo)?),
        other => other.clone(),
    })
}

fn has_binder(e: &Expr) -> bool {
    match e {
        Expr::Pi(..) | Expr::Lam(..) | Expr::Let(..) => true,
        Expr::App(f, a) => has_binder(f) || has_binder(a),
        Expr::Proj(_, _, v) => has_binder(v),
        _ => false,
    }
}

enum Walk<'a> {
    Open,
    Closed(&'a [bool], &'a mut bool),
}

impl NestedExpansion {
    fn universe_params(&self) -> &[String] {
        &self.block.types[0].params
    }

    pub fn is_nested(&self) -> bool {
        !self.auxiliaries.is_empty()
    }

    pub fn new(env: &Environment, original: &InductiveBlock) -> Result<Self> {
        let first = &original.types[0];
        let mut params = Vec::new();
        let mut ty = first.ty.clone();
        for _ in 0..first.num_params {
            let Expr::Pi(domain, body) = ty else {
                return Err(Error::Rejected("missing inductive parameter".into()));
            };
            let local = (Name::new(PARAMETER_NAME), (*domain).clone());
            ty = (*body.instantiate(&variable(&local))).clone();
            params.push(local);
        }
        let mut result = Self {
            block: original.clone(),
            original_types: original.types.len(),
            original_constructors: original.constructors.len(),
            params,
            auxiliaries: Vec::new(),
        };
        result.block.recursors.clear();
        // Auxiliary recursor names follow declared constructor order, not serialized order.
        result.block.constructors = original
            .types
            .iter()
            .flat_map(|t| &t.constructors)
            .map(|name| {
                original
                    .constructors
                    .iter()
                    .find(|c| &c.name == name)
                    .cloned()
                    .ok_or_else(|| Error::Rejected("missing constructor".into()))
            })
            .collect::<Result<_>>()?;
        demand(
            result.block.constructors.len() == original.constructors.len(),
            "extraneous constructor",
        )?;
        let mut reserved: BTreeSet<String> = original
            .types
            .iter()
            .map(|t| t.name.clone())
            .chain(original.constructors.iter().map(|c| c.name.clone()))
            .chain(original.recursors.iter().map(|r| r.name.clone()))
            .collect();
        let mut fuel = 100_000usize;
        let mut next_name = 0usize;
        let mut cursor = 0;
        while cursor < result.block.constructors.len() {
            let c = result.block.constructors[cursor].clone();
            let mut body = c.ty;
            let mut locals = Vec::new();
            for p in &result.params {
                let Expr::Pi(domain, rest) = body else {
                    return Err(Error::Rejected("missing constructor parameter".into()));
                };
                locals.push((p.0.clone(), (*domain).clone()));
                body = (*rest.instantiate(&variable(p))).clone();
            }
            let names = result.block.type_names().into_iter().collect();
            let body = rewrite(&body, &mut |e| {
                fuel = fuel
                    .checked_sub(1)
                    .ok_or_else(|| Error::from(Budget::NestedExpansion))?;
                // Keep DAG sharing for domains that cannot contain nested occurrences.
                if !occurs(e, &names) {
                    return Ok(Some(e.clone()));
                }
                result.replace_nested(env, e, &mut reserved, &mut next_name)
            })?;
            result.block.constructors[cursor].ty = pis(&locals, body);
            cursor += 1;
        }
        let all = result.block.type_names();
        for t in &mut result.block.types {
            t.all = all.clone();
            t.num_nested = result.auxiliaries.len();
        }
        Ok(result)
    }

    fn replace_nested(
        &mut self,
        env: &Environment,
        e: &Expr,
        reserved: &mut BTreeSet<String>,
        next: &mut usize,
    ) -> Result<Option<Expr>> {
        let (head, args) = spine(e);
        let Expr::Const(name, levels) = head else {
            return Ok(None);
        };
        let Some(container) = env.inductives.get(&name) else {
            return Ok(None);
        };
        if args.len() < container.num_params {
            return Ok(None);
        }
        let nested_args = &args[..container.num_params];
        let names: BTreeSet<_> = self.block.type_names().into_iter().collect();
        if !nested_args.iter().any(|e| occurs(e, &names)) {
            return Ok(None);
        }
        let allowed: Vec<_> = self.params.iter().filter_map(|p| p.0.to_any()).collect();
        for arg in nested_args {
            demand(
                arg.fv().iter().all(|n| allowed.contains(n)),
                "nested inductive parameters contain constructor-local variables",
            )?;
        }
        let application = apply(
            Expr::Const(name.clone(), levels.clone()),
            nested_args.iter().cloned(),
        );
        let found = self
            .auxiliaries
            .iter()
            .find(|a| a.application.aeq(&application))
            .map(|a| a.name.clone());
        let auxiliary = if let Some(found) = found {
            found
        } else {
            let mut found = None;
            for member in &container.all {
                let aux_name =
                    self.add_auxiliary(env, member, &levels, nested_args, reserved, next)?;
                if member == &name {
                    found = Some(aux_name);
                }
            }
            found.ok_or_else(|| Error::Rejected("invalid nested mutual family".into()))?
        };
        let levels = self
            .universe_params()
            .iter()
            .cloned()
            .map(Level::Param)
            .collect();
        Ok(Some(apply(
            Expr::Const(auxiliary, levels),
            self.params
                .iter()
                .map(variable)
                .chain(args[container.num_params..].iter().cloned()),
        )))
    }

    fn fresh_auxiliary_name(
        &self,
        env: &Environment,
        source: &InductiveType,
        reserved: &mut BTreeSet<String>,
        next: &mut usize,
    ) -> String {
        loop {
            *next += 1;
            let candidate =
                append_name(&self.block.types[0].name, &format!("{NESTED_PREFIX}{next}"));
            if !env.declarations.contains_key(&candidate)
                && !reserved.contains(&candidate)
                && !env.declarations.contains_key(&rec_name(&candidate))
                && !reserved.contains(&rec_name(&candidate))
                && source.constructors.iter().enumerate().all(|(i, _)| {
                    let ctor = auxiliary_ctor_name(&candidate, i);
                    !env.declarations.contains_key(&ctor) && !reserved.contains(&ctor)
                })
            {
                reserved.insert(candidate.clone());
                reserved.insert(rec_name(&candidate));
                return candidate;
            }
        }
    }

    fn add_auxiliary(
        &mut self,
        env: &Environment,
        member: &str,
        levels: &[Level],
        nested_args: &[Expr],
        reserved: &mut BTreeSet<String>,
        next: &mut usize,
    ) -> Result<String> {
        let source = &env.inductives[member];
        demand(
            source.params.len() == levels.len(),
            "nested inductive universe argument count mismatch",
        )?;
        let substitution = level_substitution(&source.params, levels);
        let aux_name = self.fresh_auxiliary_name(env, source, reserved, next);
        let source_ty = source.ty.substitute_levels(&substitution)?;
        let specialized = instantiate_params(source_ty, nested_args)?;
        let ty = pis(&self.params, specialized);
        let mut constructors = Vec::new();
        for (i, source_name) in source.constructors.iter().enumerate() {
            let source_ctor = &env.constructors[source_name];
            let cname = auxiliary_ctor_name(&aux_name, i);
            demand(
                !env.declarations.contains_key(&cname) && reserved.insert(cname.clone()),
                "duplicate nested auxiliary name",
            )?;
            let subst = level_substitution(&source_ctor.params, levels);
            let cty = instantiate_params(source_ctor.ty.substitute_levels(&subst)?, nested_args)?;
            self.block.constructors.push(Constructor {
                name: cname.clone(),
                params: self.universe_params().to_vec(),
                ty: pis(&self.params, cty),
                inductive: aux_name.clone(),
                index: i,
                num_params: self.params.len(),
                num_fields: source_ctor.num_fields,
            });
            constructors.push((cname, source_name.clone()));
        }
        self.block.types.push(InductiveType {
            name: aux_name.clone(),
            params: self.universe_params().to_vec(),
            ty,
            all: Vec::new(),
            constructors: constructors.iter().map(|c| c.0.clone()).collect(),
            num_params: self.params.len(),
            num_indices: source.num_indices,
            num_nested: 0,
            recursive: false,
            reflexive: false,
        });
        self.auxiliaries.push(Auxiliary {
            name: aux_name.clone(),
            application: apply(
                Expr::Const(member.into(), levels.to_vec()),
                nested_args.iter().cloned(),
            ),
            constructors,
        });
        Ok(aux_name)
    }

    fn restore_expr(&self, e: &Expr, recs: &[String], names: &FxHashSet<&str>) -> Result<Expr> {
        let binders: Vec<_> = self
            .auxiliaries
            .iter()
            .map(|a| has_binder(&a.application))
            .collect();
        let mut loose = false;
        let r = self.restore_walk(e, recs, names, &mut Walk::Closed(&binders, &mut loose))?;
        if loose {
            return self.restore_walk(e, recs, names, &mut Walk::Open);
        }
        Ok(r)
    }

    fn restore_walk(
        &self,
        e: &Expr,
        recs: &[String],
        names: &FxHashSet<&str>,
        walk: &mut Walk,
    ) -> Result<Expr> {
        let f = |term: &Expr, walk: &mut Walk| -> Result<Option<Expr>> {
            let mut head = term;
            while let Expr::App(f, _) = head {
                head = f;
            }
            if !matches!(head, Expr::Const(n, _) if names.contains(n.as_str())) {
                return Ok(None);
            }
            let (head, args) = spine(term);
            let Expr::Const(name, levels) = head else {
                return Ok(None);
            };
            for (i, auxiliary) in self.auxiliaries.iter().enumerate() {
                if name == recs[i] {
                    if args.is_empty() {
                        return Ok(Some(Expr::Const(
                            auxiliary_rec_name(&self.block.types[0].name, i),
                            levels,
                        )));
                    }
                    return Ok(None);
                }
                let ctor = auxiliary.constructors.iter().find(|(n, _)| *n == name);
                if name != auxiliary.name && ctor.is_none() {
                    continue;
                }
                demand(
                    args.len() >= self.params.len(),
                    "unsaturated nested auxiliary application",
                )?;
                if let Walk::Closed(binders, loose) = walk
                    && binders[i]
                    && args[..self.params.len()]
                        .iter()
                        .any(|a| a.support().has_loose_bound_vars())
                {
                    **loose = true;
                    return Ok(Some(term.clone()));
                }
                let level_subst = level_substitution(self.universe_params(), &levels);
                let mut nested = auxiliary.application.substitute_levels(&level_subst)?;
                for (p, arg) in self.params.iter().zip(&args) {
                    nested = nested.subst(&p.0, arg);
                }
                let restored = if let Some((_, original)) = ctor {
                    let (container, params) = spine(&nested);
                    let Expr::Const(_, us) = container else {
                        return Err(Error::Rejected(
                            "invalid nested constructor restoration".into(),
                        ));
                    };
                    apply(Expr::Const(original.clone(), us), params)
                } else {
                    nested
                };
                let tail = args[self.params.len()..]
                    .iter()
                    .map(|a| self.restore_walk(a, recs, names, walk))
                    .collect::<Result<Vec<_>>>()?;
                return Ok(Some(apply(restored, tail)));
            }
            Ok(None)
        };
        match walk {
            Walk::Open => rewrite(e, &mut |t| f(t, &mut Walk::Open)),
            Walk::Closed(binders, loose) => rewrite_closed(
                e,
                &mut |t| f(t, &mut Walk::Closed(binders, loose)),
                &mut Memo::default(),
            ),
        }
    }

    pub fn restore(&self, mut generated: InductiveBlock) -> Result<InductiveBlock> {
        if !self.is_nested() {
            return Ok(generated);
        }
        generated.types.truncate(self.original_types);
        generated.constructors.truncate(self.original_constructors);
        let all = generated.type_names();
        let recs: Vec<_> = self.auxiliaries.iter().map(|a| rec_name(&a.name)).collect();
        let names: FxHashSet<&str> = self
            .auxiliaries
            .iter()
            .flat_map(|a| iter::once(&a.name).chain(a.constructors.iter().map(|c| &c.0)))
            .chain(&recs)
            .map(String::as_str)
            .collect();
        for t in &mut generated.types {
            t.all = all.clone();
        }
        for c in &mut generated.constructors {
            c.ty = self.restore_expr(&c.ty, &recs, &names)?;
        }
        for r in &mut generated.recursors {
            r.ty = self.restore_expr(&r.ty, &recs, &names)?;
            r.all = all.clone();
            if let Some(i) = recs.iter().position(|n| *n == r.name) {
                r.name = auxiliary_rec_name(&generated.types[0].name, i);
            }
            for rule in &mut r.rules {
                rule.rhs = self.restore_expr(&rule.rhs, &recs, &names)?;
                for auxiliary in &self.auxiliaries {
                    if let Some((_, original)) = auxiliary
                        .constructors
                        .iter()
                        .find(|(n, _)| *n == rule.constructor)
                    {
                        rule.constructor = original.clone();
                        break;
                    }
                }
            }
        }
        Ok(generated)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::parse_expr;

    fn spec(name: &str, ty: &str, params: usize, ctors: &[(&str, &str, usize)]) -> InductiveBlock {
        InductiveBlock {
            types: vec![InductiveType {
                name: name.into(),
                params: vec![],
                ty: parse_expr(ty).unwrap(),
                all: vec![name.into()],
                constructors: ctors.iter().map(|c| c.0.into()).collect(),
                num_params: params,
                num_indices: 0,
                num_nested: 0,
                recursive: false,
                reflexive: false,
            }],
            constructors: ctors
                .iter()
                .enumerate()
                .map(|(i, (n, ty, fields))| Constructor {
                    name: (*n).into(),
                    params: vec![],
                    ty: parse_expr(ty).unwrap(),
                    inductive: name.into(),
                    index: i,
                    num_params: params,
                    num_fields: *fields,
                })
                .collect(),
            recursors: vec![],
        }
    }

    fn complete(env: &mut Environment, input: InductiveBlock) -> InductiveBlock {
        let expansion = NestedExpansion::new(env, &input).unwrap();
        let mut temporary = Vec::new();
        let generated = env
            .generate_inductive(&expansion.block, &mut temporary)
            .unwrap();
        let restored = expansion.restore(generated).unwrap();
        for name in temporary {
            env.declarations.remove(&name);
        }
        restored
    }

    #[test]
    fn nested_discovery_preserves_unrelated_shared_domains() {
        let mut block = spec("Tree", "Type", 0, &[("node", "Type -> Tree", 1)]);
        let mut domain = Shared::new(Expr::Const("Leaf".into(), vec![]));
        for _ in 0..18 {
            let pair = Shared::new(Expr::Const("Pair".into(), vec![]));
            let head = Shared::new(Expr::App(pair, domain.clone()));
            domain = Shared::new(Expr::App(head, domain.clone()));
        }
        block.constructors[0].ty = Expr::pi(
            Name::new("field"),
            (*domain).clone(),
            Expr::Const("Tree".into(), vec![]),
        );
        let expansion = NestedExpansion::new(&Environment::new(), &block).unwrap();
        assert!(!expansion.is_nested());
        let Expr::Pi(result, _) = &expansion.block.constructors[0].ty else {
            panic!("missing constructor domain");
        };
        let (Expr::App(original, _), Expr::App(rewritten, _)) = (&*domain, &**result) else {
            panic!("missing shared domain");
        };
        assert_eq!(original.as_ptr(), rewritten.as_ptr());
    }

    #[test]
    fn rejected_nested_blocks_roll_back_and_auxiliaries_remain_private() {
        let mut env = Environment::new();
        let list = complete(
            &mut env,
            spec(
                "List",
                "Type -> Type",
                1,
                &[
                    ("nil", "forall (A : Type), List A", 0),
                    ("cons", "forall (A : Type), A -> List A -> List A", 2),
                ],
            ),
        );
        env.declare_inductive(list).unwrap();
        let rose = complete(
            &mut env,
            spec("Rose", "Type", 0, &[("node", "List Rose -> Rose", 1)]),
        );
        let original_names: Vec<_> = env.declarations.keys().cloned().collect();
        let mut forged = rose.clone();
        forged.recursors[1].rules[1].rhs = Expr::Sort(Level::Nat(0));
        assert!(env.declare_inductive(forged).is_err());
        assert_eq!(
            env.declarations.keys().cloned().collect::<Vec<_>>(),
            original_names
        );
        assert_eq!(env.inductives.len(), 1);
        assert_eq!(env.constructors.len(), 2);
        assert_eq!(env.recursors.len(), 1);
        env.declare_inductive(rose).unwrap();
        assert_eq!(env.declarations.len(), 8);
        assert_eq!(env.inductives.len(), 2);
        assert_eq!(env.constructors.len(), 3);
        assert_eq!(env.recursors.len(), 3);
        assert!(env.declarations.keys().all(|n| !n.contains("_nested_")));
    }
}
