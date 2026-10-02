use super::*;

struct Auxiliary {
    name: String,
    application: Expr,
    constructors: Vec<(String, String)>,
}

/// A private mutual presentation of a nested declaration. No auxiliary types
/// or constructors are retained in the public environment.
pub(super) struct NestedExpansion {
    pub block: InductiveBlock,
    original_types: usize,
    original_constructors: usize,
    params: Vec<Local>,
    auxiliaries: Vec<Auxiliary>,
}

fn append_name(name: &str, suffix: &str) -> String {
    if let Ok(mut parts) = serde_json::from_str::<Vec<serde_json::Value>>(name) {
        parts.push(serde_json::Value::String(suffix.into()));
        serde_json::to_string(&parts).unwrap()
    } else {
        format!("{name}.{suffix}")
    }
}

fn instantiate_params(mut ty: Expr, args: &[Expr]) -> Result<Expr> {
    for arg in args {
        let Expr::Pi(_, body) = ty else {
            return Err(Error("missing nested inductive parameter".into()));
        };
        ty = (*body.instantiate(arg)).clone();
    }
    Ok(ty)
}

// Open binder bodies before visiting them, so a constructor-local variable
// cannot be mistaken for an allowed enclosing inductive parameter.
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

impl NestedExpansion {
    pub fn is_nested(&self) -> bool {
        !self.auxiliaries.is_empty()
    }

    pub fn new(env: &Environment, original: &InductiveBlock) -> Result<Self> {
        let first = &original.types[0];
        let mut params = Vec::new();
        let mut ty = first.ty.clone();
        for _ in 0..first.num_params {
            let Expr::Pi(domain, body) = ty else {
                return Err(Error("missing inductive parameter".into()));
            };
            let local = (Name::new("parameter"), (*domain).clone());
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
        // Discovery order determines auxiliary recursor names. Use each type's
        // declared constructor order, independently of the serialized array order.
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
                    .ok_or_else(|| Error("missing constructor".into()))
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
        // New auxiliary constructors can themselves contain nested occurrences.
        while cursor < result.block.constructors.len() {
            let c = result.block.constructors[cursor].clone();
            let mut body = c.ty;
            let mut locals = Vec::new();
            for p in &result.params {
                let Expr::Pi(domain, rest) = body else {
                    return Err(Error("missing constructor parameter".into()));
                };
                locals.push((p.0.clone(), (*domain).clone()));
                body = (*rest.instantiate(&variable(p))).clone();
            }
            let body = rewrite(&body, &mut |e| {
                fuel = fuel.checked_sub(1).ok_or_else(|| {
                    Error("checking budget exhausted during nested expansion".into())
                })?;
                result.replace_nested(env, e, &mut reserved, &mut next_name)
            })?;
            result.block.constructors[cursor].ty = abstract_over(&locals, body, false);
            cursor += 1;
        }
        let all: Vec<_> = result.block.types.iter().map(|t| t.name.clone()).collect();
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
        let names: BTreeSet<_> = self.block.types.iter().map(|t| t.name.clone()).collect();
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
                let source = &env.inductives[member];
                demand(
                    source.params.len() == levels.len(),
                    "nested inductive universe argument count mismatch",
                )?;
                let substitution = source
                    .params
                    .iter()
                    .cloned()
                    .zip(levels.iter().cloned())
                    .collect();
                let aux_name = loop {
                    *next += 1;
                    let candidate =
                        append_name(&self.block.types[0].name, &format!("_nested_{next}"));
                    if !env.declarations.contains_key(&candidate)
                        && !reserved.contains(&candidate)
                        && !env.declarations.contains_key(&rec_name(&candidate))
                        && !reserved.contains(&rec_name(&candidate))
                        && source.constructors.iter().enumerate().all(|(i, _)| {
                            let ctor = append_name(&candidate, &format!("ctor_{i}"));
                            !env.declarations.contains_key(&ctor) && !reserved.contains(&ctor)
                        })
                    {
                        reserved.insert(candidate.clone());
                        reserved.insert(rec_name(&candidate));
                        break candidate;
                    }
                };
                let source_ty = source.ty.substitute_levels(&substitution)?;
                let specialized = instantiate_params(source_ty, nested_args)?;
                let ty = abstract_over(&self.params, specialized, false);
                let mut constructors = Vec::new();
                for (i, source_name) in source.constructors.iter().enumerate() {
                    let source_ctor = &env.constructors[source_name];
                    let cname = append_name(&aux_name, &format!("ctor_{i}"));
                    demand(
                        !env.declarations.contains_key(&cname) && reserved.insert(cname.clone()),
                        "duplicate nested auxiliary name",
                    )?;
                    let subst = source_ctor
                        .params
                        .iter()
                        .cloned()
                        .zip(levels.iter().cloned())
                        .collect();
                    let cty =
                        instantiate_params(source_ctor.ty.substitute_levels(&subst)?, nested_args)?;
                    self.block.constructors.push(Constructor {
                        name: cname.clone(),
                        params: self.block.types[0].params.clone(),
                        ty: abstract_over(&self.params, cty, false),
                        inductive: aux_name.clone(),
                        index: i,
                        num_params: self.params.len(),
                        num_fields: source_ctor.num_fields,
                    });
                    constructors.push((cname, source_name.clone()));
                }
                self.block.types.push(InductiveType {
                    name: aux_name.clone(),
                    params: self.block.types[0].params.clone(),
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
                        Expr::Const(member.clone(), levels.clone()),
                        nested_args.iter().cloned(),
                    ),
                    constructors,
                });
                if member == &name {
                    found = Some(aux_name);
                }
            }
            found.ok_or_else(|| Error("invalid nested mutual family".into()))?
        };
        let levels = self.block.types[0]
            .params
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

    fn restore_expr(&self, e: &Expr) -> Result<Expr> {
        rewrite(e, &mut |term| {
            let (head, args) = spine(term);
            let Expr::Const(name, levels) = head else {
                return Ok(None);
            };
            for (i, auxiliary) in self.auxiliaries.iter().enumerate() {
                if name == rec_name(&auxiliary.name) {
                    // Rename the head only; ordinary traversal restores its arguments.
                    if args.is_empty() {
                        return Ok(Some(Expr::Const(
                            append_name(&self.block.types[0].name, &format!("rec_{}", i + 1)),
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
                let level_subst = self.block.types[0]
                    .params
                    .iter()
                    .cloned()
                    .zip(levels.iter().cloned())
                    .collect();
                let mut nested = auxiliary.application.substitute_levels(&level_subst)?;
                for (p, arg) in self.params.iter().zip(&args) {
                    nested = nested.subst(&p.0, arg);
                }
                let restored = if let Some((_, original)) = ctor {
                    let (container, params) = spine(&nested);
                    let Expr::Const(_, us) = container else {
                        return Err(Error("invalid nested constructor restoration".into()));
                    };
                    apply(Expr::Const(original.clone(), us), params)
                } else {
                    nested
                };
                let tail = args[self.params.len()..]
                    .iter()
                    .map(|a| self.restore_expr(a))
                    .collect::<Result<Vec<_>>>()?;
                return Ok(Some(apply(restored, tail)));
            }
            Ok(None)
        })
    }

    pub fn restore(&self, mut generated: InductiveBlock) -> Result<InductiveBlock> {
        if !self.is_nested() {
            return Ok(generated);
        }
        generated.types.truncate(self.original_types);
        generated.constructors.truncate(self.original_constructors);
        let all: Vec<_> = generated.types.iter().map(|t| t.name.clone()).collect();
        for t in &mut generated.types {
            t.all = all.clone();
        }
        for c in &mut generated.constructors {
            c.ty = self.restore_expr(&c.ty)?;
        }
        for r in &mut generated.recursors {
            r.ty = self.restore_expr(&r.ty)?;
            r.all = all.clone();
            if let Some(i) = self
                .auxiliaries
                .iter()
                .position(|a| rec_name(&a.name) == r.name)
            {
                r.name = append_name(&generated.types[0].name, &format!("rec_{}", i + 1));
            }
            for rule in &mut r.rules {
                rule.rhs = self.restore_expr(&rule.rhs)?;
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

    // Prepare valid input to exercise the transaction, then deliberately corrupt
    // an exported rule. Signature correctness is tested with official exports.
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
