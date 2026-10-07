use super::*;

impl Checker<'_> {
    pub(in crate::kernel) fn reduce_neutral_recursor(
        &mut self,
        head: &Expr,
        args: &[Expr],
    ) -> Result<Option<Expr>> {
        let Expr::Const(name, levels) = head else {
            return Ok(None);
        };
        let Some(rec) = self.env.recursors.get(name).cloned() else {
            return Ok(None);
        };
        // Ordinary constructor reduction already failed, so only structure eta or K can apply.
        if !rec.k
            && !rec.rules.first().is_some_and(|rule| {
                self.structure(&self.env.constructors[&rule.constructor].inductive)
                    .is_some()
            })
        {
            return Ok(None);
        }
        let major_pos = rec.num_params + rec.num_motives + rec.num_minors + rec.num_indices;
        if args.len() <= major_pos {
            return Ok(None);
        }
        let subst = self.level_arguments(&rec.params, levels)?;
        // K compares the major's type, so it must not evaluate its proof body.
        let major = if rec.k {
            args[major_pos].clone()
        } else {
            self.whnf(&args[major_pos])?
        };
        let major = match major {
            Expr::Nat(n) => self.nat_constructor(&n.0),
            Expr::Str(s) => {
                let expanded = self.string_constructor(&s)?;
                self.whnf(&expanded)?
            }
            other => other,
        };
        let (mut ctor, mut fields) = spine(&major);
        if !matches!(&ctor, Expr::Const(n, _) if self.env.constructors.contains_key(n))
            && let Some(rule) = rec.rules.first()
            && let Some(expanded) = self.eta_expand_major(rule, &major)?
        {
            (ctor, fields) = expanded;
        }
        if rec.k
            && !matches!(&ctor, Expr::Const(n, _) if rec.rules.iter().any(|r| r.constructor == *n))
        {
            let Some(expanded) =
                self.k_major(&rec.rules[0], &subst, &major, &args[..rec.num_params])?
            else {
                return Ok(None);
            };
            (ctor, fields) = expanded;
        }
        let Expr::Const(name, _) = ctor else {
            return Ok(None);
        };
        let Some(rule) = rec.rules.iter().find(|r| r.constructor == name) else {
            return Ok(None);
        };
        let ctor_params = self
            .env
            .constructors
            .get(&name)
            .ok_or_else(|| Error("missing recursor constructor".into()))?
            .num_params;
        if fields.len() != ctor_params + rule.num_fields {
            return Ok(None);
        }
        let rhs = self.substitute_levels(&rule.rhs, &subst)?;
        let prefix = rec.num_params + rec.num_motives + rec.num_minors;
        Ok(Some(apply(
            rhs,
            args[..prefix]
                .iter()
                .chain(&fields[ctor_params..])
                .chain(&args[major_pos + 1..])
                .cloned(),
        )))
    }

    fn eta_expand_major(
        &mut self,
        rule: &RecursorRule,
        major: &Expr,
    ) -> Result<Option<(Expr, Vec<Expr>)>> {
        let info = self.env.constructors[&rule.constructor].clone();
        if self.structure(&info.inductive).is_none() {
            return Ok(None);
        }
        let ty = self.type_of(major)?;
        let ty = self.whnf(&ty)?;
        let (head, mut fields) = spine(&ty);
        let Expr::Const(n, us) = head else {
            return Ok(None);
        };
        if n != info.inductive || is_zero(&self.sort(&ty)?)? || fields.len() != info.num_params {
            return Ok(None);
        }
        fields.extend(
            (0..info.num_fields)
                .map(|i| Expr::Proj(info.inductive.clone(), i, Shared::new(major.clone()))),
        );
        Ok(Some((Expr::Const(info.name.clone(), us), fields)))
    }

    fn k_major(
        &mut self,
        rule: &RecursorRule,
        subst: &BTreeMap<String, Level>,
        major: &Expr,
        params: &[Expr],
    ) -> Result<Option<(Expr, Vec<Expr>)>> {
        let info = &self.env.constructors[&rule.constructor];
        let us = info
            .params
            .iter()
            .map(|n| {
                subst
                    .get(n)
                    .cloned()
                    .ok_or_else(|| Error("missing recursor universe argument".into()))
            })
            .collect::<Result<Vec<_>>>()?;
        let replacement = apply(
            Expr::Const(rule.constructor.clone(), us.clone()),
            params.iter().cloned(),
        );
        let actual = self.type_of(major)?;
        let expected = self.type_of(&replacement)?;
        if !self.conv(&actual, &expected)? {
            return Ok(None);
        }
        Ok(Some((
            Expr::Const(rule.constructor.clone(), us),
            params.to_vec(),
        )))
    }
}

impl Checker<'_> {
    pub(in crate::kernel) fn structure(&self, name: &str) -> Option<Rc<Constructor>> {
        let info = self.env.inductives.get(name)?;
        if info.recursive || info.num_indices != 0 || info.constructors.len() != 1 {
            return None;
        }
        self.env.constructors.get(&info.constructors[0]).cloned()
    }

    pub(in crate::kernel) fn unit_like(&mut self, ty: &Expr) -> Result<bool> {
        let ty = self.whnf(ty)?;
        let (head, _) = spine(&ty);
        Ok(
            matches!(head, Expr::Const(n, _) if self.structure(&n).is_some_and(|c| c.num_fields == 0)),
        )
    }

    pub(in crate::kernel) fn infer_projection(
        &mut self,
        name: &str,
        index: usize,
        e: &Shared<Expr>,
    ) -> Result<Expr> {
        let ty = self.type_of(e)?;
        let ty = self.whnf(&ty)?;
        let (head, args) = spine(&ty);
        let Expr::Const(n, levels) = head else {
            return Err(Error("projection from non-inductive type".into()));
        };
        demand(n == name, "projection type name mismatch")?;
        let info = self
            .env
            .inductives
            .get(name)
            .ok_or_else(|| Error("projection from non-inductive type".into()))?;
        demand(
            info.constructors.len() == 1 && args.len() == info.num_params + info.num_indices,
            "projection requires a single-constructor inductive",
        )?;
        let ctor = self.env.constructors[&info.constructors[0]].clone();
        demand(index < ctor.num_fields, "projection field out of range")?;
        let subst = self.level_arguments(&ctor.params, &levels)?;
        let mut field_ty = self.substitute_levels(&ctor.ty, &subst)?;
        for arg in args.into_iter().take(ctor.num_params) {
            let Expr::Pi(_, body) = self.whnf(&field_ty)? else {
                return Err(Error("invalid constructor telescope".into()));
            };
            field_ty = (*body.instantiate(&arg)).clone();
        }
        let prop = is_zero(&self.sort(&ty)?)?;
        for i in 0..index {
            let Expr::Pi(domain, body) = self.whnf(&field_ty)? else {
                return Err(Error("invalid projection telescope".into()));
            };
            let (n, opened) = body.unbind_ref();
            let depends = opened.fv().contains(&n.to_any().unwrap());
            if prop && depends {
                demand(
                    is_zero(&self.sort(&domain)?)?,
                    "projection eliminates proposition into data",
                )?;
            }
            field_ty = (*body.instantiate(&Expr::Proj(name.into(), i, e.clone()))).clone();
        }
        let Expr::Pi(domain, _) = self.whnf(&field_ty)? else {
            return Err(Error("invalid projection telescope".into()));
        };
        if prop {
            demand(
                is_zero(&self.sort(&domain)?)?,
                "projection eliminates proposition into data",
            )?;
        }
        Ok((*domain).clone())
    }

    pub(in crate::kernel) fn structure_eta(&mut self, a: &Expr, b: &Expr) -> Result<bool> {
        let (head, args) = spine(b);
        let Expr::Const(n, _) = head else {
            return Ok(false);
        };
        let Some(ctor) = self.env.constructors.get(&n).cloned() else {
            return Ok(false);
        };
        if self.structure(&ctor.inductive).is_none()
            || args.len() != ctor.num_params + ctor.num_fields
        {
            return Ok(false);
        }
        let at = self.type_of(a)?;
        let bt = self.type_of(b)?;
        if !self.conv(&at, &bt)? {
            return Ok(false);
        }
        for (i, field) in args[ctor.num_params..].iter().enumerate() {
            let proj = Expr::Proj(ctor.inductive.clone(), i, Shared::new(a.clone()));
            if !self.conv(&proj, field)? {
                return Ok(false);
            }
        }
        Ok(true)
    }
}
