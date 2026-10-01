use super::*;

#[derive(Clone, Debug)]
pub struct InductiveType {
    pub name: String,
    pub params: Vec<String>,
    pub ty: Expr,
    pub all: Vec<String>,
    pub constructors: Vec<String>,
    pub num_params: usize,
    pub num_indices: usize,
    pub num_nested: usize,
    pub recursive: bool,
    pub reflexive: bool,
}

#[derive(Clone, Debug)]
pub struct Constructor {
    pub name: String,
    pub params: Vec<String>,
    pub ty: Expr,
    pub inductive: String,
    pub index: usize,
    pub num_params: usize,
    pub num_fields: usize,
}

#[derive(Clone, Debug)]
pub struct RecursorRule {
    pub constructor: String,
    pub num_fields: usize,
    pub rhs: Expr,
}

#[derive(Clone, Debug)]
pub struct Recursor {
    pub name: String,
    pub params: Vec<String>,
    pub ty: Expr,
    pub all: Vec<String>,
    pub num_params: usize,
    pub num_indices: usize,
    pub num_motives: usize,
    pub num_minors: usize,
    pub k: bool,
    pub rules: Vec<RecursorRule>,
}

#[derive(Clone, Debug)]
pub struct InductiveBlock {
    pub types: Vec<InductiveType>,
    pub constructors: Vec<Constructor>,
    pub recursors: Vec<Recursor>,
}

type Local = (Name<Expr>, Expr);
type RecursiveField = (Vec<Local>, usize, Vec<Expr>);

fn demand(ok: bool, message: &str) -> Result<()> {
    if ok {
        Ok(())
    } else {
        Err(Error(message.into()))
    }
}

fn variable(local: &Local) -> Expr {
    Expr::Var(local.0.clone())
}

fn apply(mut f: Expr, args: impl IntoIterator<Item = Expr>) -> Expr {
    for arg in args {
        f = f.app(arg);
    }
    f
}

fn abstract_over(locals: &[Local], mut body: Expr, lambda: bool) -> Expr {
    for (n, ty) in locals.iter().rev() {
        body = if lambda {
            Expr::lam(n.clone(), ty.clone(), body)
        } else {
            Expr::pi(n.clone(), ty.clone(), body)
        };
    }
    body
}

pub(super) fn spine(e: &Expr) -> (Expr, Vec<Expr>) {
    let mut args = Vec::new();
    let mut head = e;
    while let Expr::App(f, a) = head {
        args.push((**a).clone());
        head = f;
    }
    args.reverse();
    (head.clone(), args)
}

fn rec_name(name: &str) -> String {
    if let Ok(mut segments) = serde_json::from_str::<Vec<serde_json::Value>>(name) {
        segments.push(serde_json::Value::String("rec".into()));
        serde_json::to_string(&segments).unwrap()
    } else {
        format!("{name}.rec")
    }
}

fn occurs(e: &Expr, names: &BTreeSet<String>) -> bool {
    fn go(e: &Expr, names: &BTreeSet<String>, seen: &mut BTreeSet<usize>) -> bool {
        let mut shared = |e: &Shared<Expr>| seen.insert(e.as_ptr() as usize) && go(e, names, seen);
        match e {
            Expr::Const(n, _) => names.contains(n),
            Expr::App(f, a) => shared(f) || shared(a),
            Expr::Proj(_, _, e) => shared(e),
            Expr::Pi(t, b) | Expr::Lam(t, b) => shared(t) || shared(b.body()),
            Expr::Let(t, v, b) => shared(t) || shared(v) || shared(b.body()),
            _ => false,
        }
    }
    go(e, names, &mut BTreeSet::new())
}

impl Checker<'_> {
    fn fresh_local(&mut self, ty: Expr) -> Local {
        let n = Name::new("x");
        self.locals.push((n.clone(), ty.clone()));
        self.scope = self.next_scope;
        self.next_scope += 1;
        (n, ty)
    }

    fn telescope(&mut self, e: &Expr) -> Result<(Vec<Local>, Expr)> {
        let mut e = self.whnf(e)?;
        let mut locals = Vec::new();
        while let Expr::Pi(ty, body) = e {
            let local = self.fresh_local((*ty).clone());
            e = self.whnf(&body.instantiate(&variable(&local)))?;
            locals.push(local);
        }
        Ok((locals, e))
    }

    fn consume_params(&mut self, ty: &Expr, params: &[Local]) -> Result<Expr> {
        let mut ty = ty.clone();
        for local in params {
            let Expr::Pi(domain, body) = self.whnf(&ty)? else {
                return Err(Error("missing inductive parameter".into()));
            };
            demand(
                self.conv(&domain, &local.1)?,
                "inductive parameter type mismatch",
            )?;
            ty = (*body.instantiate(&variable(local))).clone();
        }
        Ok(ty)
    }
}

struct Family<'a> {
    types: &'a [InductiveType],
    names: BTreeSet<String>,
    levels: Vec<Level>,
    params: Vec<Local>,
}

impl Family<'_> {
    fn application(&self, e: &Expr) -> Option<(usize, Vec<Expr>)> {
        let (head, args) = spine(e);
        let Expr::Const(name, levels) = head else {
            return None;
        };
        let i = self.types.iter().position(|t| t.name == name)?;
        if levels != self.levels || args.len() != self.params.len() + self.types[i].num_indices {
            return None;
        }
        if !args
            .iter()
            .zip(&self.params)
            .all(|(a, p)| a.aeq(&variable(p)))
        {
            return None;
        }
        let indices = args[self.params.len()..].to_vec();
        if indices.iter().any(|e| occurs(e, &self.names)) {
            return None;
        }
        Some((i, indices))
    }

    fn positive(&self, tc: &mut Checker<'_>, ty: &Expr) -> Result<()> {
        let ty = tc.whnf(ty)?;
        if !occurs(&ty, &self.names) {
            return Ok(());
        }
        match ty {
            Expr::Pi(domain, body) => {
                demand(
                    !occurs(&domain, &self.names),
                    "negative inductive occurrence",
                )?;
                let local = tc.fresh_local((*domain).clone());
                self.positive(tc, &body.instantiate(&variable(&local)))
            }
            _ => demand(
                self.application(&ty).is_some(),
                "invalid recursive inductive occurrence",
            ),
        }
    }

    fn recursive_field(&self, tc: &mut Checker<'_>, ty: &Expr) -> Result<Option<RecursiveField>> {
        let (xs, result) = tc.telescope(ty)?;
        Ok(self.application(&result).map(|(i, args)| (xs, i, args)))
    }
}

struct ConstructorShape {
    constructor: Constructor,
    fields: Vec<Local>,
    indices: Vec<Expr>,
    owner: usize,
}

impl Environment {
    pub fn declare_inductive(&mut self, block: InductiveBlock) -> Result<()> {
        let mut added = Vec::new();
        let result = self.build_inductive(&block, &mut added);
        if result.is_err() {
            for name in added {
                self.declarations.remove(&name);
                self.inductives.remove(&name);
                self.constructors.remove(&name);
                self.recursors.remove(&name);
            }
        }
        result
    }

    fn insert_generated(
        &mut self,
        name: &str,
        params: &[String],
        ty: Expr,
        added: &mut Vec<String>,
    ) -> Result<()> {
        demand(
            !self.declarations.contains_key(name),
            "duplicate inductive declaration name",
        )?;
        self.declarations.insert(
            name.into(),
            Declaration {
                params: params.to_vec(),
                ty,
                value: None,
            },
        );
        added.push(name.into());
        Ok(())
    }

    fn build_inductive(&mut self, block: &InductiveBlock, added: &mut Vec<String>) -> Result<()> {
        demand(!block.types.is_empty(), "empty inductive block")?;
        if block.types.iter().any(|t| t.num_nested != 0) {
            return Err(Error("unsupported: nested inductive block".into()));
        }
        let first = &block.types[0];
        let all: Vec<_> = block.types.iter().map(|t| t.name.clone()).collect();
        let mut reserved = BTreeSet::new();
        for n in all
            .iter()
            .chain(block.constructors.iter().map(|c| &c.name))
            .chain(block.recursors.iter().map(|r| &r.name))
        {
            demand(
                reserved.insert(n.clone()) && !self.declarations.contains_key(n),
                "duplicate inductive declaration name",
            )?;
        }
        demand(
            first.params.iter().collect::<BTreeSet<_>>().len() == first.params.len(),
            "duplicate universe parameter",
        )?;
        let mut tc = Checker::new(self);
        tc.uparams = first.params.iter().cloned().collect();
        let mut family = Family {
            types: &block.types,
            names: all.iter().cloned().collect(),
            levels: first.params.iter().cloned().map(Level::Param).collect(),
            params: Vec::new(),
        };
        let mut result_level = Level::Nat(0);
        let mut indices = Vec::new();
        for (i, t) in block.types.iter().enumerate() {
            demand(
                t.params == first.params && t.num_params == first.num_params && t.all == all,
                "inconsistent mutual inductive parameters",
            )?;
            tc.sort(&t.ty)?;
            let rest = if i == 0 {
                let mut rest = t.ty.clone();
                for _ in 0..t.num_params {
                    let Expr::Pi(domain, body) = tc.whnf(&rest)? else {
                        return Err(Error("missing inductive parameter".into()));
                    };
                    let local = tc.fresh_local((*domain).clone());
                    rest = (*body.instantiate(&variable(&local))).clone();
                    family.params.push(local);
                }
                rest
            } else {
                tc.consume_params(&t.ty, &family.params)?
            };
            let (is, result) = tc.telescope(&rest)?;
            demand(is.len() == t.num_indices, "incorrect inductive index count")?;
            let Expr::Sort(level) = result else {
                return Err(Error("inductive type does not end in a sort".into()));
            };
            if i == 0 {
                result_level = level;
            } else {
                demand(
                    result_level.equivalent(&level)?,
                    "mutual inductive universe mismatch",
                )?;
            }
            indices.push(is);
        }
        drop(tc);
        for t in &block.types {
            self.insert_generated(&t.name, &t.params, t.ty.clone(), added)?;
        }
        let mut tc = Checker::new(self);
        tc.uparams = first.params.iter().cloned().collect();
        tc.locals.extend(family.params.iter().cloned());
        for is in &indices {
            tc.locals.extend(is.iter().cloned());
        }
        let mut shapes = Vec::new();
        let mut recursive = false;
        let mut reflexive = false;
        for (owner, t) in block.types.iter().enumerate() {
            for (index, name) in t.constructors.iter().enumerate() {
                let c = block
                    .constructors
                    .iter()
                    .find(|c| c.name == *name)
                    .ok_or_else(|| Error("missing constructor".into()))?;
                demand(
                    c.inductive == t.name
                        && c.index == index
                        && c.params == first.params
                        && c.num_params == first.num_params,
                    "incorrect constructor metadata",
                )?;
                tc.sort(&c.ty)?;
                let rest = tc.consume_params(&c.ty, &family.params)?;
                let (fields, ret) = tc.telescope(&rest)?;
                demand(
                    fields.len() == c.num_fields,
                    "incorrect constructor field count",
                )?;
                for (_, ty) in &fields {
                    let level = tc.sort(ty)?;
                    demand(
                        result_level.equivalent(&Level::Nat(0))?
                            || Level::max(level, result_level.clone()).equivalent(&result_level)?,
                        "constructor field universe exceeds inductive universe",
                    )?;
                    tc.tick()?;
                    family.positive(&mut tc, ty)?;
                    let has = occurs(ty, &family.names);
                    recursive |= has;
                    reflexive |= has && matches!(ty, Expr::Pi(..));
                }
                let Some((i, args)) = family.application(&ret) else {
                    return Err(Error("invalid constructor return type".into()));
                };
                demand(i == owner, "constructor returns the wrong inductive type")?;
                shapes.push(ConstructorShape {
                    constructor: c.clone(),
                    fields,
                    indices: args,
                    owner,
                });
            }
        }
        demand(
            shapes.len() == block.constructors.len(),
            "extraneous constructor",
        )?;
        for t in &block.types {
            demand(
                t.recursive == recursive && t.reflexive == reflexive,
                "incorrect inductive recursion metadata",
            )?;
        }
        let zero = result_level.equivalent(&Level::Nat(0))?;
        let zeros = first
            .params
            .iter()
            .map(|p| (p.clone(), Level::Nat(0)))
            .collect();
        let definitely_positive = !result_level
            .substitute(&zeros)?
            .equivalent(&Level::Nat(0))?;
        let large = if definitely_positive {
            true
        } else if block.types.len() > 1 || shapes.len() > 1 {
            false
        } else if shapes.is_empty() {
            true
        } else {
            let shape = &shapes[0];
            let mut allowed = true;
            for local in &shape.fields {
                if !tc.sort(&local.1)?.equivalent(&Level::Nat(0))?
                    && !shape.indices.iter().any(|e| e.aeq(&variable(local)))
                {
                    allowed = false;
                }
            }
            allowed
        };
        let k = zero && block.types.len() == 1 && shapes.len() == 1 && shapes[0].fields.is_empty();
        demand(
            block.recursors.len() == block.types.len(),
            "incorrect recursor count",
        )?;
        let mut recs = Vec::new();
        for t in &block.types {
            let r = block
                .recursors
                .iter()
                .find(|r| r.name == rec_name(&t.name))
                .ok_or_else(|| Error("missing recursor".into()))?;
            demand(
                r.all == all
                    && r.num_params == first.num_params
                    && r.num_indices == t.num_indices
                    && r.num_motives == block.types.len()
                    && r.num_minors == shapes.len()
                    && r.k == k,
                "incorrect recursor metadata",
            )?;
            recs.push(r);
        }
        let rparams = &recs[0].params;
        let elim = if large {
            demand(
                rparams.len() == first.params.len() + 1
                    && rparams[1..] == first.params
                    && !first.params.contains(&rparams[0]),
                "incorrect recursor universe parameters",
            )?;
            Level::Param(rparams[0].clone())
        } else {
            demand(
                *rparams == first.params,
                "invalid large elimination from proposition",
            )?;
            Level::Nat(0)
        };
        for r in &recs {
            demand(
                r.params == *rparams,
                "inconsistent recursor universe parameters",
            )?;
        }
        tc.uparams.extend(rparams.iter().cloned());
        let mut motives = Vec::new();
        let mut majors = Vec::new();
        for (i, t) in block.types.iter().enumerate() {
            let applied = apply(
                Expr::Const(t.name.clone(), family.levels.clone()),
                family.params.iter().chain(&indices[i]).map(variable),
            );
            let major = tc.fresh_local(applied);
            let mty = abstract_over(
                &indices[i],
                abstract_over(
                    std::slice::from_ref(&major),
                    Expr::Sort(elim.clone()),
                    false,
                ),
                false,
            );
            motives.push(tc.fresh_local(mty));
            majors.push(major);
        }
        let mut minors = Vec::new();
        for shape in &shapes {
            let ctor = apply(
                Expr::Const(shape.constructor.name.clone(), family.levels.clone()),
                family.params.iter().chain(&shape.fields).map(variable),
            );
            let conclusion = apply(
                variable(&motives[shape.owner]),
                shape.indices.iter().cloned().chain([ctor]),
            );
            let mut ihs = Vec::new();
            for local in &shape.fields {
                if let Some((xs, owner, args)) = family.recursive_field(&mut tc, &local.1)? {
                    let term = apply(variable(local), xs.iter().map(variable));
                    let ih = abstract_over(
                        &xs,
                        apply(variable(&motives[owner]), args.into_iter().chain([term])),
                        false,
                    );
                    ihs.push(tc.fresh_local(ih));
                }
            }
            let ty = abstract_over(&shape.fields, abstract_over(&ihs, conclusion, false), false);
            minors.push(tc.fresh_local(ty));
        }
        let prefix: Vec<_> = family
            .params
            .iter()
            .chain(&motives)
            .chain(&minors)
            .cloned()
            .collect();
        let mut generated = Vec::new();
        for (owner, r) in recs.iter().enumerate() {
            let result = apply(
                variable(&motives[owner]),
                indices[owner]
                    .iter()
                    .map(variable)
                    .chain([variable(&majors[owner])]),
            );
            let tail: Vec<_> = indices[owner]
                .iter()
                .chain(std::slice::from_ref(&majors[owner]))
                .cloned()
                .collect();
            let ty = abstract_over(&prefix, abstract_over(&tail, result, false), false);
            let mut rules = Vec::new();
            for (minor, shape) in shapes.iter().enumerate().filter(|(_, s)| s.owner == owner) {
                let mut ihs = Vec::new();
                for local in &shape.fields {
                    if let Some((xs, target, args)) = family.recursive_field(&mut tc, &local.1)? {
                        let rec = Expr::Const(
                            recs[target].name.clone(),
                            rparams.iter().cloned().map(Level::Param).collect(),
                        );
                        let term = apply(variable(local), xs.iter().map(variable));
                        let call =
                            apply(rec, prefix.iter().map(variable).chain(args).chain([term]));
                        ihs.push(abstract_over(&xs, call, true));
                    }
                }
                let rhs = apply(
                    variable(&minors[minor]),
                    shape.fields.iter().map(variable).chain(ihs),
                );
                let rhs = abstract_over(&prefix, abstract_over(&shape.fields, rhs, true), true);
                rules.push(RecursorRule {
                    constructor: shape.constructor.name.clone(),
                    num_fields: shape.fields.len(),
                    rhs,
                });
            }
            generated.push(Recursor {
                ty,
                rules,
                ..(*r).clone()
            });
        }
        drop(tc);
        for c in &block.constructors {
            self.insert_generated(&c.name, &c.params, c.ty.clone(), added)?;
        }
        for r in &generated {
            self.insert_generated(&r.name, &r.params, r.ty.clone(), added)?;
        }
        let mut tc = Checker::new(self);
        tc.uparams = rparams.iter().cloned().collect();
        for (actual, expected) in recs.iter().zip(&generated) {
            tc.sort(&expected.ty)?;
            tc.sort(&actual.ty)?;
            demand(
                tc.conv(&actual.ty, &expected.ty)?,
                "incorrect recursor type",
            )?;
            demand(
                actual.rules.len() == expected.rules.len(),
                "incorrect recursor rule count",
            )?;
            for (a, e) in actual.rules.iter().zip(&expected.rules) {
                demand(
                    a.constructor == e.constructor && a.num_fields == e.num_fields,
                    "incorrect recursor rule metadata",
                )?;
                let ty = tc.infer(&e.rhs)?;
                tc.check(&a.rhs, &ty)?;
                demand(
                    tc.conv(&a.rhs, &e.rhs)?,
                    "incorrect recursor computation rule",
                )?;
            }
        }
        drop(tc);
        for t in &block.types {
            self.inductives.insert(t.name.clone(), t.clone());
        }
        for c in &block.constructors {
            self.constructors.insert(c.name.clone(), c.clone());
        }
        for r in generated {
            self.recursors.insert(r.name.clone(), r);
        }
        Ok(())
    }
}

impl Checker<'_> {
    pub(super) fn reduce_recursor(&mut self, head: &Expr, args: &[Expr]) -> Result<Option<Expr>> {
        let Expr::Const(name, levels) = head else {
            return Ok(None);
        };
        let Some(rec) = self.env.recursors.get(name).cloned() else {
            return Ok(None);
        };
        let major_pos = rec.num_params + rec.num_motives + rec.num_minors + rec.num_indices;
        if args.len() <= major_pos {
            return Ok(None);
        }
        let subst = self.level_arguments(&rec.params, levels)?;
        let major = self.whnf(&args[major_pos])?;
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
        {
            let info = self.env.constructors[&rule.constructor].clone();
            if self.structure(&info.inductive).is_some() {
                let ty = self.infer(&major)?;
                let ty = self.whnf(&ty)?;
                let (head, params) = spine(&ty);
                if matches!(&head, Expr::Const(n, _) if *n == info.inductive)
                    && !self.sort(&ty)?.equivalent(&Level::Nat(0))?
                    && params.len() == info.num_params
                {
                    let Expr::Const(_, us) = head else {
                        unreachable!()
                    };
                    ctor = Expr::Const(info.name.clone(), us);
                    fields = params;
                    fields.extend((0..info.num_fields).map(|i| {
                        Expr::Proj(info.inductive.clone(), i, Shared::new(major.clone()))
                    }));
                }
            }
        }
        if rec.k
            && !matches!(&ctor, Expr::Const(n, _) if rec.rules.iter().any(|r| r.constructor == *n))
        {
            let rule = &rec.rules[0];
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
                args[..rec.num_params].iter().cloned(),
            );
            let actual = self.infer(&major)?;
            let expected = self.infer(&replacement)?;
            if !self.conv(&actual, &expected)? {
                return Ok(None);
            }
            ctor = Expr::Const(rule.constructor.clone(), us);
            fields = args[..rec.num_params].to_vec();
        }
        let Expr::Const(name, _) = ctor else {
            return Ok(None);
        };
        let Some(rule) = rec.rules.iter().find(|r| r.constructor == name) else {
            return Ok(None);
        };
        if fields.len() != rec.num_params + rule.num_fields {
            return Ok(None);
        }
        let rhs = rule.rhs.substitute_levels(&subst)?;
        let prefix = rec.num_params + rec.num_motives + rec.num_minors;
        Ok(Some(apply(
            rhs,
            args[..prefix]
                .iter()
                .chain(&fields[rec.num_params..])
                .chain(&args[major_pos + 1..])
                .cloned(),
        )))
    }
}

impl Checker<'_> {
    fn structure(&self, name: &str) -> Option<Constructor> {
        let info = self.env.inductives.get(name)?;
        if info.recursive || info.num_indices != 0 || info.constructors.len() != 1 {
            return None;
        }
        self.env.constructors.get(&info.constructors[0]).cloned()
    }

    pub(super) fn unit_like(&mut self, ty: &Expr) -> Result<bool> {
        let ty = self.whnf(ty)?;
        let (head, _) = spine(&ty);
        Ok(
            matches!(head, Expr::Const(n, _) if self.structure(&n).is_some_and(|c| c.num_fields == 0)),
        )
    }

    pub(super) fn infer_projection(
        &mut self,
        name: &str,
        index: usize,
        e: &Shared<Expr>,
    ) -> Result<Expr> {
        let ty = self.infer_shared(e)?;
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
        let mut field_ty = ctor.ty.substitute_levels(&subst)?;
        for arg in args.into_iter().take(ctor.num_params) {
            let Expr::Pi(_, body) = self.whnf(&field_ty)? else {
                return Err(Error("invalid constructor telescope".into()));
            };
            field_ty = (*body.instantiate(&arg)).clone();
        }
        let prop = self.sort(&ty)?.equivalent(&Level::Nat(0))?;
        for i in 0..index {
            let Expr::Pi(domain, body) = self.whnf(&field_ty)? else {
                return Err(Error("invalid projection telescope".into()));
            };
            let (n, opened) = body.unbind_ref();
            let depends = opened.fv().contains(&n.to_any().unwrap());
            if prop && depends {
                demand(
                    self.sort(&domain)?.equivalent(&Level::Nat(0))?,
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
                self.sort(&domain)?.equivalent(&Level::Nat(0))?,
                "projection eliminates proposition into data",
            )?;
        }
        Ok((*domain).clone())
    }

    pub(super) fn structure_eta(&mut self, a: &Expr, b: &Expr) -> Result<bool> {
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
        let at = self.infer(a)?;
        let bt = self.infer(b)?;
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
