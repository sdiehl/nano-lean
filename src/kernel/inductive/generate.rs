use super::*;
use std::slice;

const ELIM_UNIVERSE: &str = "_rec.u";

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

    fn universe_params(&self) -> &[String] {
        &self.types[0].params
    }

    fn check_types(
        &mut self,
        tc: &mut Checker<'_>,
        all: &[String],
    ) -> Result<(Vec<Vec<Local>>, Level)> {
        let types = self.types;
        let first = &types[0];
        let mut result_level = Level::Nat(0);
        let mut indices = Vec::new();
        for (i, t) in types.iter().enumerate() {
            demand(
                t.params == first.params && t.num_params == first.num_params && t.all == all,
                "inconsistent mutual inductive parameters",
            )?;
            tc.sort(&t.ty)?;
            let rest = if i == 0 {
                let (params, rest) = tc.open_params(&t.ty, t.num_params)?;
                self.params = params;
                rest
            } else {
                tc.consume_params(&t.ty, &self.params)?
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
        Ok((indices, result_level))
    }

    fn constructor_shapes(
        &self,
        tc: &mut Checker<'_>,
        constructors: &[Constructor],
        result_level: &Level,
    ) -> Result<Shapes> {
        let first = &self.types[0];
        let mut shapes = Shapes::default();
        for (owner, t) in self.types.iter().enumerate() {
            for (index, name) in t.constructors.iter().enumerate() {
                let c = constructors
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
                let rest = tc.consume_params(&c.ty, &self.params)?;
                let (fields, ret) = tc.telescope(&rest)?;
                demand(
                    fields.len() == c.num_fields,
                    "incorrect constructor field count",
                )?;
                for (_, ty) in &fields {
                    let level = tc.sort(ty)?;
                    demand(
                        is_zero(result_level)?
                            || Level::max(level, result_level.clone()).equivalent(result_level)?,
                        "constructor field universe exceeds inductive universe",
                    )?;
                    tc.tick()?;
                    self.positive(tc, ty)?;
                    let has = occurs(ty, &self.names);
                    shapes.recursive |= has;
                    shapes.reflexive |= has && matches!(ty, Expr::Pi(..));
                }
                let Some((i, args)) = self.application(&ret) else {
                    return Err(Error("invalid constructor return type".into()));
                };
                demand(i == owner, "constructor returns the wrong inductive type")?;
                shapes.shapes.push(ConstructorShape {
                    constructor: c.clone(),
                    fields,
                    indices: args,
                    owner,
                });
            }
        }
        demand(
            shapes.shapes.len() == constructors.len(),
            "extraneous constructor",
        )?;
        Ok(shapes)
    }

    fn elimination(
        &self,
        tc: &mut Checker<'_>,
        shapes: &[ConstructorShape],
        result_level: &Level,
    ) -> Result<Elimination> {
        let universe_params = self.universe_params();
        let zero = is_zero(result_level)?;
        let zeros = universe_params
            .iter()
            .map(|p| (p.clone(), Level::Nat(0)))
            .collect();
        let definitely_positive = !is_zero(&result_level.substitute(&zeros)?)?;
        let forced =
            Recursor::forced_elimination(definitely_positive, self.types.len(), shapes.len());
        let large = if let Some(large) = forced {
            large
        } else {
            let shape = &shapes[0];
            let mut allowed = true;
            for local in &shape.fields {
                if !is_zero(&tc.sort(&local.1)?)?
                    && !shape.indices.iter().any(|e| e.aeq(&variable(local)))
                {
                    allowed = false;
                }
            }
            allowed
        };
        let k = Recursor::k_like(
            zero,
            self.types.len(),
            shapes.iter().map(|s| s.fields.len()),
        );
        let mut params = universe_params.to_vec();
        let level = if large {
            let mut fresh = ELIM_UNIVERSE.to_string();
            while universe_params.contains(&fresh) {
                fresh.push('_');
            }
            params.insert(0, fresh.clone());
            Level::Param(fresh)
        } else {
            Level::Nat(0)
        };
        Ok(Elimination { params, level, k })
    }

    fn recursors(
        &self,
        tc: &mut Checker<'_>,
        shapes: &[ConstructorShape],
        indices: &[Vec<Local>],
        elim: Elimination,
        all: &[String],
    ) -> Result<Vec<Recursor>> {
        tc.uparams.extend(elim.params.iter().cloned());
        let mut motives = Vec::new();
        let mut majors = Vec::new();
        for (t, is) in self.types.iter().zip(indices) {
            let applied = apply(
                Expr::Const(t.name.clone(), self.levels.clone()),
                self.params.iter().chain(is).map(variable),
            );
            let major = tc.fresh_local(applied);
            let mty = pis(
                is,
                pis(slice::from_ref(&major), Expr::Sort(elim.level.clone())),
            );
            motives.push(tc.fresh_local(mty));
            majors.push(major);
        }
        let mut minors = Vec::new();
        for shape in shapes {
            let ty = self.minor_premise(tc, shape, &motives)?;
            minors.push(tc.fresh_local(ty));
        }
        let prefix: Vec<_> = self
            .params
            .iter()
            .chain(&motives)
            .chain(&minors)
            .cloned()
            .collect();
        let names: Vec<_> = self.types.iter().map(|t| rec_name(&t.name)).collect();
        let levels: Vec<_> = elim.params.iter().cloned().map(Level::Param).collect();
        let mut generated = Vec::new();
        for (owner, t) in self.types.iter().enumerate() {
            let result = apply(
                variable(&motives[owner]),
                indices[owner]
                    .iter()
                    .map(variable)
                    .chain([variable(&majors[owner])]),
            );
            let tail: Vec<_> = indices[owner]
                .iter()
                .chain(slice::from_ref(&majors[owner]))
                .cloned()
                .collect();
            let mut rules = Vec::new();
            for (minor, shape) in shapes.iter().enumerate().filter(|(_, s)| s.owner == owner) {
                let mut ihs = Vec::new();
                for local in &shape.fields {
                    if let Some((xs, target, args)) = self.recursive_field(tc, &local.1)? {
                        let rec = Expr::Const(names[target].clone(), levels.clone());
                        let term = apply(variable(local), xs.iter().map(variable));
                        let call =
                            apply(rec, prefix.iter().map(variable).chain(args).chain([term]));
                        ihs.push(lambdas(&xs, call));
                    }
                }
                let rhs = apply(
                    variable(&minors[minor]),
                    shape.fields.iter().map(variable).chain(ihs),
                );
                rules.push(RecursorRule {
                    constructor: shape.constructor.name.clone(),
                    num_fields: shape.fields.len(),
                    rhs: lambdas(&prefix, lambdas(&shape.fields, rhs)),
                });
            }
            generated.push(Recursor {
                name: names[owner].clone(),
                params: elim.params.clone(),
                ty: pis(&prefix, pis(&tail, result)),
                all: all.to_vec(),
                num_params: self.types[0].num_params,
                num_indices: t.num_indices,
                num_motives: self.types.len(),
                num_minors: shapes.len(),
                k: elim.k,
                rules,
            });
        }
        Ok(generated)
    }

    fn minor_premise(
        &self,
        tc: &mut Checker<'_>,
        shape: &ConstructorShape,
        motives: &[Local],
    ) -> Result<Expr> {
        let ctor = apply(
            Expr::Const(shape.constructor.name.clone(), self.levels.clone()),
            self.params.iter().chain(&shape.fields).map(variable),
        );
        let conclusion = apply(
            variable(&motives[shape.owner]),
            shape.indices.iter().cloned().chain([ctor]),
        );
        let mut ihs = Vec::new();
        for local in &shape.fields {
            if let Some((xs, owner, args)) = self.recursive_field(tc, &local.1)? {
                let term = apply(variable(local), xs.iter().map(variable));
                let ih = pis(
                    &xs,
                    apply(variable(&motives[owner]), args.into_iter().chain([term])),
                );
                ihs.push(tc.fresh_local(ih));
            }
        }
        Ok(pis(&shape.fields, pis(&ihs, conclusion)))
    }
}

struct ConstructorShape {
    constructor: Constructor,
    fields: Vec<Local>,
    indices: Vec<Expr>,
    owner: usize,
}

#[derive(Default)]
struct Shapes {
    shapes: Vec<ConstructorShape>,
    recursive: bool,
    reflexive: bool,
}

struct Elimination {
    params: Vec<String>,
    level: Level,
    k: bool,
}

impl Environment {
    pub(super) fn generate_inductive(
        &mut self,
        block: &InductiveBlock,
        added: &mut Vec<String>,
    ) -> Result<InductiveBlock> {
        demand(!block.types.is_empty(), "empty inductive block")?;
        let first = &block.types[0];
        let all = block.type_names();
        self.reserve_names(all.iter().chain(block.constructors.iter().map(|c| &c.name)))?;
        demand(
            InductiveType::distinct_params(&first.params),
            "duplicate universe parameter",
        )?;
        let mut family = Family {
            types: &block.types,
            names: all.iter().cloned().collect(),
            levels: first.params.iter().cloned().map(Level::Param).collect(),
            params: Vec::new(),
        };
        let (indices, result_level) = family.check_types(&mut self.checker(&first.params), &all)?;
        self.insert_all(&block.types, added)?;
        let mut tc = self.checker(&first.params);
        tc.locals.extend(family.params.iter().cloned());
        for is in &indices {
            tc.locals.extend(is.iter().cloned());
        }
        let shapes = family.constructor_shapes(&mut tc, &block.constructors, &result_level)?;
        let elim = family.elimination(&mut tc, &shapes.shapes, &result_level)?;
        let recursors = family.recursors(&mut tc, &shapes.shapes, &indices, elim, &all)?;
        drop(tc);
        self.insert_all(&block.constructors, added)?;
        self.insert_all(&recursors, added)?;
        let mut types = block.types.clone();
        for t in &mut types {
            t.recursive = shapes.recursive;
            t.reflexive = shapes.reflexive;
        }
        Ok(InductiveBlock {
            types,
            constructors: block.constructors.clone(),
            recursors,
        })
    }
}
