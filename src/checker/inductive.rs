use super::Tc;
use crate::kernel;
use crate::kernel::export_validation::{
    ExportDependency, ExportSession, TargetKind, validate_export_dependencies,
};
use crate::kernel::{Expr as KernelExpr, Level as KernelLevel};
use crate::resource::{Budget, stack_exhausted, stack_floor};
use crate::term::decl::Declar;
use crate::term::expr::Expr;
use crate::term::intern::{Block, Store};
use crate::term::level::Level;
use crate::term::name::Name;
use crate::term::outcome::{Decline, Failure, R};
use crate::term::ptr::{ExprPtr, LevelPtr, LevelsPtr, NamePtr};
use crate::term::{FxHashMap, FxHashSet};
use crate::{ensure, reject};
use std::cell::Cell;
use std::collections::BTreeSet;
use std::ptr;
use std::rc::Rc;
#[cfg(feature = "vstats")]
use std::sync::atomic::{AtomicU64, Ordering::Relaxed};
#[cfg(feature = "vstats")]
use std::time::Instant;
use unbound::prelude::{Name as KernelName, Shared, bind};

const CONVERT_CACHE_LIMIT: usize = 65536;

pub struct Adapter<'a> {
    store: &'a Store<'a>,
    session: ExportSession,
    convert: Convert<'a>,
}

impl<'a> Adapter<'a> {
    pub fn new(store: &'a Store<'a>) -> Self {
        Self {
            store,
            session: ExportSession::default(),
            convert: Convert::new(),
        }
    }
}

#[cfg(feature = "vstats")]
pub static BLOCKS: [[AtomicU64; 2]; 2] = [const { [const { AtomicU64::new(0) }; 2] }; 2];

#[cfg(feature = "vstats")]
struct BlockTimer(usize, Instant);

#[cfg(feature = "vstats")]
impl Drop for BlockTimer {
    fn drop(&mut self) {
        let [n, t] = &BLOCKS[self.0];
        n.fetch_add(1, Relaxed);
        t.fetch_add(self.1.elapsed().as_nanos() as u64, Relaxed);
    }
}

impl<'t, 'a: 't> Tc<'t, 'a> {
    pub(crate) fn check_inductive(&mut self, idx: u32, d: Declar<'t>) -> R<()> {
        let block = *self
            .ctx
            .store
            .blocks
            .get(&d.name())
            .expect("imported block");
        if block.start != idx {
            return Ok(());
        }
        let native = self.native_block(block);
        #[cfg(feature = "vstats")]
        let _timer = BlockTimer(usize::from(!native), Instant::now());
        if !native {
            return self.check_existing(idx);
        }
        let result = self.check_block(block);
        if result.is_ok()
            || !self.nested_block(block)
            || !matches!(self.fail, Some(Failure::Rejected(_)))
        {
            return result;
        }
        // A nested block the native expansion turns down is re-decided by the reference path,
        // which carries Lean's own reasons.
        self.fail = None;
        self.check_existing(idx)
    }

    pub(super) fn check_existing(&mut self, idx: u32) -> R<()> {
        let d = self.ctx.store.declars[idx as usize];
        let block = self
            .ctx
            .store
            .blocks
            .get(&d.name())
            .copied()
            .unwrap_or(Block {
                start: idx,
                types_end: idx,
                ctors_end: idx,
                end: idx + 1,
            });
        if let Some(adapter) = self.adapter.as_mut() {
            assert!(
                ptr::eq(adapter.store, self.ctx.store),
                "adapter belongs to another export"
            );
            adapter.session.begin(idx);
        }
        let dependencies = self.inductive_dependencies(block)?;
        let kind = match d {
            Declar::Thm(..) => TargetKind::Theorem,
            Declar::Opaque(..) => TargetKind::Opaque,
            _ => TargetKind::Definition,
        };
        if let Some(adapter) = self.adapter.as_mut() {
            let result = bridged(adapter, dependencies, idx, kind, &mut self.steps_left);
            return result.map_err(|f| self.failed(f));
        }
        let mut convert = Convert::new();
        let store = self.ctx.store;
        let mut prefix = Vec::with_capacity(dependencies.len());
        for index in dependencies {
            self.tick()?;
            let dependency = convert
                .declaration(store, store.declars[index as usize], false)
                .map_err(|f| self.failed(f))?;
            prefix.push(dependency);
        }
        let target = convert
            .declaration(store, d, true)
            .map_err(|f| self.failed(f))?;
        let result = with_work(&mut self.steps_left, |work| {
            validate_export_dependencies(prefix, target, kind, work)
        });
        accept(result).map_err(|f| self.failed(f))
    }

    fn inductive_dependencies(&mut self, target: Block) -> R<BTreeSet<u32>> {
        let store = self.ctx.store;
        let mut declarations = Vec::new();
        let mut expressions = Vec::new();
        let mut seen = FxHashSet::default();
        let mut needed = BTreeSet::new();
        for d in &store.declars[target.start as usize..target.end as usize] {
            roots(*d, &mut expressions, true);
        }
        loop {
            while let Some(e) = expressions.pop() {
                self.tick()?;
                if !seen.insert(e) {
                    continue;
                }
                match *e {
                    Expr::Const { name, .. } => declarations.push(name),
                    Expr::App { fun, arg, .. } => expressions.extend([fun, arg]),
                    Expr::Pi { ty, body, .. } | Expr::Lam { ty, body, .. } => {
                        expressions.extend([ty, body]);
                    }
                    Expr::Let { data, .. } => expressions.extend([data.ty, data.val, data.body]),
                    Expr::Proj { name, e, .. } => {
                        declarations.push(name);
                        expressions.push(e);
                    }
                    Expr::NatLit { .. } => declarations.extend(self.names.nat),
                    Expr::StrLit { .. } => declarations.extend(
                        [
                            self.names.string,
                            self.names.string_of_list,
                            self.names.char,
                            self.names.char_of_nat,
                            self.names.list_nil,
                            self.names.list_cons,
                        ]
                        .into_iter()
                        .flatten(),
                    ),
                    _ => (),
                }
            }
            let Some(name) = declarations.pop() else {
                break;
            };
            let Some(index) = name.decl_idx() else {
                reject!(self, "unknown dependency {name}")
            };
            ensure!(
                self,
                index < target.end,
                "inductive dependency is out of scope"
            );
            if index >= target.start {
                continue;
            }
            let dependency = store.blocks.get(&name).map_or(index, |block| block.start);
            if self
                .adapter
                .as_ref()
                .is_some_and(|a| a.session.contains(dependency))
            {
                continue;
            }
            if let Some(block) = store.blocks.get(&name) {
                if needed.insert(block.start) {
                    for d in &store.declars[block.start as usize..block.end as usize] {
                        roots(*d, &mut expressions, false);
                    }
                }
            } else if needed.insert(index) {
                let d = store.declars[index as usize];
                roots(d, &mut expressions, false);
                if matches!(d, Declar::Quot(_)) {
                    declarations.extend(self.names.eq);
                    for n in [self.names.quot, self.names.quot_mk].into_iter().flatten() {
                        if n.decl_idx().is_some_and(|i| i < index) {
                            declarations.push(n);
                        }
                    }
                }
            }
        }
        Ok(needed)
    }
}

fn bridged(
    adapter: &mut Adapter<'_>,
    dependencies: BTreeSet<u32>,
    idx: u32,
    kind: TargetKind,
    steps_left: &mut u64,
) -> Result<(), Failure> {
    let store = adapter.store;
    let mut prefix = Vec::with_capacity(dependencies.len());
    for index in dependencies {
        let dependency = store.declars[index as usize];
        let converted = adapter.convert.declaration(store, dependency, false)?;
        prefix.push((index, converted));
    }
    let target = adapter
        .convert
        .declaration(store, store.declars[idx as usize], true)?;
    let result = with_work(steps_left, |work| {
        adapter.session.validate(prefix, target, kind, work)
    });
    if adapter.convert.expressions.len() > CONVERT_CACHE_LIMIT {
        adapter.convert = Convert::new();
    }
    accept(result)
}

fn with_work(
    steps_left: &mut u64,
    validate: impl FnOnce(Rc<Cell<u64>>) -> Result<(), kernel::Error>,
) -> Result<(), kernel::Error> {
    let work = Rc::new(Cell::new(*steps_left));
    let result = validate(work.clone());
    *steps_left = work.get();
    result
}

fn accept(result: Result<(), kernel::Error>) -> Result<(), Failure> {
    match result {
        Ok(()) => Ok(()),
        Err(error @ kernel::Error::Rejected(_)) => Err(Failure::Rejected(format!(
            "declaration validation: {error}"
        ))),
        Err(error) => Err(Failure::Declined(Decline::Unsupported(format!(
            "validation: {error}"
        )))),
    }
}

fn roots<'a>(d: Declar<'a>, out: &mut Vec<ExprPtr<'a>>, target: bool) {
    out.push(d.ty());
    // Opaque dependency bodies cannot reduce and are validated by their own checks.
    if target && let Declar::Opaque(_, v) = d {
        out.push(v);
    }
    if let Some((v, _)) = d.unfoldable() {
        out.push(v);
    }
    if let Declar::Rec(r) = d {
        out.extend(r.rules.iter().map(|r| r.rhs));
    }
}

struct Convert<'a> {
    names: FxHashMap<NamePtr<'a>, String>,
    levels: FxHashMap<LevelPtr<'a>, KernelLevel>,
    expressions: FxHashMap<ExprPtr<'a>, Shared<KernelExpr>>,
    floor: usize,
}

impl<'a> Convert<'a> {
    fn new() -> Self {
        Self {
            names: FxHashMap::default(),
            levels: FxHashMap::default(),
            expressions: FxHashMap::default(),
            floor: stack_floor(),
        }
    }

    fn declaration(
        &mut self,
        store: &Store<'a>,
        d: Declar<'a>,
        target: bool,
    ) -> Result<ExportDependency, Failure> {
        Ok(match d {
            Declar::Ind(_) | Declar::Ctor(_) | Declar::Rec(_) => {
                ExportDependency::Inductive(self.block(store, store.blocks[&d.name()])?)
            }
            Declar::Quot(info) => ExportDependency::Quotient {
                name: self.name(info.name),
                params: self.params(info.uparams)?,
                ty: (*self.expr(info.ty)?).clone(),
                kind: match Some(info.name) {
                    n if n == store.names.quot => "type",
                    n if n == store.names.quot_mk => "ctor",
                    n if n == store.names.quot_lift => "lift",
                    n if n == store.names.quot_ind => "ind",
                    _ => return Err(rejected("invalid quotient dependency")),
                },
            },
            _ => ExportDependency::Ordinary {
                name: self.name(d.name()),
                params: self.params(d.uparams())?,
                ty: (*self.expr(d.ty())?).clone(),
                value: match d {
                    Declar::Opaque(_, v) if target => Some((*self.expr(v)?).clone()),
                    _ => match d.unfoldable() {
                        Some((v, _)) => Some((*self.expr(v)?).clone()),
                        None => None,
                    },
                },
            },
        })
    }

    fn name(&mut self, name: NamePtr<'a>) -> String {
        self.names
            .entry(name)
            .or_insert_with(|| {
                let mut segments = Vec::new();
                let mut n = name;
                loop {
                    match n.kind {
                        Name::Anon => break,
                        Name::Str(p, s, _) => {
                            segments.push(serde_json::Value::String(s.s.into()));
                            n = p;
                        }
                        Name::Num(p, i, _) => {
                            segments.push(serde_json::Value::from(i));
                            n = p;
                        }
                    }
                }
                segments.reverse();
                serde_json::to_string(&segments).expect("name encoding")
            })
            .clone()
    }

    fn level(&mut self, l: LevelPtr<'a>) -> Result<KernelLevel, Failure> {
        if let Some(v) = self.levels.get(&l) {
            return Ok(v.clone());
        }
        let v = match *l {
            Level::Zero => KernelLevel::Nat(0),
            Level::Param(n, _) => KernelLevel::Param(self.name(n)),
            Level::Succ(l, _) => self
                .level(l)?
                .succ()
                .map_err(|e| rejected(&e.to_string()))?,
            Level::Max(a, b, _) => KernelLevel::max(self.level(a)?, self.level(b)?),
            Level::IMax(a, b, _) => KernelLevel::imax(self.level(a)?, self.level(b)?),
        };
        self.levels.insert(l, v.clone());
        Ok(v)
    }

    fn params(&mut self, levels: LevelsPtr<'a>) -> Result<Vec<String>, Failure> {
        levels
            .iter()
            .map(|l| match **l {
                Level::Param(n, _) => Ok(self.name(n)),
                _ => Err(rejected("invalid universe parameter")),
            })
            .collect()
    }

    fn expr(&mut self, e: ExprPtr<'a>) -> Result<Shared<KernelExpr>, Failure> {
        if let Some(v) = self.expressions.get(&e) {
            return Ok(v.clone());
        }
        if stack_exhausted(self.floor) {
            return Err(Failure::Declined(Decline::Exhausted(Budget::Stack)));
        }
        let out = match *e {
            Expr::Var { idx, .. } => KernelExpr::Var(KernelName::bound(usize::from(idx), 0)),
            Expr::Sort { level, .. } => KernelExpr::Sort(self.level(level)?),
            Expr::Const { name, levels, .. } => KernelExpr::Const(
                self.name(name),
                levels
                    .iter()
                    .map(|l| self.level(*l))
                    .collect::<Result<_, _>>()?,
            ),
            Expr::App { fun, arg, .. } => KernelExpr::App(self.expr(fun)?, self.expr(arg)?),
            Expr::Lam { ty, body, .. } => {
                KernelExpr::Lam(self.expr(ty)?, bind(KernelName::new("x"), self.expr(body)?))
            }
            Expr::Pi { ty, body, .. } => {
                KernelExpr::Pi(self.expr(ty)?, bind(KernelName::new("x"), self.expr(body)?))
            }
            Expr::Let { data, .. } => KernelExpr::Let(
                self.expr(data.ty)?,
                self.expr(data.val)?,
                bind(KernelName::new("x"), self.expr(data.body)?),
            ),
            Expr::Proj { name, idx, e, .. } => {
                KernelExpr::Proj(self.name(name), usize::from(idx), self.expr(e)?)
            }
            Expr::NatLit { n, .. } => KernelExpr::nat(n.as_ref().clone()),
            Expr::StrLit { s, .. } => KernelExpr::Str(s.s.into()),
            Expr::Local { .. } => return Err(rejected("local in imported inductive declaration")),
        };
        let out = Shared::new(out);
        self.expressions.insert(e, out.clone());
        Ok(out)
    }

    fn block(&mut self, store: &Store<'a>, b: Block) -> Result<kernel::InductiveBlock, Failure> {
        let mut out = kernel::InductiveBlock {
            types: Vec::new(),
            constructors: Vec::new(),
            recursors: Vec::new(),
        };
        for d in &store.declars[b.start as usize..b.end as usize] {
            match *d {
                Declar::Ind(i) => out.types.push(kernel::InductiveType {
                    name: self.name(i.info.name),
                    params: self.params(i.info.uparams)?,
                    ty: (*self.expr(i.info.ty)?).clone(),
                    all: i.all.iter().map(|n| self.name(*n)).collect(),
                    constructors: i.ctors.iter().map(|n| self.name(*n)).collect(),
                    num_params: i.num_params.into(),
                    num_indices: i.num_indices.into(),
                    num_nested: i.num_nested,
                    recursive: i.is_rec,
                    reflexive: i.is_reflexive,
                }),
                Declar::Ctor(c) => out.constructors.push(kernel::Constructor {
                    name: self.name(c.info.name),
                    params: self.params(c.info.uparams)?,
                    ty: (*self.expr(c.info.ty)?).clone(),
                    inductive: self.name(c.induct),
                    index: c.cidx.into(),
                    num_params: c.num_params.into(),
                    num_fields: c.num_fields.into(),
                }),
                Declar::Rec(r) => {
                    let mut rules = Vec::with_capacity(r.rules.len());
                    for rule in r.rules {
                        rules.push(kernel::RecursorRule {
                            constructor: self.name(rule.ctor),
                            num_fields: rule.nfields.into(),
                            rhs: (*self.expr(rule.rhs)?).clone(),
                        });
                    }
                    out.recursors.push(kernel::Recursor {
                        name: self.name(r.info.name),
                        params: self.params(r.info.uparams)?,
                        ty: (*self.expr(r.info.ty)?).clone(),
                        all: r.all.iter().map(|n| self.name(*n)).collect(),
                        num_params: r.num_params.into(),
                        num_indices: r.num_indices.into(),
                        num_motives: r.num_motives.into(),
                        num_minors: r.num_minors.into(),
                        k: r.is_k,
                        rules,
                    });
                }
                _ => unreachable!("non-inductive block member"),
            }
        }
        Ok(out)
    }
}

fn rejected(message: &str) -> Failure {
    Failure::Rejected(message.to_owned())
}
