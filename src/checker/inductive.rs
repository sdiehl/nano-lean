use super::Tc;
use crate::kernel;
use crate::kernel::export_validation::{
    ExportDependency, ExportSession, validate_export_dependencies,
};
use crate::term::decl::Declar;
use crate::term::expr::Expr;
use crate::term::intern::{Block, Store};
use crate::term::level::Level;
use crate::term::name::Name;
use crate::term::ptr::{ExprPtr, LevelPtr, LevelsPtr, NamePtr};
use crate::term::{FxHashMap, FxHashSet};
use crate::{Expr as OldExpr, Level as OldLevel};
use crate::{ensure, reject, unsupported};
use std::cell::Cell;
use std::collections::BTreeSet;
use std::ptr;
use std::rc::Rc;
#[cfg(feature = "vstats")]
use std::sync::atomic::{AtomicU64, Ordering::Relaxed};
#[cfg(feature = "vstats")]
use std::time::Instant;
use unbound::prelude::{Name as OldName, Shared, bind};

const CONVERT_CACHE_LIMIT: usize = 65536;
const STACK_RED_ZONE: usize = 128 << 10;
const STACK_GROWTH: usize = 2 << 20;

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
            convert: Convert::default(),
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
    pub(crate) fn check_inductive(&mut self, idx: u32, d: Declar<'t>) {
        let block = *self
            .ctx
            .store
            .blocks
            .get(&d.name())
            .expect("imported block");
        if block.start != idx {
            return;
        }
        let native = self.native_block(block);
        #[cfg(feature = "vstats")]
        let _timer = BlockTimer(usize::from(!native), Instant::now());
        if native {
            self.check_block(block);
        } else {
            self.check_existing(idx);
        }
    }

    pub(super) fn check_existing(&mut self, idx: u32) {
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
        let dependencies = self.inductive_dependencies(block);
        let theorem = matches!(d, Declar::Thm(..));
        if let Some(adapter) = self.adapter.as_mut() {
            let prefix: Vec<_> = dependencies
                .into_iter()
                .map(|index| {
                    let dependency = adapter.store.declars[index as usize];
                    (
                        index,
                        adapter
                            .convert
                            .declaration(adapter.store, dependency, false),
                    )
                })
                .collect();
            let target = adapter.convert.declaration(
                adapter.store,
                adapter.store.declars[idx as usize],
                true,
            );
            let result = with_work(&mut self.steps_left, |work| {
                adapter.session.validate(prefix, target, theorem, work)
            });
            if adapter.convert.expressions.len() > CONVERT_CACHE_LIMIT {
                adapter.convert = Convert::default();
            }
            return accept(result);
        }
        let mut convert = Convert::default();
        let store = self.ctx.store;
        let prefix: Vec<_> = dependencies
            .into_iter()
            .map(|index| {
                self.tick();
                convert.declaration(store, store.declars[index as usize], false)
            })
            .collect();
        let target = convert.declaration(store, d, true);
        let result = with_work(&mut self.steps_left, |work| {
            validate_export_dependencies(prefix, target, theorem, work)
        });
        accept(result);
    }

    fn inductive_dependencies(&mut self, target: Block) -> BTreeSet<u32> {
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
                self.tick();
                if !seen.insert(e) {
                    continue;
                }
                match *e {
                    Expr::Const { name, .. } => declarations.push(name),
                    Expr::App { fun, arg, .. } => expressions.extend([fun, arg]),
                    Expr::Pi { ty, body, .. } | Expr::Lam { ty, body, .. } => {
                        expressions.extend([ty, body])
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
            let index = name
                .decl_idx()
                .unwrap_or_else(|| reject!("unknown dependency {name}"));
            ensure!(index < target.end, "inductive dependency is out of scope");
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
        needed
    }
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

fn accept(result: Result<(), kernel::Error>) {
    match result {
        Ok(()) => {}
        Err(error @ kernel::Error::Rejected(_)) => reject!("declaration validation: {error}"),
        Err(error) => unsupported!("validation: {error}"),
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

#[derive(Default)]
struct Convert<'a> {
    names: FxHashMap<NamePtr<'a>, String>,
    levels: FxHashMap<LevelPtr<'a>, OldLevel>,
    expressions: FxHashMap<ExprPtr<'a>, Shared<OldExpr>>,
}

impl<'a> Convert<'a> {
    fn declaration(&mut self, store: &Store<'a>, d: Declar<'a>, target: bool) -> ExportDependency {
        match d {
            Declar::Ind(_) | Declar::Ctor(_) | Declar::Rec(_) => {
                ExportDependency::Inductive(self.block(store, store.blocks[&d.name()]))
            }
            Declar::Quot(info) => ExportDependency::Quotient {
                name: self.name(info.name),
                params: self.params(info.uparams),
                ty: (*self.expr(info.ty)).clone(),
                kind: match Some(info.name) {
                    n if n == store.names.quot => "type",
                    n if n == store.names.quot_mk => "ctor",
                    n if n == store.names.quot_lift => "lift",
                    n if n == store.names.quot_ind => "ind",
                    _ => reject!("invalid quotient dependency"),
                },
            },
            _ => ExportDependency::Ordinary {
                name: self.name(d.name()),
                params: self.params(d.uparams()),
                ty: (*self.expr(d.ty())).clone(),
                value: match d {
                    Declar::Opaque(_, v) if target => Some((*self.expr(v)).clone()),
                    _ => d.unfoldable().map(|(v, _)| (*self.expr(v)).clone()),
                },
            },
        }
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

    fn level(&mut self, l: LevelPtr<'a>) -> OldLevel {
        if let Some(v) = self.levels.get(&l) {
            return v.clone();
        }
        let v = match *l {
            Level::Zero => OldLevel::Nat(0),
            Level::Param(n, _) => OldLevel::Param(self.name(n)),
            Level::Succ(l, _) => self.level(l).succ().unwrap_or_else(|e| reject!("{e}")),
            Level::Max(a, b, _) => OldLevel::max(self.level(a), self.level(b)),
            Level::IMax(a, b, _) => OldLevel::imax(self.level(a), self.level(b)),
        };
        self.levels.insert(l, v.clone());
        v
    }

    fn params(&mut self, levels: LevelsPtr<'a>) -> Vec<String> {
        levels
            .iter()
            .map(|l| match **l {
                Level::Param(n, _) => self.name(n),
                _ => reject!("invalid universe parameter"),
            })
            .collect()
    }

    fn expr(&mut self, e: ExprPtr<'a>) -> Shared<OldExpr> {
        if let Some(v) = self.expressions.get(&e) {
            return v.clone();
        }
        stacker::maybe_grow(STACK_RED_ZONE, STACK_GROWTH, || {
            let out = match *e {
                Expr::Var { idx, .. } => OldExpr::Var(OldName::bound(usize::from(idx), 0)),
                Expr::Sort { level, .. } => OldExpr::Sort(self.level(level)),
                Expr::Const { name, levels, .. } => OldExpr::Const(
                    self.name(name),
                    levels.iter().map(|l| self.level(*l)).collect(),
                ),
                Expr::App { fun, arg, .. } => OldExpr::App(self.expr(fun), self.expr(arg)),
                Expr::Lam { ty, body, .. } => {
                    OldExpr::Lam(self.expr(ty), bind(OldName::new("x"), self.expr(body)))
                }
                Expr::Pi { ty, body, .. } => {
                    OldExpr::Pi(self.expr(ty), bind(OldName::new("x"), self.expr(body)))
                }
                Expr::Let { data, .. } => OldExpr::Let(
                    self.expr(data.ty),
                    self.expr(data.val),
                    bind(OldName::new("x"), self.expr(data.body)),
                ),
                Expr::Proj { name, idx, e, .. } => {
                    OldExpr::Proj(self.name(name), usize::from(idx), self.expr(e))
                }
                Expr::NatLit { n, .. } => OldExpr::nat(n.as_ref().clone()),
                Expr::StrLit { s, .. } => OldExpr::Str(s.s.into()),
                Expr::Local { .. } => reject!("local in imported inductive declaration"),
            };
            let out = Shared::new(out);
            self.expressions.insert(e, out.clone());
            out
        })
    }

    fn block(&mut self, store: &Store<'a>, b: Block) -> kernel::InductiveBlock {
        let mut out = kernel::InductiveBlock {
            types: Vec::new(),
            constructors: Vec::new(),
            recursors: Vec::new(),
        };
        for d in &store.declars[b.start as usize..b.end as usize] {
            match *d {
                Declar::Ind(i) => out.types.push(kernel::InductiveType {
                    name: self.name(i.info.name),
                    params: self.params(i.info.uparams),
                    ty: (*self.expr(i.info.ty)).clone(),
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
                    params: self.params(c.info.uparams),
                    ty: (*self.expr(c.info.ty)).clone(),
                    inductive: self.name(c.induct),
                    index: c.cidx.into(),
                    num_params: c.num_params.into(),
                    num_fields: c.num_fields.into(),
                }),
                Declar::Rec(r) => out.recursors.push(kernel::Recursor {
                    name: self.name(r.info.name),
                    params: self.params(r.info.uparams),
                    ty: (*self.expr(r.info.ty)).clone(),
                    all: r.all.iter().map(|n| self.name(*n)).collect(),
                    num_params: r.num_params.into(),
                    num_indices: r.num_indices.into(),
                    num_motives: r.num_motives.into(),
                    num_minors: r.num_minors.into(),
                    k: r.is_k,
                    rules: r
                        .rules
                        .iter()
                        .map(|r| kernel::RecursorRule {
                            constructor: self.name(r.ctor),
                            num_fields: r.nfields.into(),
                            rhs: (*self.expr(r.rhs)).clone(),
                        })
                        .collect(),
                }),
                _ => unreachable!("non-inductive block member"),
            }
        }
        out
    }
}
