//! Per-thread allocation context: a bump arena plus local interners layered over
//! the shared import store. Everything the checker builds lives here.

use super::FxHashMap;
use super::expr::{Expr, LetData, mk};
use super::intern::{Dag, Store};
use super::level::{IMAX_HASH, Level, MAX_HASH, PARAM_HASH, SUCC_HASH};
use super::name::{Name, STR_HASH as NAME_STR_HASH};
use super::ptr::{BigUintPtr, ExprPtr, LevelPtr, LevelsPtr, NamePtr, StringPtr};
use crate::hash64;
use crate::term::arena::Arena;
use num_bigint::BigUint;

pub struct Ctx<'t, 'a: 't> {
    pub store: &'a Store<'a>,
    pub arena: &'t Arena,
    pub dag: Dag<'t>,
    /// Memo for one traversal: key (expr, op and offset) to (generation, result).
    pub(crate) memo: FxHashMap<(ExprPtr<'t>, u32), (u32, ExprPtr<'t>)>,
    pub(crate) generation: u32,
    pub(crate) subst_cache: FxHashMap<(ExprPtr<'t>, LevelsPtr<'t>, LevelsPtr<'t>), ExprPtr<'t>>,
    pub(crate) simp_cache: FxHashMap<LevelPtr<'t>, LevelPtr<'t>>,
}

impl<'t, 'a: 't> Ctx<'t, 'a> {
    pub fn new(store: &'a Store<'a>, arena: &'t Arena) -> Self {
        Self {
            store,
            arena,
            dag: Dag::default(),
            memo: FxHashMap::default(),
            generation: 0,
            subst_cache: FxHashMap::default(),
            simp_cache: FxHashMap::default(),
        }
    }

    pub fn anon(&self) -> NamePtr<'t> {
        self.store.anon
    }

    pub fn zero(&self) -> LevelPtr<'t> {
        self.store.zero
    }

    pub fn name(&mut self, n: Name<'t>) -> NamePtr<'t> {
        if let Some(p) = self.store.dag.find_name(&n) {
            return p;
        }
        match self.dag.find_name(&n) {
            Some(p) => p,
            None => self.dag.add_name(self.arena, n),
        }
    }

    pub fn str_name(&mut self, pfx: NamePtr<'t>, s: StringPtr<'t>) -> NamePtr<'t> {
        self.name(Name::Str(pfx, s, hash64!(NAME_STR_HASH, pfx, s)))
    }

    pub fn string(&mut self, s: &str) -> StringPtr<'t> {
        if let Some(p) = self.store.dag.find_str(s) {
            return p;
        }
        match self.dag.find_str(s) {
            Some(p) => p,
            None => self.dag.add_str(self.arena, s),
        }
    }

    pub fn str1(&mut self, s: &str) -> NamePtr<'t> {
        let s = self.string(s);
        let anon = self.anon();
        self.str_name(anon, s)
    }

    pub fn level(&mut self, l: Level<'t>) -> LevelPtr<'t> {
        if let Some(p) = self.store.dag.find_level(&l) {
            return p;
        }
        match self.dag.find_level(&l) {
            Some(p) => p,
            None => self.dag.add_level(self.arena, l),
        }
    }

    pub fn succ(&mut self, l: LevelPtr<'t>) -> LevelPtr<'t> {
        self.level(Level::Succ(l, hash64!(SUCC_HASH, l)))
    }

    pub fn max(&mut self, l: LevelPtr<'t>, r: LevelPtr<'t>) -> LevelPtr<'t> {
        if l == r || matches!(*r, Level::Zero) {
            return l;
        }
        if matches!(*l, Level::Zero) {
            return r;
        }
        self.level(Level::Max(l, r, hash64!(MAX_HASH, l, r)))
    }

    pub fn imax(&mut self, l: LevelPtr<'t>, r: LevelPtr<'t>) -> LevelPtr<'t> {
        if l == r || matches!(*l, Level::Zero) || matches!(*r, Level::Zero) {
            return r;
        }
        if matches!(*r, Level::Succ(..)) {
            return self.max(l, r);
        }
        self.level(Level::IMax(l, r, hash64!(IMAX_HASH, l, r)))
    }

    pub fn param(&mut self, n: NamePtr<'t>) -> LevelPtr<'t> {
        self.level(Level::Param(n, hash64!(PARAM_HASH, n)))
    }

    pub fn levels(&mut self, ls: &[LevelPtr<'t>]) -> LevelsPtr<'t> {
        if let Some(p) = self.store.dag.find_levels(ls) {
            return p;
        }
        match self.dag.find_levels(ls) {
            Some(p) => p,
            None => self.dag.add_levels(self.arena, ls),
        }
    }

    pub fn nat(&mut self, n: BigUint) -> BigUintPtr<'t> {
        if let Some(p) = self.store.dag.find_nat(&n) {
            return p;
        }
        match self.dag.find_nat(&n) {
            Some(p) => p,
            None => self.dag.add_nat(self.arena, n),
        }
    }

    #[inline]
    fn expr(&mut self, (e, meta): (Expr<'t>, u16)) -> ExprPtr<'t> {
        if let Some(p) = self.store.dag.find_expr(&e) {
            return p;
        }
        match self.dag.find_expr(&e) {
            Some(p) => p,
            None => self.dag.add_expr(self.arena, e, meta),
        }
    }

    pub fn var(&mut self, idx: u16) -> ExprPtr<'t> {
        self.expr(mk::var(idx))
    }

    pub fn sort(&mut self, level: LevelPtr<'t>) -> ExprPtr<'t> {
        self.expr(mk::sort(level))
    }

    pub fn prop(&mut self) -> ExprPtr<'t> {
        let z = self.zero();
        self.sort(z)
    }

    pub fn konst(&mut self, name: NamePtr<'t>, levels: LevelsPtr<'t>) -> ExprPtr<'t> {
        self.expr(mk::konst(name, levels))
    }

    pub fn app(&mut self, fun: ExprPtr<'t>, arg: ExprPtr<'t>) -> ExprPtr<'t> {
        self.expr(mk::app(fun, arg))
    }

    pub fn apps(&mut self, mut f: ExprPtr<'t>, args: &[ExprPtr<'t>]) -> ExprPtr<'t> {
        for &a in args {
            f = self.app(f, a);
        }
        f
    }

    pub fn lam(&mut self, ty: ExprPtr<'t>, body: ExprPtr<'t>) -> ExprPtr<'t> {
        self.expr(mk::lam(ty, body))
    }

    pub fn pi(&mut self, ty: ExprPtr<'t>, body: ExprPtr<'t>) -> ExprPtr<'t> {
        self.expr(mk::pi(ty, body))
    }

    pub fn let_(
        &mut self,
        ty: ExprPtr<'t>,
        val: ExprPtr<'t>,
        body: ExprPtr<'t>,
        nondep: bool,
    ) -> ExprPtr<'t> {
        let probe = LetData {
            ty,
            val,
            body,
            nondep,
        };
        let (hash, nlb) = mk::let_(probe);
        let e = Expr::Let { data: &probe, hash };
        if let Some(p) = self
            .store
            .dag
            .find_expr(&e)
            .or_else(|| self.dag.find_expr(&e))
        {
            return p;
        }
        let data = self.arena.alloc(probe);
        self.dag.add_expr(self.arena, Expr::Let { data, hash }, nlb)
    }

    pub fn proj(&mut self, name: NamePtr<'t>, idx: u16, e: ExprPtr<'t>) -> ExprPtr<'t> {
        self.expr(mk::proj(name, idx, e))
    }

    pub fn nat_lit(&mut self, n: BigUint) -> ExprPtr<'t> {
        let n = self.nat(n);
        self.expr(mk::nat(n))
    }

    pub fn local(&mut self, id: u32, ty: ExprPtr<'t>) -> ExprPtr<'t> {
        self.expr(mk::local(id, ty))
    }
}
