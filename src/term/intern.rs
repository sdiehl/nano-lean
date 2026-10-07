use super::FxHashMap;
use super::arena::Arena;
use super::decl::Declar;
use super::expr::{Expr, HAS_LOCAL, Meta, mk};
use super::level::Level;
use super::name::{NUM_HASH, Name, NameNode, NatRed, STR_HASH, StrNode};
use super::names::*;
use super::ptr::{BigUintPtr, ExprPtr, LevelPtr, LevelsPtr, NamePtr, StringPtr};
use crate::hash64;
use hashbrown::HashTable;
use num_bigint::BigUint;

pub trait Keyed {
    fn key_hash(&self) -> u64;
}

impl Keyed for NameNode<'_> {
    fn key_hash(&self) -> u64 {
        self.kind.get_hash()
    }
}

impl Keyed for Level<'_> {
    fn key_hash(&self) -> u64 {
        self.get_hash()
    }
}

impl Keyed for Expr<'_> {
    fn key_hash(&self) -> u64 {
        self.get_hash()
    }
}

impl Keyed for StrNode<'_> {
    fn key_hash(&self) -> u64 {
        self.hash
    }
}

impl Keyed for [LevelPtr<'_>] {
    fn key_hash(&self) -> u64 {
        hash64!(self)
    }
}

impl Keyed for BigUint {
    fn key_hash(&self) -> u64 {
        hash64!(self)
    }
}

/// Bits of the bucket index that order a bulk fill, so its writes sweep the table.
const FILL_RADIX_BITS: u32 = 11;

pub struct Interner<'a, T: ?Sized>(HashTable<&'a T>);

impl<'a, T: ?Sized + Keyed> Interner<'a, T> {
    pub fn new() -> Self {
        Self(HashTable::new())
    }

    pub fn with_capacity(n: usize) -> Self {
        Self(HashTable::with_capacity(n))
    }

    #[cfg(test)]
    pub(crate) fn len(&self) -> usize {
        self.0.len()
    }

    #[inline]
    pub fn find(&self, hash: u64, mut eq: impl FnMut(&T) -> bool) -> Option<&'a T> {
        self.0.find(hash, |r| eq(r)).copied()
    }

    #[inline]
    pub fn insert(&mut self, r: &'a T) -> &'a T {
        self.0.insert_unique(r.key_hash(), r, |r| r.key_hash());
        r
    }

    pub fn fill(&mut self, items: impl Iterator<Item = &'a T> + Clone) {
        let n = items.clone().count();
        self.0.reserve(n, |r| r.key_hash());
        let buckets = (self.0.capacity() * 8 / 7).next_power_of_two();
        let shift = buckets.trailing_zeros().saturating_sub(FILL_RADIX_BITS);
        let region = |h: u64| (h as usize & (buckets - 1)) >> shift;
        let mut starts = vec![0usize; (1 << FILL_RADIX_BITS) + 1];
        for r in items.clone() {
            starts[region(r.key_hash()) + 1] += 1;
        }
        for i in 1..starts.len() {
            starts[i] += starts[i - 1];
        }
        let mut sorted: Vec<(u64, Option<&'a T>)> = vec![(0, None); n];
        for r in items {
            let h = r.key_hash();
            let s = &mut starts[region(h)];
            sorted[*s] = (h, Some(r));
            *s += 1;
        }
        for (h, r) in sorted {
            let r = r.expect("every slot is written once");
            self.0.insert_unique(h, r, |r| r.key_hash());
        }
    }
}

impl<T: ?Sized + Keyed> Default for Interner<'_, T> {
    fn default() -> Self {
        Self::new()
    }
}

const LINES_PER_NAME: usize = 16;

#[derive(Default)]
pub struct Dag<'a> {
    pub names: Interner<'a, NameNode<'a>>,
    pub strings: Interner<'a, StrNode<'a>>,
    pub levels: Interner<'a, Level<'a>>,
    pub level_lists: Interner<'a, [LevelPtr<'a>]>,
    pub exprs: Interner<'a, Expr<'a>>,
    pub nats: Interner<'a, BigUint>,
}

impl<'a> Dag<'a> {
    /// Presized for `lines` lines so the big tables never rehash.
    pub fn with_capacity(lines: usize) -> Self {
        Self {
            names: Interner::with_capacity(lines / LINES_PER_NAME),
            strings: Interner::with_capacity(lines / LINES_PER_NAME),
            exprs: Interner::with_capacity(lines),
            ..Self::default()
        }
    }

    pub fn find_name<'b>(&self, n: &Name<'b>) -> Option<NamePtr<'a>>
    where
        'a: 'b,
    {
        self.names
            .find(n.get_hash(), |s| {
                let k: Name<'b> = s.kind;
                k == *n
            })
            .map(NamePtr::new)
    }

    pub fn add_name(&mut self, arena: &'a Arena, n: Name<'a>) -> NamePtr<'a> {
        NamePtr::new(self.names.insert(arena.alloc(NameNode::new(n))))
    }

    pub fn find_str(&self, s: &str) -> Option<StringPtr<'a>> {
        self.strings
            .find(hash64!(s), |n| n.s == s)
            .map(StringPtr::new)
    }

    pub fn add_str(&mut self, arena: &'a Arena, s: &str) -> StringPtr<'a> {
        let hash = hash64!(s);
        let s = arena.alloc_str(s);
        StringPtr::new(self.strings.insert(arena.alloc(StrNode { s, hash })))
    }

    pub fn find_level<'b>(&self, l: &Level<'b>) -> Option<LevelPtr<'a>>
    where
        'a: 'b,
    {
        self.levels
            .find(l.get_hash(), |s| {
                let k: Level<'b> = *s;
                k == *l
            })
            .map(LevelPtr::new)
    }

    pub fn add_level(&mut self, arena: &'a Arena, l: Level<'a>) -> LevelPtr<'a> {
        LevelPtr::new(self.levels.insert(arena.alloc(l)))
    }

    pub fn find_levels<'b>(&self, ls: &[LevelPtr<'b>]) -> Option<LevelsPtr<'a>>
    where
        'a: 'b,
    {
        self.level_lists
            .find(hash64!(ls), |s| {
                let k: &[LevelPtr<'b>] = s;
                k == ls
            })
            .map(LevelsPtr::new)
    }

    pub fn add_levels(&mut self, arena: &'a Arena, ls: &[LevelPtr<'a>]) -> LevelsPtr<'a> {
        LevelsPtr::new(self.level_lists.insert(arena.alloc_slice_copy(ls)))
    }

    pub fn find_expr<'b>(&self, e: &Expr<'b>) -> Option<ExprPtr<'a>>
    where
        'a: 'b,
    {
        self.exprs
            .find(e.get_hash(), |s| {
                let k: Expr<'b> = *s;
                k == *e
            })
            .map(|r| ExprPtr::new(r, meta_of(r)))
    }

    pub fn add_expr(&mut self, arena: &'a Arena, e: Expr<'a>, meta: Meta) -> ExprPtr<'a> {
        ExprPtr::new(self.exprs.insert(arena.alloc(e)), meta)
    }

    pub fn find_nat(&self, n: &BigUint) -> Option<BigUintPtr<'a>> {
        self.nats.find(hash64!(n), |s| s == n).map(BigUintPtr::new)
    }

    pub fn add_nat(&mut self, arena: &'a Arena, n: BigUint) -> BigUintPtr<'a> {
        BigUintPtr::new(self.nats.insert(arena.alloc_nat(n)))
    }

    #[inline]
    pub fn intern_name(&mut self, arena: &'a Arena, n: Name<'a>) -> NamePtr<'a> {
        self.find_name(&n)
            .unwrap_or_else(|| self.add_name(arena, n))
    }

    #[inline]
    pub fn intern_str(&mut self, arena: &'a Arena, s: &str) -> StringPtr<'a> {
        self.find_str(s).unwrap_or_else(|| self.add_str(arena, s))
    }

    #[inline]
    pub fn intern_level(&mut self, arena: &'a Arena, l: Level<'a>) -> LevelPtr<'a> {
        self.find_level(&l)
            .unwrap_or_else(|| self.add_level(arena, l))
    }

    #[inline]
    pub fn intern_levels(&mut self, arena: &'a Arena, ls: &[LevelPtr<'a>]) -> LevelsPtr<'a> {
        self.find_levels(ls)
            .unwrap_or_else(|| self.add_levels(arena, ls))
    }

    #[inline]
    pub fn intern_nat(&mut self, arena: &'a Arena, n: BigUint) -> BigUintPtr<'a> {
        self.find_nat(&n).unwrap_or_else(|| self.add_nat(arena, n))
    }

    #[inline]
    pub fn intern_expr(&mut self, arena: &'a Arena, e: Expr<'a>, meta: Meta) -> ExprPtr<'a> {
        self.find_expr(&e)
            .unwrap_or_else(|| self.add_expr(arena, e, meta))
    }

    pub fn lookup(&self, anon: NamePtr<'a>, dotted: &str) -> Option<NamePtr<'a>> {
        let mut pfx = anon;
        for s in dotted.split('.') {
            pfx = if let Ok(n) = s.parse::<u64>() {
                self.find_name(&Name::Num(pfx, n, hash64!(NUM_HASH, pfx, n)))?
            } else {
                let s = self.find_str(s)?;
                self.find_name(&Name::Str(pfx, s, hash64!(STR_HASH, pfx, s)))?
            };
        }
        Some(pfx)
    }
}

pub fn meta_of(e: &Expr<'_>) -> Meta {
    match *e {
        Expr::Var { idx, .. } => mk::var(idx).1,
        Expr::App { fun, arg, .. } => mk::app(fun, arg).1,
        Expr::Lam { ty, body, .. } | Expr::Pi { ty, body, .. } => mk::lam(ty, body).1,
        Expr::Let { data, .. } => mk::let_(*data).2,
        Expr::Proj { e, .. } => e.meta(),
        Expr::Local { .. } => HAS_LOCAL,
        _ => 0,
    }
}

macro_rules! names {
    ($($field:ident = $path:expr $(=> $red:ident)?,)*) => {
        #[derive(Clone, Copy, Debug, Default)]
        pub struct Names<'a> {
            $(pub $field: Option<NamePtr<'a>>,)*
        }

        impl<'a> Names<'a> {
            pub fn build(dag: &Dag<'a>, anon: NamePtr<'a>) -> Self {
                let names = Names { $($field: dag.lookup(anon, $path),)* };
                $($(if let Some(n) = names.$field { n.set_nat_red(NatRed::$red); })?)*
                names
            }
        }
    };
}

names! {
    quot = QUOT,
    quot_mk = QUOT_MK,
    quot_lift = QUOT_LIFT,
    quot_ind = QUOT_IND,
    eq = EQ,
    string = STRING,
    string_of_list = STRING_OF_LIST,
    char = CHAR,
    char_of_nat = CHAR_OF_NAT,
    list_nil = LIST_NIL,
    list_cons = LIST_CONS,
    nat = NAT,
    nat_zero = NAT_ZERO,
    bool_true = BOOL_TRUE,
    bool_false = BOOL_FALSE,
    nat_succ = NAT_SUCC => Succ,
    nat_add = NAT_ADD => Add,
    nat_sub = NAT_SUB => Sub,
    nat_mul = NAT_MUL => Mul,
    nat_pow = NAT_POW => Pow,
    nat_mod = NAT_MOD => Mod,
    nat_div = NAT_DIV => Div,
    nat_gcd = NAT_GCD => Gcd,
    nat_beq = NAT_BEQ => Beq,
    nat_ble = NAT_BLE => Ble,
    nat_land = NAT_LAND => Land,
    nat_lor = NAT_LOR => Lor,
    nat_xor = NAT_XOR => Xor,
    nat_shl = NAT_SHL => Shl,
    nat_shr = NAT_SHR => Shr,
    nat_log2 = NAT_LOG2 => Log2,
}

#[derive(Clone, Copy, Debug, Default)]
pub struct Stats {
    pub declarations: usize,
    pub expressions: usize,
    pub names: usize,
    pub levels: usize,
}

#[derive(Clone, Copy, Debug)]
pub struct Block {
    pub start: u32,
    pub types_end: u32,
    pub ctors_end: u32,
    pub end: u32,
}

pub struct Store<'a> {
    pub dag: Dag<'a>,
    pub anon: NamePtr<'a>,
    pub zero: LevelPtr<'a>,
    pub declars: Vec<Declar<'a>>,
    pub blocks: FxHashMap<NamePtr<'a>, Block>,
    pub names: Names<'a>,
    pub stats: Stats,
}
