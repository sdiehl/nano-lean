use super::expr::Expr;
use super::level::Level;
use super::name::{Name, NameNode, NatRed, StrNode};
use super::ptr::{BigUintPtr, ExprPtr, LevelPtr, LevelsPtr, NamePtr, StringPtr};
use crate::hash64;
use bumpalo::Bump;
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

/// Hash-consing table over arena references.
pub struct Interner<'a, T: ?Sized>(HashTable<&'a T>);

impl<'a, T: ?Sized + Keyed> Interner<'a, T> {
    pub fn new() -> Self {
        Self(HashTable::new())
    }

    pub fn with_capacity(n: usize) -> Self {
        Self(HashTable::with_capacity(n))
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn len(&self) -> usize {
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
}

impl<T: ?Sized + Keyed> Default for Interner<'_, T> {
    fn default() -> Self {
        Self::new()
    }
}

/// All interners for one arena.
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

    pub fn add_name(&mut self, arena: &'a Bump, n: Name<'a>) -> NamePtr<'a> {
        NamePtr::new(self.names.insert(arena.alloc(NameNode::new(n))))
    }

    pub fn find_str(&self, s: &str) -> Option<StringPtr<'a>> {
        self.strings
            .find(hash64!(s), |n| n.s == s)
            .map(StringPtr::new)
    }

    pub fn add_str(&mut self, arena: &'a Bump, s: &str) -> StringPtr<'a> {
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

    pub fn add_level(&mut self, arena: &'a Bump, l: Level<'a>) -> LevelPtr<'a> {
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

    pub fn add_levels(&mut self, arena: &'a Bump, ls: &[LevelPtr<'a>]) -> LevelsPtr<'a> {
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

    pub fn add_expr(&mut self, arena: &'a Bump, e: Expr<'a>, meta: u16) -> ExprPtr<'a> {
        ExprPtr::new(self.exprs.insert(arena.alloc(e)), meta)
    }

    pub fn find_nat(&self, n: &BigUint) -> Option<BigUintPtr<'a>> {
        self.nats.find(hash64!(n), |s| s == n).map(BigUintPtr::new)
    }

    pub fn add_nat(&mut self, arena: &'a Bump, n: BigUint) -> BigUintPtr<'a> {
        BigUintPtr::new(self.nats.insert(arena.alloc(n)))
    }

    /// Resolve a dotted name against the interned names, without allocating.
    pub fn lookup(&self, anon: NamePtr<'a>, dotted: &str) -> Option<NamePtr<'a>> {
        let mut pfx = anon;
        for s in dotted.split('.') {
            pfx = if let Ok(n) = s.parse::<u64>() {
                self.find_name(&Name::Num(pfx, n, hash64!(super::name::NUM_HASH, pfx, n)))?
            } else {
                let s = self.find_str(s)?;
                self.find_name(&Name::Str(pfx, s, hash64!(super::name::STR_HASH, pfx, s)))?
            };
        }
        Some(pfx)
    }
}

/// Pointer metadata, recomputed from children for interner hits.
pub fn meta_of(e: &Expr<'_>) -> u16 {
    use super::expr::mk;
    match *e {
        Expr::Var { idx, .. } => mk::var(idx).1,
        Expr::App { fun, arg, .. } => mk::app(fun, arg).1,
        Expr::Lam { ty, body, .. } | Expr::Pi { ty, body, .. } => mk::lam(ty, body).1,
        Expr::Let { data, .. } => mk::let_(*data).1,
        Expr::Proj { e, .. } => e.meta(),
        Expr::Local { .. } => super::expr::HAS_LOCAL,
        _ => 0,
    }
}

macro_rules! names {
    ($($field:ident = $path:literal $(=> $red:ident)?,)*) => {
        /// Names the checker treats specially, resolved once after import.
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
    quot = "Quot",
    quot_mk = "Quot.mk",
    quot_lift = "Quot.lift",
    quot_ind = "Quot.ind",
    eq = "Eq",
    string = "String",
    string_mk = "String.mk",
    string_of_list = "String.ofList",
    char = "Char",
    char_of_nat = "Char.ofNat",
    list_nil = "List.nil",
    list_cons = "List.cons",
    nat = "Nat",
    nat_zero = "Nat.zero",
    bool_true = "Bool.true",
    bool_false = "Bool.false",
    nat_succ = "Nat.succ" => Succ,
    nat_add = "Nat.add" => Add,
    nat_sub = "Nat.sub" => Sub,
    nat_mul = "Nat.mul" => Mul,
    nat_pow = "Nat.pow" => Pow,
    nat_mod = "Nat.mod" => Mod,
    nat_div = "Nat.div" => Div,
    nat_gcd = "Nat.gcd" => Gcd,
    nat_beq = "Nat.beq" => Beq,
    nat_ble = "Nat.ble" => Ble,
    nat_land = "Nat.land" => Land,
    nat_lor = "Nat.lor" => Lor,
    nat_xor = "Nat.xor" => Xor,
    nat_shl = "Nat.shiftLeft" => Shl,
    nat_shr = "Nat.shiftRight" => Shr,
    nat_log2 = "Nat.log2" => Log2,
}

/// Import statistics reported to the user.
#[derive(Clone, Copy, Debug, Default)]
pub struct Stats {
    pub declarations: usize,
    pub expressions: usize,
    pub names: usize,
    pub levels: usize,
}

/// Exact declaration interval emitted by one inductive export entry.
#[derive(Clone, Copy, Debug)]
pub struct Block {
    pub start: u32,
    pub types_end: u32,
    pub ctors_end: u32,
    pub end: u32,
}

/// Immutable imported declarations and their interned syntax, shared by workers.
pub struct Store<'a> {
    pub dag: Dag<'a>,
    pub anon: NamePtr<'a>,
    pub zero: LevelPtr<'a>,
    pub declars: Vec<super::decl::Declar<'a>>,
    /// Each inductive member maps to its exact export block.
    pub blocks: super::FxHashMap<NamePtr<'a>, Block>,
    pub names: Names<'a>,
    pub stats: Stats,
}

impl<'a> Store<'a> {
    pub fn get(&self, n: NamePtr<'a>) -> Option<&super::decl::Declar<'a>> {
        self.declars.get(n.decl_idx()? as usize)
    }
}
