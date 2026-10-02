use crate::Error;
use std::collections::{BTreeMap, BTreeSet};
use unbound::{Alpha, AnyName, Name, Subst, SubstName};

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Level {
    Nat(u32),
    Param(String),
    Succ(Box<Level>),
    Max(Box<Level>, Box<Level>),
    IMax(Box<Level>, Box<Level>),
}

impl From<u32> for Level {
    fn from(n: u32) -> Self {
        Self::Nat(n)
    }
}

#[derive(Default, PartialEq, Eq)]
struct Polynomial {
    constant: u32,
    terms: BTreeMap<String, u32>,
}

impl Polynomial {
    fn join(mut self, other: Self) -> Self {
        self.constant = self.constant.max(other.constant);
        for (name, offset) in other.terms {
            let entry = self.terms.entry(name).or_default();
            *entry = (*entry).max(offset);
        }
        self.canonicalize();
        self
    }
    fn canonicalize(&mut self) {
        self.constant = self
            .constant
            .max(self.terms.values().copied().max().unwrap_or(0));
    }
    fn succ(mut self) -> Result<Self, Error> {
        let add = |n: u32| {
            n.checked_add(1)
                .ok_or_else(|| Error("universe overflow".into()))
        };
        self.constant = add(self.constant)?;
        for offset in self.terms.values_mut() {
            *offset = add(*offset)?;
        }
        Ok(self)
    }
}

impl Level {
    pub fn succ(self) -> Result<Self, Error> {
        match self {
            Self::Nat(n) => Ok(Self::Nat(
                n.checked_add(1)
                    .ok_or_else(|| Error("universe overflow".into()))?,
            )),
            other => Ok(Self::Succ(Box::new(other))),
        }
    }
    pub fn max(a: Self, b: Self) -> Self {
        if a == b {
            return a;
        }
        match (&a, &b) {
            (Self::Nat(x), Self::Nat(y)) => Self::Nat((*x).max(*y)),
            (Self::Nat(0), _) => b,
            (_, Self::Nat(0)) => a,
            _ => Self::Max(Box::new(a), Box::new(b)),
        }
    }
    pub fn imax(a: Self, b: Self) -> Self {
        match &b {
            Self::Nat(0) => Self::Nat(0),
            Self::Nat(_) | Self::Succ(_) => Self::max(a, b),
            _ if a == b => a,
            _ => Self::IMax(Box::new(a), Box::new(b)),
        }
    }
    pub fn params(&self, out: &mut BTreeSet<String>) {
        match self {
            Self::Param(n) => {
                out.insert(n.clone());
            }
            Self::Succ(a) => a.params(out),
            Self::Max(a, b) | Self::IMax(a, b) => {
                a.params(out);
                b.params(out);
            }
            Self::Nat(_) => {}
        }
    }
    pub fn substitute(&self, values: &BTreeMap<String, Level>) -> Result<Self, Error> {
        Ok(match self {
            Self::Nat(n) => Self::Nat(*n),
            Self::Param(n) => values
                .get(n)
                .cloned()
                .ok_or_else(|| Error(format!("undeclared universe: {n}")))?,
            Self::Succ(a) => a.substitute(values)?.succ()?,
            Self::Max(a, b) => Self::max(a.substitute(values)?, b.substitute(values)?),
            Self::IMax(a, b) => Self::imax(a.substitute(values)?, b.substitute(values)?),
        })
    }
    fn polynomial(&self, cases: &BTreeMap<String, bool>) -> Result<Option<Polynomial>, Error> {
        Ok(Some(match self {
            Self::Nat(n) => Polynomial {
                constant: *n,
                ..Polynomial::default()
            },
            Self::Param(n) => match cases.get(n) {
                Some(false) => Polynomial::default(),
                positive => {
                    let offset = u32::from(positive == Some(&true));
                    Polynomial {
                        constant: offset,
                        terms: BTreeMap::from([(n.clone(), offset)]),
                    }
                }
            },
            Self::Succ(a) => {
                let Some(a) = a.polynomial(cases)? else {
                    return Ok(None);
                };
                a.succ()?
            }
            Self::Max(a, b) => {
                let (Some(a), Some(b)) = (a.polynomial(cases)?, b.polynomial(cases)?) else {
                    return Ok(None);
                };
                a.join(b)
            }
            Self::IMax(a, b) => {
                let Some(b) = b.polynomial(cases)? else {
                    return Ok(None);
                };
                if b.constant == 0 && b.terms.is_empty() {
                    Polynomial::default()
                } else if b.constant > 0 {
                    let Some(a) = a.polynomial(cases)? else {
                        return Ok(None);
                    };
                    a.join(b)
                } else {
                    return Ok(None);
                }
            }
        }))
    }
    pub fn equivalent(&self, other: &Self) -> Result<bool, Error> {
        if self == other {
            return Ok(true);
        }
        let mut cases = BTreeMap::new();
        if let (Some(a), Some(b)) = (self.polynomial(&cases)?, other.polynomial(&cases)?) {
            return Ok(a == b);
        }
        let mut params = BTreeSet::new();
        self.params(&mut params);
        other.params(&mut params);
        if params.len() > 16 {
            return Err(Error("universe comparison budget exhausted".into()));
        }
        // Split each parameter into zero or (fresh natural + 1). On each branch
        // imax becomes max or zero, and max-plus polynomials have a canonical form.
        for mask in 0..(1usize << params.len()) {
            for (i, n) in params.iter().enumerate() {
                cases.insert(n.clone(), mask & (1 << i) != 0);
            }
            match (self.polynomial(&cases)?, other.polynomial(&cases)?) {
                (Some(a), Some(b)) if a == b => {}
                (Some(_), Some(_)) => return Ok(false),
                _ => return Err(Error("unresolved universe branch".into())),
            }
        }
        Ok(true)
    }
}

impl Alpha for Level {
    fn support(&self) -> unbound::Support {
        unbound::Support::default()
    }
    fn aeq(&self, other: &Self) -> bool {
        self == other
    }
    fn close(&mut self, _: usize, _: &[AnyName]) {}
    fn open(&mut self, _: usize, _: &[AnyName]) {}
    fn fv_in(&self, _: &mut Vec<AnyName>) {}
}
impl<V> Subst<V> for Level {
    fn instantiate_with(&self, _: usize, _: &mut unbound::InstantiateCtx<'_, V>) -> Option<Self> {
        Some(self.clone())
    }
    fn is_var(&self) -> Option<SubstName<V>> {
        None
    }
    fn subst(&self, _: &Name<V>, _: &V) -> Self {
        self.clone()
    }
}
impl std::fmt::Display for Level {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Nat(n) => write!(f, "{n}"),
            Self::Param(n) => f.write_str(n),
            Self::Succ(a) => write!(f, "(succ {a})"),
            Self::Max(a, b) => write!(f, "(max {a} {b})"),
            Self::IMax(a, b) => write!(f, "(imax {a} {b})"),
        }
    }
}
