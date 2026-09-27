use serde_json::Value;
use unbound::prelude::*;

#[derive(Clone, Alpha, Subst)]
pub enum Term {
    Var(Name<Term>),
    Atom,
    App(Shared<Term>, Shared<Term>),
    Binder(Shared<Term>, Bind<Name<Term>, Shared<Term>>),
    Let(Shared<Term>, Shared<Term>, Bind<Name<Term>, Shared<Term>>),
    Proj(Shared<Term>),
}

pub fn decode(
    item: &Value,
    get: impl Fn(&Value) -> Result<Shared<Term>, Box<dyn std::error::Error>>,
) -> Result<Shared<Term>, Box<dyn std::error::Error>> {
    let kind = item
        .as_object()
        .ok_or("expected object")?
        .keys()
        .find(|k| *k != "ie")
        .ok_or("missing node kind")?;
    let node = &item[kind];
    let term = match kind.as_str() {
        "bvar" => Term::Var(Name::bound(
            node.as_u64().ok_or("invalid variable")? as usize,
            0,
        )),
        "app" => Term::App(get(&node["fn"])?, get(&node["arg"])?),
        "lam" | "forallE" => Term::Binder(
            get(&node["type"])?,
            bind(Name::new(""), get(&node["body"])?),
        ),
        "letE" => Term::Let(
            get(&node["type"])?,
            get(&node["value"])?,
            bind(Name::new(""), get(&node["body"])?),
        ),
        "proj" => Term::Proj(get(&node["struct"])?),
        "mdata" => {
            return get(&node["expr"]);
        }
        "sort" | "const" | "natVal" | "strVal" => Term::Atom,
        _ => return Err(format!("unknown expression kind {kind}").into()),
    };

    Ok(Shared::new(term))
}
