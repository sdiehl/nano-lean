#[cfg(panic = "abort")]
compile_error!("rejection and decline unwind through catch_unwind, so panic must unwind");

pub mod checker;
pub mod emit;
pub mod export;
pub mod import;
pub mod kernel;
pub mod level;
mod lexer;
pub mod mutate;
pub mod parser;
#[cfg(feature = "profile")]
mod profile;
mod resource;
pub mod schema;
pub mod syntax;
pub mod term;
pub mod value_checker;
pub mod verdict;

pub use kernel::{Environment, Error};
pub use resource::Budget;
