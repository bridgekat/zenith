mod arena;
mod errors;
mod term;

pub use arena::Arena;
pub use errors::{EvalError, TypeError};
pub use term::{Clos, Stack, Term, Val};
