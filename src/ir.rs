mod errors;
mod term;

pub use errors::{EvalError, TypeError};
pub use term::{Bound, Clos, Core, Decoration, Field, Ix, Name, Named, Stack, Term, Val, Var};
