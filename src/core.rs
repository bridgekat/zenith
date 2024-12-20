mod error;
mod stack;
mod structs;
mod term;

pub use error::{EvalError, TypeError};
pub use structs::{Arena, Clos, Entry, Frame, Stack, Term, Univ, Val};
