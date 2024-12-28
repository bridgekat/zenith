mod arena;
mod errors;
mod io;
mod term;

pub use arena::Arena;
pub use errors::{EvalError, LexError, ParseError, TypeError};
pub use io::{Span, Token};
pub use term::{Clos, Stack, Term, Val};
