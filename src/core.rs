pub mod stack;
pub use stack::{Frame, Stack};

pub mod term;
pub use term::{Clos, Ctx, Env, Term, Univ, Val};

pub mod error;
pub use error::{EvalError, TypeError};
