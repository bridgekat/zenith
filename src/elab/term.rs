use typed_arena::Arena;

use self::Term::*;
use super::*;
use crate::core;

/// One of the two central data structures of the elaborator. The other one is [`Context`].
///
/// A [`Term`] is conceptually associated with a unique [`Context`], under which should it be interpreted.
/// A [`Fun`], [`Pi`] or [`Let`] binder introduces a new layer in the associated context of the enclosed sub-term,
/// compared with the parent term.
///
///
#[derive(Debug, Clone, Copy)]
pub enum Term<'a> {
  /// Universes.
  Univ(Sort),
  /// Variables in de Bruijn indices.
  Var(usize),
  /// Type annotations.
  Ann(&'a Term<'a>, &'a Term<'a>),
  /// Definitions.
  Let(&'a Term<'a>, &'a Term<'a>, BinderInfo),
  /// Function types.
  Pi(&'a Term<'a>, &'a Term<'a>, BinderInfo),
  /// Function descriptions.
  Fun(&'a Term<'a>, BinderInfo),
  /// Function applications.
  App(&'a Term<'a>, &'a Term<'a>),
  /// Metavariables.
  Meta(usize),
  /// Source info.
  Src(&'a Term<'a>, SourceInfo),
}

/// Dictionary index and implicitness of the bound variable.
#[derive(Debug, Clone, Copy, Hash)]
pub struct BinderInfo {
  pub name_id: usize,
  pub is_implicit: bool,
}

/// Starting and ending positions in input source code.
#[derive(Debug, Clone, Copy, Hash)]
pub struct SourceInfo {
  pub begin: usize,
  pub end: usize,
}

impl<'a> Term<'a> {
  /// Moves the term to a given pool.
  pub fn clone_to<'b>(&'a self, pool: &'b Arena<Term<'b>>) -> &'b Term<'b> {
    match *self {
      Univ(u) => pool.alloc(Univ(u)),
      Var(i) => pool.alloc(Var(i)),
      App(f, x) => pool.alloc(App(f.clone_to(pool), x.clone_to(pool))),
      Fun(x, info) => pool.alloc(Fun(x.clone_to(pool), info)),
      Pi(s, t, info) => pool.alloc(Pi(s.clone_to(pool), t.clone_to(pool), info)),
      Meta(i) => pool.alloc(Meta(i)),
      Let(v, x, info) => pool.alloc(Let(v.clone_to(pool), x.clone_to(pool), info)),
      Ann(x, t) => pool.alloc(Ann(x.clone_to(pool), t.clone_to(pool))),
      Src(x, info) => pool.alloc(Src(x.clone_to(pool), info)),
    }
  }

  /// Converts the term to core term.
  pub fn clone_to_core<'b>(&'a self, pool: &'b Arena<core::Term<'b>>) -> Result<&'b core::Term<'b>, Error> {
    match *self {
      Univ(Sort(u)) => Ok(pool.alloc(core::Term::Univ(core::Univ(u)))),
      Var(i) => Ok(pool.alloc(core::Term::Var(i))),
      App(f, x) => Ok(pool.alloc(core::Term::App(f.clone_to_core(pool)?, x.clone_to_core(pool)?))),
      Fun(x, _) => Ok(pool.alloc(core::Term::Fun(x.clone_to_core(pool)?))),
      Pi(s, t, _) => Ok(pool.alloc(core::Term::Pi(s.clone_to_core(pool)?, t.clone_to_core(pool)?))),
      Meta(_) => Err(Error::UnresolvedMeta { term: self }),
      Let(v, x, _) => Ok(pool.alloc(core::Term::Let(v.clone_to_core(pool)?, x.clone_to_core(pool)?))),
      Ann(x, _) => Ok(x.clone_to_core(pool)?),
      Src(x, _) => Ok(x.clone_to_core(pool)?),
    }
  }
}
