//! # Term evaluator
//!
//! This module implements the evaluator for the core language.
//!
//! The main function [`Val::eval`] turns [`Term`] into [`Val`], which is a special type for terms
//! in weak normal forms.

use super::*;
use crate::arena::{Arena, Relocate};
use std::slice::from_raw_parts;

/// # Values
///
/// Values are terms whose outermost `let`s are already collected and frozen at binders.
///
/// Can be understood as "runtime objects" produced by the evaluator.
#[derive(Debug, Clone, Copy)]
pub enum Val<'a, 'b> {
  /// Universe in levels.
  Univ(usize),
  /// Free variables in de Bruijn *levels* for cheap weakening.
  Free(usize),
  /// Function types (parameter type, *return type*).
  Pi(&'a Self, &'a Clos<'a, 'b>),
  /// Function abstractions (*body*).
  Fun(&'a Clos<'a, 'b>),
  /// Function applications (function, argument, dot-syntax flag).
  App(&'a Self, &'a Self, bool),
  /// Tuple types (field variable info, *element types*).
  Sig(&'a [(&'b Field<'b>, Clos<'a, 'b>)]),
  /// Tuple constructors (field variable info, element values).
  Tup(&'a [(&'b Field<'b>, Self)]),
  /// Tuple initial segments (truncation, tuple).
  Init(usize, &'a Self),
  /// Tuple projections (index, tuple).
  Proj(usize, &'a Self),
  /// Holes (environment, id).
  Meta(&'a Stack<'a, 'b>, usize),
}

/// # Closures
///
/// Closures are terms annotated with frozen `let`s capturing the whole environment.
///
/// The environment is represented using a special data structure which supports structural sharing
/// and fast random access (in most cases). For more details, see the documentation for [`Stack`].
#[derive(Debug, Clone)]
pub struct Clos<'a, 'b> {
  pub info: &'b Bound<'b>,
  pub env: Stack<'a, 'b>,
  pub body: &'a Term<'a, 'b, Core>,
}

impl<'a, 'b> Val<'a, 'b> {
  /// Reduces `self` so that all `let`s are collected into the environment and then frozen at
  /// binders. This is mutually recursive with [`Val::apply`], forming an eval-apply loop.
  ///
  /// Pre-conditions:
  ///
  /// - `self` is well-typed under a context and environment `env` (to ensure termination).
  pub fn eval(term: &Term<'a, 'b, Core>, env: &Stack<'a, 'b>, ar: &'a Arena) -> Result<Val<'a, 'b>, EvalError<'a, 'b>> {
    match term {
      // The garbage collection mark forces the subterm to be evaluated inside a new arena.
      Term::Gc(x) => Val::eval(x, env, &Arena::new()).map(|v| v.relocate(ar)).map_err(|e| e.relocate(ar)),
      // Universes are already in normal form.
      Term::Univ(v) => Ok(Val::Univ(*v)),
      // The (δ) rule is always applied.
      // Variables of values are in de Bruijn levels, so weakening is no-op.
      Term::Var(ix) => Ok(env.get(*ix, ar).ok_or_else(|| EvalError::env_index(*ix, env.len()))?.1),
      // The (τ) rule is always applied.
      Term::Ann(x, _) => Val::eval(x, env, ar),
      // For `let`s, we reduce the value, collect it into the environment to reduce the body.
      Term::Let(i, v, x) => Val::eval(x, &env.extend(i, Val::eval(v, env, ar)?, ar), ar),
      // For binders, we freeze the whole environment and store the body as a closure.
      Term::Pi(i, t, u) => {
        Ok(Val::Pi(ar.val(Val::eval(t, env, ar)?), ar.clos(Clos { info: i, env: env.clone(), body: u })))
      }
      Term::Fun(i, b) => Ok(Val::Fun(ar.clos(Clos { info: i, env: env.clone(), body: b }))),
      // For applications, we reduce both operands and combine them back.
      // In the case of a redex, the (β) rule is applied.
      Term::App(f, x, b) => match (Val::eval(f, env, ar)?, Val::eval(x, env, ar)?) {
        (Val::Fun(b), x) => Val::apply(b, x, ar),
        (f, x) => Ok(Val::App(ar.val(f), ar.val(x), *b)),
      },
      // For binders, we freeze the whole environment and store the body as a closure.
      Term::Sig(us) => {
        let cs = ar.closures(us.len());
        for (i, (info, u)) in us.iter().enumerate() {
          cs[i] = (info, Clos { info: Bound::empty(), env: env.clone(), body: u });
        }
        Ok(Val::Sig(cs))
      }
      Term::Tup(bs) => {
        let vs = ar.values(bs.len()).as_mut_ptr();
        for (i, (info, b)) in bs.iter().enumerate() {
          // SAFETY: the borrowed range `&vs[..i]` is no longer modified.
          let a = Val::Tup(unsafe { from_raw_parts(vs, i) });
          let b = Val::eval(b, &env.extend(Bound::empty(), a, ar), ar)?;
          // SAFETY: `i < bs.len()` which is the valid size of `vs`.
          unsafe { *vs.add(i) = (info, b) };
        }
        // SAFETY: the borrowed slice `&vs` has valid size `bs.len()` and is no longer modified.
        Ok(Val::Tup(unsafe { from_raw_parts(vs, bs.len()) }))
      }
      // For initials (i.e. iterated first projections), we reduce the operand and combine it back.
      // In the case of a redex, the (π init) rule is applied.
      Term::Init(n, x) => match Val::eval(x, env, ar)? {
        Val::Init(m, y) => Ok(Val::Init(n + m, y)),
        Val::Tup(bs) => {
          let m = bs.len().checked_sub(*n).ok_or_else(|| EvalError::tup_init(*n, Val::Tup(bs), env, ar))?;
          Ok(Val::Tup(&bs[..m]))
        }
        x => Ok(Val::Init(*n, ar.val(x))),
      },
      // For projections (i.e. second projections after iterated first projections), we reduce the
      // operand and combine it back.
      // In the case of a redex, the (π proj) rule is applied.
      Term::Proj(n, x) => match Val::eval(x, env, ar)? {
        Val::Init(m, y) => Ok(Val::Proj(n + m, y)),
        Val::Tup(bs) => {
          let i = bs.len().checked_sub(n + 1).ok_or_else(|| EvalError::tup_proj(*n, Val::Tup(bs), env, ar))?;
          Ok(bs[i].1)
        }
        x => Ok(Val::Proj(*n, ar.val(x))),
      },
      // For holes, we freeze the whole environment around it.
      Term::Meta(m) => Ok(Val::Meta(ar.frame(env.clone()), *m)),
    }
  }

  /// Inserts a new `let` around the body after the frozen `let`s, and reduces the body under the
  /// empty environment populated with all `let`s. This is mutually recursive with [`Val::eval`],
  /// forming an eval-apply loop.
  pub fn apply(clos: &'a Clos<'a, 'b>, x: Val<'a, 'b>, ar: &'a Arena) -> Result<Val<'a, 'b>, EvalError<'a, 'b>> {
    let Clos { env, info, body } = clos;
    Val::eval(body, &Stack::Cons { prev: env, info, value: x }, ar)
  }

  /// Returns if `self` and `other` are definitionally equal. Can be an expensive operation if
  /// they are indeed definitionally equal.
  ///
  /// Pre-conditions:
  ///
  /// - `self` and `other` are well-typed under a context with size `len` (to ensure termination).
  pub fn conv(&self, other: &Self, len: usize, ar: &'a Arena) -> Result<bool, EvalError<'a, 'b>> {
    match (self, other) {
      (Val::Univ(v), Val::Univ(w)) => Ok(v == w),
      (Val::Free(i), Val::Free(j)) => Ok(i == j),
      (Val::Pi(t, v), Val::Pi(u, w)) => Ok(
        Val::conv(t, u, len, ar)?
          && Val::conv(&Val::apply(v, Val::Free(len), ar)?, &Val::apply(w, Val::Free(len), ar)?, len + 1, ar)?,
      ),
      (Val::Fun(b), Val::Fun(c)) => {
        Ok(Val::conv(&Val::apply(b, Val::Free(len), ar)?, &Val::apply(c, Val::Free(len), ar)?, len + 1, ar)?)
      }
      (Val::App(f, x, _), Val::App(g, y, _)) => Ok(Val::conv(f, g, len, ar)? && Val::conv(x, y, len, ar)?),
      (Val::Sig(us), Val::Sig(vs)) if us.len() == vs.len() => {
        for ((i, u), (j, v)) in us.iter().zip(vs.iter()) {
          if i.name != j.name {
            return Ok(false);
          }
          if !Val::conv(&Val::apply(u, Val::Free(len), ar)?, &Val::apply(v, Val::Free(len), ar)?, len + 1, ar)? {
            return Ok(false);
          }
        }
        Ok(true)
      }
      (Val::Tup(bs), Val::Tup(cs)) if bs.len() == cs.len() => {
        for ((i, b), (j, c)) in bs.iter().zip(cs.iter()) {
          if i.name != j.name {
            return Ok(false);
          }
          if !Val::conv(b, c, len, ar)? {
            return Ok(false);
          }
        }
        Ok(true)
      }
      (Val::Init(n, x), Val::Init(m, y)) => Ok(n == m && Val::conv(x, y, len, ar)?),
      (Val::Proj(n, x), Val::Proj(m, y)) => Ok(n == m && Val::conv(x, y, len, ar)?),
      (Val::Meta(_, _), Val::Meta(_, _)) => todo!(),
      _ => Ok(false),
    }
  }

  /// Reduces well-typed `self` to eliminate `let`s and convert it back into a [`Term`].
  /// Can be an expensive operation. Expected to be used for outputs and error reporting.
  ///
  /// Pre-conditions:
  ///
  /// - `self` is well-typed under a context with size `len` (to ensure termination).
  pub fn quote(&self, len: usize, ar: &'a Arena) -> Result<Term<'a, 'b, Core>, EvalError<'a, 'b>> {
    match self {
      Val::Univ(v) => Ok(Term::Univ(*v)),
      Val::Free(i) => Ok(Term::Var(len.checked_sub(i + 1).ok_or_else(|| EvalError::gen_level(*i, len))?)),
      Val::Pi(t, u) => Ok(Term::Pi(
        u.info,
        ar.term(t.quote(len, ar)?),
        ar.term(Val::apply(u, Val::Free(len), ar)?.quote(len + 1, ar)?),
      )),
      Val::Fun(b) => Ok(Term::Fun(b.info, ar.term(Val::apply(b, Val::Free(len), ar)?.quote(len + 1, ar)?))),
      Val::App(f, x, b) => Ok(Term::App(ar.term(f.quote(len, ar)?), ar.term(x.quote(len, ar)?), *b)),
      Val::Sig(us) => {
        let terms = ar.terms(us.len());
        for (term, (info, u)) in terms.iter_mut().zip(us.iter()) {
          *term = (info, Val::apply(u, Val::Free(len), ar)?.quote(len + 1, ar)?);
        }
        Ok(Term::Sig(terms))
      }
      Val::Tup(bs) => {
        let terms = ar.terms(bs.len());
        for (term, (info, b)) in terms.iter_mut().zip(bs.iter()) {
          *term = (info, b.quote(len + 1, ar)?);
        }
        Ok(Term::Tup(terms))
      }
      Val::Init(n, x) => Ok(Term::Init(*n, ar.term(x.quote(len, ar)?))),
      Val::Proj(n, x) => Ok(Term::Proj(*n, ar.term(x.quote(len, ar)?))),
      Val::Meta(_, _) => todo!(),
    }
  }
}
