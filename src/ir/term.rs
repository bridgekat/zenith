//! # Term checker
//!
//! This module implements the core terms.
//!
//! The main functions [`Term::infer`] and [`Term::check`] performs type checking and returns a
//! named variant of the term.

use std::cmp::max;
use std::fmt::Debug;
use std::slice::from_raw_parts;

use super::*;
use crate::arena::{Arena, Relocate};

/// # Terms
///
/// Terms of the core calculus. Can be understood as the "source code" given to the evaluator.
///
/// Every extension can be hard-coded in this enum. [`Decoration`]s are then use to selectively
/// disable certain extension variants. This design is due to limitations of Rust's type variance.
#[derive(Debug, Clone, Copy)]
pub enum Term<'a, 'b, T: Decoration> {
  /// Garbage collection mark.
  Gc(&'a Self),
  /// Universe in levels.
  Univ(usize),
  /// Variables in de Bruijn indices.
  Var(usize),
  /// Type annotations (value, type).
  Ann(&'a Self, &'a Self),
  /// Let expressions (bound variable info, value, *body*).
  Let(&'b Bound<'b>, &'a Self, &'a Self),
  /// Function types (bound variable info, parameter type, *return type*).
  Pi(&'b Bound<'b>, &'a Self, &'a Self),
  /// Function abstractions (bound variable info, *body*).
  Fun(&'b Bound<'b>, &'a Self),
  /// Function applications (function, argument, dot-syntax flag).
  App(&'a Self, &'a Self, bool),
  /// Tuple types (field variable info, *element types*).
  Sig(&'a [(&'b Field<'b>, Self)]),
  /// Tuple constructors (field variable info, *element values*).
  Tup(&'a [(&'b Field<'b>, Self)]),
  /// Tuple initial segments (truncation, tuple).
  Init(usize, &'a Self),
  /// Tuple projections (index, tuple).
  Proj(usize, &'a Self),
  /// Holes in unique identifiers.
  Hole(usize),
  /// Named variables.
  NamedVar(Name<'b>, T::NamedVar<'b>),
  /// Named projections.
  NamedProj(Name<'b>, &'a Self, T::NamedProj<'b>),
}

impl<'a, 'b, T: Decoration> Term<'a, 'b, T> {
  /// Given universe `u`, returns the universe of its type.
  pub fn univ_univ(u: usize) -> Result<usize, TypeError<'a, 'b, T>> {
    match u {
      #[cfg(feature = "type_in_type")]
      0 => Ok(0),
      #[cfg(not(feature = "type_in_type"))]
      0 => Ok(1),
      _ => Err(TypeError::univ_form(u)),
    }
  }

  /// Given universes `v` and `w`, returns the universe of Pi types from `v` to `w`.
  pub fn pi_univ(v: usize, w: usize) -> Result<usize, TypeError<'a, 'b, T>> {
    Ok(max(v, w))
  }

  /// Given universes `v` and `w`, returns the universe of Sigma types containing `v` and `w`.
  pub fn sig_univ(v: usize, w: usize) -> Result<usize, TypeError<'a, 'b, T>> {
    Ok(max(v, w))
  }

  /// Returns the universe of the unit type.
  pub fn unit_univ() -> Result<usize, TypeError<'a, 'b, T>> {
    Ok(0)
  }
}

impl<'a, 'b> Term<'a, 'b, Core> {
  /// Given `val`, tries elimination as [`Val::Univ`].
  fn as_univ<E>(val: Val<'a, 'b>, err: impl FnOnce(Val<'a, 'b>) -> E) -> Result<usize, E> {
    match val {
      Val::Univ(v) => Ok(v),
      ty => Err(err(ty)),
    }
  }

  /// Given `val`, tries elimination as [`Val::Pi`].
  fn as_pi<E>(val: Val<'a, 'b>, err: impl FnOnce(Val<'a, 'b>) -> E) -> Result<(&'a Val<'a, 'b>, &'a Clos<'a, 'b>), E> {
    match val {
      Val::Pi(t, u) => Ok((t, u)),
      ty => Err(err(ty)),
    }
  }

  /// Given `val`, tries elimination as [`Val::Sig`].
  fn as_sig<E>(val: Val<'a, 'b>, err: impl FnOnce(Val<'a, 'b>) -> E) -> Result<&'a [(&'b Field<'b>, Clos<'a, 'b>)], E> {
    match val {
      Val::Sig(us) => Ok(us),
      ty => Err(err(ty)),
    }
  }

  /// Given preterm `self`, returns the type of `self`. This is mutually recursive with
  /// [`Term::check`], and is the entry point of Coquand’s type checking algorithm.
  ///
  /// - See: <https://www.sciencedirect.com/science/article/pii/0167642395000216>
  /// - See: <https://github.com/AndrasKovacs/elaboration-zoo/blob/master/02-typecheck-closures-debruijn/Main.hs>
  ///
  /// Pre-conditions:
  ///
  /// - `ctx` is well-formed context.
  /// - `env` is well-formed environment.
  pub fn infer(
    &self,
    sig: &Signature<'a, 'b>,
    ctx: &Stack<'a, 'b>,
    env: &Stack<'a, 'b>,
    ar: &'a Arena,
  ) -> Result<(Term<'a, 'b, Named>, Val<'a, 'b>), TypeError<'a, 'b, Core>> {
    match self {
      // The garbage collection mark forces the subterm to be inferred inside a new arena.
      Term::Gc(x) => {
        x.infer(sig, ctx, env, &Arena::new()).map(|(x, v)| (x.relocate(ar), v.relocate(ar))).map_err(|e| e.relocate(ar))
      }
      // The (univ) rule is used.
      Term::Univ(lvl) => Ok(((Term::Univ(*lvl)), Val::Univ(Term::univ_univ(*lvl)?))),
      // The (ann) rule is used.
      // To establish pre-conditions for `eval()` and `check()`, the type of `t` is checked first.
      Term::Ann(x_old, t_old) => {
        let (t_new, t_type) = t_old.infer(sig, ctx, env, ar)?;
        let _ = Term::as_univ(t_type, |t_type| TypeError::type_expected(t_old, t_type, sig, ctx, env, ar))?;
        let t_val = Val::eval(t_old, sig, env, ar)?;
        let x_new = x_old.check(t_val, sig, ctx, env, ar)?;
        Ok(((Term::Ann(ar.term(x_new), ar.term(t_new))), t_val))
      }
      // The (let) and (extend) rules are used.
      // The (ζ) rule is implicitly used on the value (in normal form) from the recursive call.
      Term::Let(info, v_old, x_old) => {
        let (v_new, v_type) = v_old.infer(sig, ctx, env, ar)?;
        let v_val = Val::eval(v_old, sig, env, ar)?;
        let ctx_ext = ctx.extend(info, v_type, ar);
        let env_ext = env.extend(info, v_val, ar);
        let (x_new, x_type) = x_old.infer(sig, &ctx_ext, &env_ext, ar)?;
        Ok(((Term::Let(info, ar.term(v_new), ar.term(x_new))), x_type))
      }
      // The (Π form) and (extend) rules are used.
      Term::Pi(info, t_old, u_old) => {
        let (t_new, t_type) = t_old.infer(sig, ctx, env, ar)?;
        let t_lvl = Term::as_univ(t_type, |t_type| TypeError::type_expected(t_old, t_type, sig, ctx, env, ar))?;
        let ctx_ext = ctx.extend(info, Val::eval(t_old, sig, env, ar)?, ar);
        let env_ext = env.extend(info, Val::Free(env.len()), ar);
        let (u_new, u_type) = u_old.infer(sig, &ctx_ext, &env_ext, ar)?;
        let u_lvl = Term::as_univ(u_type, |u_type| TypeError::type_expected(u_old, u_type, sig, ctx, env, ar))?;
        Ok(((Term::Pi(info, ar.term(t_new), ar.term(u_new))), Val::Univ(Term::pi_univ(t_lvl, u_lvl)?)))
      }
      // Function abstractions must be enclosed in type annotations, or appear as an argument.
      Term::Fun(_, _) => Err(TypeError::ann_expected(ar.term(*self))),
      // The (Π elim) rule is used.
      Term::App(f_old, x_old, dot) => {
        let (f_new, f_type) = f_old.infer(sig, ctx, env, ar)?;
        let (t_val, u_val) = Term::as_pi(f_type, |f_type| TypeError::pi_expected(f_old, f_type, sig, ctx, env, ar))?;
        let x_new = x_old.check(*t_val, sig, ctx, env, ar)?;
        Ok((
          (Term::App(ar.term(f_new), ar.term(x_new), *dot)),
          Val::apply(u_val, Val::eval(x_old, sig, env, ar)?, sig, ar)?,
        ))
      }
      // The (Σ form), (⊤ form) and (extend) rules are used.
      Term::Sig(us_old) => {
        let mut lvl = Term::unit_univ()?;
        let us_new = ar.terms(us_old.len());
        let us_val = ar.closures(us_old.len());
        for (i, (info, u_old)) in us_old.iter().enumerate() {
          us_val[i] = (info, Clos { info: Bound::empty(), env: env.clone(), body: u_old });
        }
        for (i, (info, u_old)) in us_old.iter().enumerate() {
          let t_val = Val::Sig(&us_val[..i]);
          let x_val = Val::Free(env.len());
          let ctx_ext = ctx.extend(Bound::empty(), t_val, ar);
          let env_ext = env.extend(Bound::empty(), x_val, ar);
          let (u_new, u_type) = u_old.infer(sig, &ctx_ext, &env_ext, ar)?;
          let u_lvl = Term::as_univ(u_type, |u_type| TypeError::type_expected(u_old, u_type, sig, ctx, env, ar))?;
          lvl = Term::sig_univ(lvl, u_lvl)?;
          us_new[i] = (*info, u_new);
        }
        Ok(((Term::Sig(us_new)), Val::Univ(lvl)))
      }
      // Tuple constructors must be enclosed in type annotations, or appear as an argument.
      Term::Tup(_) => Err(TypeError::ann_expected(ar.term(*self))),
      // The (Σ init) rule is used.
      Term::Init(n, x_old) => {
        let (x_new, x_type) = x_old.infer(sig, ctx, env, ar)?;
        let us_val = Term::as_sig(x_type, |x_type| TypeError::sig_expected(x_old, x_type, sig, ctx, env, ar))?;
        let m =
          us_val.len().checked_sub(*n).ok_or_else(|| TypeError::sig_init(*n, Val::Sig(us_val), sig, ctx, env, ar))?;
        Ok(((Term::Init(*n, ar.term(x_new))), Val::Sig(&us_val[..m])))
      }
      // The (var) and (Σ proj) rules are used.
      Term::Var(ix) => Term::present_named_var(*ix, None, sig, ctx, env, ar),
      Term::Proj(n, Term::Var(ix)) => Term::present_named_var(*ix, Some(*n), sig, ctx, env, ar),
      Term::Proj(n, x_old) => {
        let (x_new, x_type) = x_old.infer(sig, ctx, env, ar)?;
        Term::present_named_proj(*n, x_old, x_new, x_type, sig, ctx, env, ar)
      }
      // The contexts and environments of holes are unchecked.
      Term::Hole(n) => {
        let hole = sig.get_hole(*n).unwrap();
        assert!(hole.ctx.len() == ctx.len());
        Ok((Term::Hole(*n), hole.ty))
      }
    }
  }

  /// Given preterm `self` and type `t`, checks if `self` has type `t`. This is mutually recursive
  /// with [`Term::infer`].
  ///
  /// Pre-conditions:
  ///
  /// - `ctx` is well-formed context.
  /// - `env` is well-formed environment.
  /// - `t` is well-typed under context `ctx` and environment `env`.
  /// - `t` has universe type under context `ctx` and environment `env`.
  pub fn check(
    &self,
    t: Val<'a, 'b>,
    sig: &Signature<'a, 'b>,
    ctx: &Stack<'a, 'b>,
    env: &Stack<'a, 'b>,
    ar: &'a Arena,
  ) -> Result<Term<'a, 'b, Named>, TypeError<'a, 'b, Core>> {
    match self {
      // The garbage collection mark forces the subterm to be checked inside a new arena.
      Term::Gc(x) => x.check(t, sig, ctx, env, &Arena::new()).map(|x| x.relocate(ar)).map_err(|e| e.relocate(ar)),
      // The (let) and (extend) rules are used.
      // The (ζ) rule is implicitly inversely used on the `t` passed into the recursive call.
      Term::Let(info, v_old, x_old) => {
        let (v_new, v_type) = v_old.infer(sig, ctx, env, ar)?;
        let v_val = Val::eval(v_old, sig, env, ar)?;
        let ctx_ext = ctx.extend(info, v_type, ar);
        let env_ext = env.extend(info, v_val, ar);
        let x_new = x_old.check(t, sig, &ctx_ext, &env_ext, ar)?;
        Ok(Term::Let(info, ar.term(v_new), ar.term(x_new)))
      }
      // The (Π intro) and (extend) rules used.
      // By pre-conditions, `t` is already known to have universe type.
      Term::Fun(info, b_old) => {
        let (t_val, u_val) = Term::as_pi(t, |t| TypeError::pi_ann_expected(t, sig, ctx, env, ar))?;
        let x_val = Val::Free(env.len());
        let ctx_ext = ctx.extend(info, *t_val, ar);
        let env_ext = env.extend(info, x_val, ar);
        let b_new = b_old.check(Val::apply(u_val, x_val, sig, ar)?, sig, &ctx_ext, &env_ext, ar)?;
        Ok(Term::Fun(info, ar.term(b_new)))
      }
      // The (∑ intro) and (extend) rules are used.
      // By pre-conditions, `t` is already known to have universe type.
      Term::Tup(bs_old) => {
        let us_val = Term::as_sig(t, |t| TypeError::sig_ann_expected(t, sig, ctx, env, ar))?;
        if bs_old.len() == us_val.len() {
          let bs_new = ar.terms(bs_old.len());
          let bs_val = ar.values(bs_old.len()).as_mut_ptr();
          for (i, (info, b_old)) in bs_old.iter().enumerate() {
            let (u_info, u_val) = &us_val[i];
            if info.name != u_info.name {
              return Err(TypeError::tup_field_mismatch(ar.term(*self), info.name, u_info.name));
            }
            let t_val = Val::Sig(&us_val[..i]);
            // SAFETY: the borrowed range `&bs_val[..i]` is no longer modified.
            let a_val = Val::Tup(unsafe { from_raw_parts(bs_val, i) });
            let ctx_ext = ctx.extend(Bound::empty(), t_val, ar);
            let env_ext = env.extend(Bound::empty(), a_val, ar);
            let b_new = b_old.check(Val::apply(u_val, a_val, sig, ar)?, sig, &ctx_ext, &env_ext, ar)?;
            bs_new[i] = (info, b_new);
            let b_val = Val::eval(b_old, sig, &env_ext, ar)?;
            // SAFETY: `i < bs_old.len()` which is the valid size of `bs_val`.
            unsafe { *bs_val.add(i) = (info, b_val) };
          }
          Ok(Term::Tup(bs_new))
        } else {
          Err(TypeError::tup_size_mismatch(ar.term(*self), bs_old.len(), us_val.len()))
        }
      }
      // The (conv) rule is used.
      // By pre-conditions, `t` is already known to have universe type.
      x_old => {
        let (x_new, x_type) = x_old.infer(sig, ctx, env, ar)?;
        let res = Val::conv(&x_type, &t, sig, env.len(), ar)?.then_some(x_new);
        res.ok_or_else(|| TypeError::type_mismatch(ar.term(*x_old), x_type, t, sig, ctx, env, ar))
      }
    }
  }

  /// Presents a variable as a named variable and returns its type.
  pub fn present_named_var(
    ix: usize,
    proj: Option<usize>,
    sig: &Signature<'a, 'b>,
    ctx: &Stack<'a, 'b>,
    env: &Stack<'a, 'b>,
    ar: &'a Arena,
  ) -> Result<(Term<'a, 'b, Named>, Val<'a, 'b>), TypeError<'a, 'b, Core>> {
    let (info, t_val) = ctx.get(ix, ar).ok_or_else(|| TypeError::ctx_index(ix, ctx.len()))?;
    match proj {
      None => match ctx.is_name_valid(ix, proj, info.name, env, ar) {
        true => Ok((Term::NamedVar(info.name, ()), t_val)),
        false => Ok((Term::Var(ix), t_val)),
      },
      Some(n) => {
        let us_val =
          Term::as_sig(t_val, |t_val| TypeError::sig_expected(ar.term(Term::Var(ix)), t_val, sig, ctx, env, ar))?;
        let i =
          us_val.len().checked_sub(n + 1).ok_or_else(|| TypeError::sig_proj(n, Val::Sig(us_val), sig, ctx, env, ar))?;
        let (info, u_val) = &us_val[i];
        let u_val = Val::apply(u_val, Val::eval(&Term::Init(n + 1, ar.term(Term::Var(ix))), sig, env, ar)?, sig, ar)?;
        match ctx.is_name_valid(ix, proj, info.name, env, ar) {
          true => Ok((Term::NamedVar(info.name, ()), u_val)),
          false => Ok((Term::Proj(n, ar.term(Term::Var(ix))), u_val)),
        }
      }
    }
  }

  /// Presents a projection as a named projection and returns its type.
  pub fn present_named_proj(
    n: usize,
    x_old: &'a Term<'a, 'b, Core>,
    x_new: Term<'a, 'b, Named>,
    x_type: Val<'a, 'b>,
    sig: &Signature<'a, 'b>,
    ctx: &Stack<'a, 'b>,
    env: &Stack<'a, 'b>,
    ar: &'a Arena,
  ) -> Result<(Term<'a, 'b, Named>, Val<'a, 'b>), TypeError<'a, 'b, Core>> {
    let us_val = Term::as_sig(x_type, |x_type| TypeError::sig_expected(x_old, x_type, sig, ctx, env, ar))?;
    let i =
      us_val.len().checked_sub(n + 1).ok_or_else(|| TypeError::sig_proj(n, Val::Sig(us_val), sig, ctx, env, ar))?;
    let (info, u_val) = &us_val[i];
    let u_val = Val::apply(u_val, Val::eval(&Term::Init(n + 1, x_old), sig, env, ar)?, sig, ar)?;
    match !info.name.is_empty() && !us_val.iter().rev().take(n).any(|(i, _)| i.name == info.name) {
      true => Ok((Term::NamedProj(info.name, ar.term(x_new), ()), u_val)),
      false => Ok((Term::Proj(n, ar.term(x_new)), u_val)),
    }
  }
}
