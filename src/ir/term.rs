use std::cmp::max;
use std::fmt::{Debug, Display};
use std::slice::from_raw_parts;

use super::*;
use crate::arena::{Arena, Relocate};

pub trait Decoration: Debug + Clone + Copy {
  type NamedVar<'b>: Debug + Display + Clone + Copy;
  type NamedProj<'b>: Debug + Display + Clone + Copy;
}

#[derive(Debug, Clone, Copy)]
pub struct Core;

#[derive(Debug, Clone, Copy)]
pub struct Named;

impl Decoration for Core {
  type NamedVar<'b> = !;
  type NamedProj<'b> = !;
}

impl Decoration for Named {
  type NamedVar<'b> = &'b str;
  type NamedProj<'b> = &'b str;
}

/// # Binder information
///
/// Auxiliary information for bound variables (e.g. names, attributes).
#[derive(Debug, Clone, Copy)]
pub struct Bound<'b> {
  pub name: &'b str,
  pub attrs: &'b [&'b str],
}

/// # Field information
///
/// Auxiliary information for field variables (e.g. names, attributes).
#[derive(Debug, Clone, Copy)]
pub struct Field<'b> {
  pub name: &'b str,
  pub attrs: &'b [&'b str],
}

/// # Terms
///
/// Terms of the core calculus.
///
/// Can be understood as the "source code" given to the evaluator.
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
  Meta(usize),
  /// Named variables.
  NamedVar(T::NamedVar<'b>),
  /// Named projections. To preserve covariance w.r.t. `'a`, this has to be hard-coded.
  NamedProj(T::NamedProj<'b>, &'a Self),
}

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

/// # Linked list stacks
///
/// The baseline implementation of evaluation environments. Cheap to append and clone, but random
/// access takes linear time. This is acceptable if most of the context is wrapped inside tuples,
/// which have constant-time random access.
#[derive(Debug, Clone)]
pub enum Stack<'a, 'b> {
  Nil,
  Cons { prev: &'a Self, info: &'b Bound<'b>, value: Val<'a, 'b> },
}

impl<'b> Bound<'b> {
  /// Creates a new bound variable info with empty name (i.e. transparent).
  pub fn empty() -> &'b Self {
    &Self { name: "", attrs: &[] }
  }

  /// Creates a new bound variable info in the given arena.
  pub fn new(name: &str, attrs: &[&str], ar: &'b Arena) -> Self {
    Self { name: ar.string(name), attrs: ar.strings(attrs) }
  }
}

impl<'b> Field<'b> {
  /// Creates a new field variable info with empty name (i.e. transparent).
  pub fn empty() -> &'b Self {
    &Self { name: "", attrs: &[] }
  }

  /// Creates a new field variable info in the given arena.
  pub fn new(name: &str, attrs: &[&str], ar: &'b Arena) -> Self {
    Self { name: ar.string(name), attrs: ar.strings(attrs) }
  }
}

impl<'a, 'b> Stack<'a, 'b> {
  /// Creates an empty stack.
  pub fn new(_: &'a Arena) -> Self {
    Stack::Nil
  }

  /// Returns if the stack is empty.
  pub fn is_empty(&self) -> bool {
    match self {
      Stack::Nil => true,
      Stack::Cons { prev: _, info: _, value: _ } => false,
    }
  }

  /// Returns the length of the stack.
  pub fn len(&self) -> usize {
    let mut curr = self;
    let mut len = 0;
    while let Stack::Cons { prev, info: _, value: _ } = curr {
      len += 1;
      curr = prev;
    }
    len
  }

  /// Returns the value at the given de Bruijn index, if it exists.
  pub fn get(&self, index: usize, ar: &'a Arena) -> Option<Val<'a, 'b>> {
    let mut curr = self;
    let mut index = index;
    ar.inc_lookup_count();
    while let Stack::Cons { prev, info: _, value } = curr {
      ar.inc_link_count();
      if index == 0 {
        return Some(*value);
      }
      index -= 1;
      curr = prev;
    }
    None
  }

  /// Extends the stack with a new value.
  pub fn extend(&self, info: &'b Bound<'b>, value: Val<'a, 'b>, ar: &'a Arena) -> Self {
    Stack::Cons { prev: ar.frame(self.clone()), info, value }
  }
}

impl<'a, 'b> Term<'a, 'b, Core> {
  /// Reduces `self` so that all `let`s are collected into the environment and then frozen at
  /// binders. This is mutually recursive with [`Clos::apply`], forming an eval-apply loop.
  ///
  /// Pre-conditions:
  ///
  /// - `self` is well-typed under a context and environment `env` (to ensure termination).
  pub fn eval(&self, env: &Stack<'a, 'b>, ar: &'a Arena) -> Result<Val<'a, 'b>, EvalError<'a, 'b>> {
    match self {
      // The garbage collection mark forces the subterm to be evaluated inside a new arena.
      Term::Gc(x) => x.eval(env, &Arena::new()).map(|v| v.relocate(ar)).map_err(|e| e.relocate(ar)),
      // Universes are already in normal form.
      Term::Univ(v) => Ok(Val::Univ(*v)),
      // The (δ) rule is always applied.
      // Variables of values are in de Bruijn levels, so weakening is no-op.
      Term::Var(ix) => env.get(*ix, ar).ok_or_else(|| EvalError::env_index(*ix, env.len())),
      // The (τ) rule is always applied.
      Term::Ann(x, _) => x.eval(env, ar),
      // For `let`s, we reduce the value, collect it into the environment to reduce the body.
      Term::Let(i, v, x) => x.eval(&env.extend(i, v.eval(env, ar)?, ar), ar),
      // For binders, we freeze the whole environment and store the body as a closure.
      Term::Pi(i, t, u) => Ok(Val::Pi(ar.val(t.eval(env, ar)?), ar.clos(Clos { info: i, env: env.clone(), body: u }))),
      Term::Fun(i, b) => Ok(Val::Fun(ar.clos(Clos { info: i, env: env.clone(), body: b }))),
      // For applications, we reduce both operands and combine them back.
      // In the case of a redex, the (β) rule is applied.
      Term::App(f, x, b) => match (f.eval(env, ar)?, x.eval(env, ar)?) {
        (Val::Fun(b), x) => b.apply(x, ar),
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
          let b = b.eval(&env.extend(Bound::empty(), a, ar), ar)?;
          // SAFETY: `i < bs.len()` which is the valid size of `vs`.
          unsafe { *vs.add(i) = (info, b) };
        }
        // SAFETY: the borrowed slice `&vs` has valid size `bs.len()` and is no longer modified.
        Ok(Val::Tup(unsafe { from_raw_parts(vs, bs.len()) }))
      }
      // For initials (i.e. iterated first projections), we reduce the operand and combine it back.
      // In the case of a redex, the (π init) rule is applied.
      Term::Init(n, x) => match x.eval(env, ar)? {
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
      Term::Proj(n, x) => match x.eval(env, ar)? {
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
}

impl<'a, 'b> Clos<'a, 'b> {
  /// Inserts a new `let` around the body after the frozen `let`s, and reduces the body under the
  /// empty environment populated with all `let`s. This is mutually recursive with [`Term::eval`],
  /// forming an eval-apply loop.
  pub fn apply(&'a self, x: Val<'a, 'b>, ar: &'a Arena) -> Result<Val<'a, 'b>, EvalError<'a, 'b>> {
    let Self { env, info, body } = self;
    body.eval(&Stack::Cons { prev: env, info, value: x }, ar)
  }
}

impl<'a, 'b> Val<'a, 'b> {
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
      Val::Pi(t, u) => {
        Ok(Term::Pi(u.info, ar.term(t.quote(len, ar)?), ar.term(u.apply(Val::Free(len), ar)?.quote(len + 1, ar)?)))
      }
      Val::Fun(b) => Ok(Term::Fun(b.info, ar.term(b.apply(Val::Free(len), ar)?.quote(len + 1, ar)?))),
      Val::App(f, x, b) => Ok(Term::App(ar.term(f.quote(len, ar)?), ar.term(x.quote(len, ar)?), *b)),
      Val::Sig(us) => {
        let terms = ar.terms(us.len());
        for (term, (info, u)) in terms.iter_mut().zip(us.iter()) {
          *term = (info, u.apply(Val::Free(len), ar)?.quote(len + 1, ar)?);
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
          && Val::conv(&v.apply(Val::Free(len), ar)?, &w.apply(Val::Free(len), ar)?, len + 1, ar)?,
      ),
      (Val::Fun(b), Val::Fun(c)) => {
        Ok(Val::conv(&b.apply(Val::Free(len), ar)?, &c.apply(Val::Free(len), ar)?, len + 1, ar)?)
      }
      (Val::App(f, x, _), Val::App(g, y, _)) => Ok(Val::conv(f, g, len, ar)? && Val::conv(x, y, len, ar)?),
      (Val::Sig(us), Val::Sig(vs)) if us.len() == vs.len() => {
        for ((i, u), (j, v)) in us.iter().zip(vs.iter()) {
          if i.name != j.name {
            return Ok(false);
          }
          if !Val::conv(&u.apply(Val::Free(len), ar)?, &v.apply(Val::Free(len), ar)?, len + 1, ar)? {
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

  /// Given `self`, tries elimination as [`Val::Univ`].
  pub fn as_univ<E>(self, err: impl FnOnce(Self) -> E) -> Result<usize, E> {
    match self {
      Val::Univ(v) => Ok(v),
      ty => Err(err(ty)),
    }
  }

  /// Given `self`, tries elimination as [`Val::Pi`].
  pub fn as_pi<E>(self, err: impl FnOnce(Self) -> E) -> Result<(&'a Val<'a, 'b>, &'a Clos<'a, 'b>), E> {
    match self {
      Val::Pi(t, u) => Ok((t, u)),
      ty => Err(err(ty)),
    }
  }

  /// Given `self`, tries elimination as [`Val::Sig`].
  pub fn as_sig<E>(self, err: impl FnOnce(Self) -> E) -> Result<&'a [(&'b Field<'b>, Clos<'a, 'b>)], E> {
    match self {
      Val::Sig(us) => Ok(us),
      ty => Err(err(ty)),
    }
  }
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
    ctx: &Stack<'a, 'b>,
    env: &Stack<'a, 'b>,
    ar: &'a Arena,
  ) -> Result<(Term<'a, 'b, Named>, Val<'a, 'b>), TypeError<'a, 'b, Core>> {
    // Special case for projections on a variable.
    if let Term::Var(_) | Term::Proj(_, _) = self {
      let mut projs = Vec::new();
      let mut term = self;
      while let Term::Proj(n, x) = term {
        projs.push(*n);
        term = x;
      }
      if let Term::Var(_ix) = term {
        projs.reverse();
        // TODO
        // return Named::present_name(*ix, &projs, ctx, env, ar);
        todo!()
      }
    }
    match self {
      // The garbage collection mark forces the subterm to be inferred inside a new arena.
      Term::Gc(x) => {
        x.infer(ctx, env, &Arena::new()).map(|(x, v)| (x.relocate(ar), v.relocate(ar))).map_err(|e| e.relocate(ar))
      }
      // The (univ) rule is used.
      Term::Univ(lvl) => Ok(((Term::Univ(*lvl)), Val::Univ(Term::univ_univ(*lvl)?))),
      // The (var) rule is used.
      // Variables of values are in de Bruijn levels, so weakening is no-op.
      Term::Var(ix) => {
        let t_val = ctx.get(*ix, ar).ok_or_else(|| TypeError::ctx_index(*ix, ctx.len()))?;
        Ok(((Term::Var(*ix)), t_val))
      }
      // The (ann) rule is used.
      // To establish pre-conditions for `eval()` and `check()`, the type of `t` is checked first.
      Term::Ann(x_old, t_old) => {
        let (t_new, t_type) = t_old.infer(ctx, env, ar)?;
        let _ = t_type.as_univ(|t_type| TypeError::type_expected(t_old, t_type, ctx, env, ar))?;
        let t_val = t_old.eval(env, ar)?;
        let x_new = x_old.check(t_val, ctx, env, ar)?;
        Ok(((Term::Ann(ar.term(x_new), ar.term(t_new))), t_val))
      }
      // The (let) and (extend) rules are used.
      // The (ζ) rule is implicitly used on the value (in normal form) from the recursive call.
      Term::Let(info, v_old, x_old) => {
        let (v_new, v_type) = v_old.infer(ctx, env, ar)?;
        let v_val = v_old.eval(env, ar)?;
        let ctx_ext = ctx.extend(info, v_type, ar);
        let env_ext = env.extend(info, v_val, ar);
        let (x_new, x_type) = x_old.infer(&ctx_ext, &env_ext, ar)?;
        Ok(((Term::Let(info, ar.term(v_new), ar.term(x_new))), x_type))
      }
      // The (Π form) and (extend) rules are used.
      Term::Pi(info, t_old, u_old) => {
        let (t_new, t_type) = t_old.infer(ctx, env, ar)?;
        let t_lvl = t_type.as_univ(|t_type| TypeError::type_expected(t_old, t_type, ctx, env, ar))?;
        let ctx_ext = ctx.extend(info, t_old.eval(env, ar)?, ar);
        let env_ext = env.extend(info, Val::Free(env.len()), ar);
        let (u_new, u_type) = u_old.infer(&ctx_ext, &env_ext, ar)?;
        let u_lvl = u_type.as_univ(|u_type| TypeError::type_expected(u_old, u_type, ctx, env, ar))?;
        Ok(((Term::Pi(info, ar.term(t_new), ar.term(u_new))), Val::Univ(Term::pi_univ(t_lvl, u_lvl)?)))
      }
      // Function abstractions must be enclosed in type annotations, or appear as an argument.
      Term::Fun(_, _) => Err(TypeError::ann_expected(ar.term(*self))),
      // The (Π elim) rule is used.
      Term::App(f_old, x_old, dot) => {
        let (f_new, f_type) = f_old.infer(ctx, env, ar)?;
        let (t_val, u_val) = f_type.as_pi(|f_type| TypeError::pi_expected(f_old, f_type, ctx, env, ar))?;
        let x_new = x_old.check(*t_val, ctx, env, ar)?;
        Ok(((Term::App(ar.term(f_new), ar.term(x_new), *dot)), u_val.apply(x_old.eval(env, ar)?, ar)?))
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
          let (u_new, u_type) = u_old.infer(&ctx_ext, &env_ext, ar)?;
          let u_lvl = u_type.as_univ(|u_type| TypeError::type_expected(u_old, u_type, ctx, env, ar))?;
          lvl = Term::sig_univ(lvl, u_lvl)?;
          us_new[i] = (*info, u_new);
        }
        Ok(((Term::Sig(us_new)), Val::Univ(lvl)))
      }
      // Tuple constructors must be enclosed in type annotations, or appear as an argument.
      Term::Tup(_) => Err(TypeError::ann_expected(ar.term(*self))),
      // The (Σ init) rule is used.
      Term::Init(n, x_old) => {
        let (x_new, x_type) = x_old.infer(ctx, env, ar)?;
        let us_val = x_type.as_sig(|x_type| TypeError::sig_expected(x_old, x_type, ctx, env, ar))?;
        let m = us_val.len().checked_sub(*n).ok_or_else(|| TypeError::sig_init(*n, Val::Sig(us_val), ctx, env, ar))?;
        Ok(((Term::Init(*n, ar.term(x_new))), Val::Sig(&us_val[..m])))
      }
      // The (Σ proj) rule is used.
      Term::Proj(n, x_old) => {
        let (x_new, x_type) = x_old.infer(ctx, env, ar)?;
        let us_val = x_type.as_sig(|x_type| TypeError::sig_expected(x_old, x_type, ctx, env, ar))?;
        let i =
          us_val.len().checked_sub(n + 1).ok_or_else(|| TypeError::sig_proj(*n, Val::Sig(us_val), ctx, env, ar))?;
        Ok(((Term::Proj(*n, ar.term(x_new))), us_val[i].1.apply(Term::Init(n + 1, x_old).eval(env, ar)?, ar)?))
      }
      // Holes must be enclosed in type annotations, or appear as an argument.
      Term::Meta(_) => Err(TypeError::ann_expected(ar.term(*self))),
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
    ctx: &Stack<'a, 'b>,
    env: &Stack<'a, 'b>,
    ar: &'a Arena,
  ) -> Result<Term<'a, 'b, Named>, TypeError<'a, 'b, Core>> {
    match self {
      // The garbage collection mark forces the subterm to be checked inside a new arena.
      Term::Gc(x) => x.check(t, ctx, env, &Arena::new()).map(|x| x.relocate(ar)).map_err(|e| e.relocate(ar)),
      // The (let) and (extend) rules are used.
      // The (ζ) rule is implicitly inversely used on the `t` passed into the recursive call.
      Term::Let(info, v_old, x_old) => {
        let (v_new, v_type) = v_old.infer(ctx, env, ar)?;
        let v_val = v_old.eval(env, ar)?;
        let ctx_ext = ctx.extend(info, v_type, ar);
        let env_ext = env.extend(info, v_val, ar);
        let x_new = x_old.check(t, &ctx_ext, &env_ext, ar)?;
        Ok(Term::Let(info, ar.term(v_new), ar.term(x_new)))
      }
      // The (Π intro) and (extend) rules is used.
      // By pre-conditions, `t` is already known to have universe type.
      Term::Fun(info, b_old) => {
        let (t_val, u_val) = t.as_pi(|t| TypeError::pi_ann_expected(t, ctx, env, ar))?;
        let x_val = Val::Free(env.len());
        let ctx_ext = ctx.extend(info, *t_val, ar);
        let env_ext = env.extend(info, x_val, ar);
        let b_new = b_old.check(u_val.apply(x_val, ar)?, &ctx_ext, &env_ext, ar)?;
        Ok(Term::Fun(info, ar.term(b_new)))
      }
      // The (∑ intro) and (extend) rules are used.
      // By pre-conditions, `t` is already known to have universe type.
      Term::Tup(bs_old) => {
        let us_val = t.as_sig(|t| TypeError::sig_ann_expected(t, ctx, env, ar))?;
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
            let b_new = b_old.check(u_val.apply(a_val, ar)?, &ctx_ext, &env_ext, ar)?;
            bs_new[i] = (info, b_new);
            let b_val = b_old.eval(&env_ext, ar)?;
            // SAFETY: `i < bs_old.len()` which is the valid size of `bs_val`.
            unsafe { *bs_val.add(i) = (info, b_val) };
          }
          Ok(Term::Tup(bs_new))
        } else {
          Err(TypeError::tup_size_mismatch(ar.term(*self), bs_old.len(), us_val.len()))
        }
      }
      // Holes in the core syntax cannot be checked.
      Term::Meta(_) => todo!(),
      // The (conv) rule is used.
      // By pre-conditions, `t` is already known to have universe type.
      x_old => {
        let (x_new, x_type) = x_old.infer(ctx, env, ar)?;
        let res = Val::conv(&x_type, &t, env.len(), ar)?.then_some(x_new);
        res.ok_or_else(|| TypeError::type_mismatch(ar.term(*x_old), x_type, t, ctx, env, ar))
      }
    }
  }
}
