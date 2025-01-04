use std::cmp::max;
use std::slice::from_raw_parts;

use super::*;

/// # Terms
///
/// Terms of the core calculus.
///
/// Can be understood as the "source code" given to the evaluator.
#[derive(Debug, Clone, Copy)]
pub enum Term<'a> {
  /// Universe in levels.
  Univ(usize),
  /// Variables in de Bruijn indices.
  Var(usize),
  /// Type annotations (value, type, arena boundary flag).
  Ann(&'a Term<'a>, &'a Term<'a>, bool),
  /// Let expressions (value, *body*).
  Let(&'a Term<'a>, &'a Term<'a>),
  /// Function types (parameter type, *return type*).
  Pi(&'a Term<'a>, &'a Term<'a>),
  /// Function abstractions (*body*).
  Fun(&'a Term<'a>),
  /// Function applications (function, argument).
  App(&'a Term<'a>, &'a Term<'a>),
  /// Tuple types (*element types*).
  Sig(&'a [Term<'a>]),
  /// Tuple constructors (*element values*).
  Tup(&'a [Term<'a>]),
  /// Tuple initial segments (truncation, tuple).
  Init(usize, &'a Term<'a>),
  /// Tuple projections (index, tuple).
  Proj(usize, &'a Term<'a>),
}

/// # Values
///
/// Values are terms whose outermost `let`s are already collected and frozen at binders.
///
/// Can be understood as "runtime objects" produced by the evaluator.
#[derive(Debug, Clone, Copy)]
pub enum Val<'a> {
  /// Universe in levels.
  Univ(usize),
  /// Free variables in de Bruijn *levels* for cheap weakening.
  Free(usize),
  /// Function types (parameter type, *return type*).
  Pi(&'a Val<'a>, &'a Clos<'a>),
  /// Function abstractions (*body*).
  Fun(&'a Clos<'a>),
  /// Function applications (function, argument).
  App(&'a Val<'a>, &'a Val<'a>),
  /// Tuple types (*element types*).
  Sig(&'a [Clos<'a>]),
  /// Tuple constructors (element values).
  Tup(&'a [Val<'a>]),
  /// Tuple initial segments (truncation, tuple).
  Init(usize, &'a Val<'a>),
  /// Tuple projections (index, tuple).
  Proj(usize, &'a Val<'a>),
}

/// # Closures
///
/// Closures are terms annotated with frozen `let`s capturing the whole environment.
///
/// The environment is represented using a special data structure which supports structural sharing
/// and fast random access (in most cases). For more details, see the documentation for [`Stack`].
#[derive(Debug, Clone, Copy)]
pub struct Clos<'a> {
  pub env: Stack<'a>,
  pub body: &'a Term<'a>,
}

/// # Linked list stacks
///
/// The baseline implementation of evaluation environments. Cheap to append and clone, but random
/// access takes linear time. This is acceptable if most of the context is wrapped inside tuples,
/// which have constant-time random access.
#[derive(Debug, Clone, Copy)]
pub enum Stack<'a> {
  Nil,
  Cons { prev: &'a Stack<'a>, value: Val<'a> },
}

impl Term<'_> {
  /// Clones `self` to given arena, expected to be used for outputs and error reporting.
  pub fn relocate<'a>(&self, ar: &'a Arena) -> &'a Term<'a> {
    match self {
      Term::Univ(v) => ar.term(Term::Univ(*v)),
      Term::Var(ix) => ar.term(Term::Var(*ix)),
      Term::Ann(x, t, b) => ar.term(Term::Ann(x.relocate(ar), t.relocate(ar), *b)),
      Term::Let(v, x) => ar.term(Term::Let(v.relocate(ar), x.relocate(ar))),
      Term::Pi(t, u) => ar.term(Term::Pi(t.relocate(ar), u.relocate(ar))),
      Term::Fun(b) => ar.term(Term::Fun(b.relocate(ar))),
      Term::App(f, x) => ar.term(Term::App(f.relocate(ar), x.relocate(ar))),
      Term::Sig(us) => {
        let terms = ar.terms(us.len());
        for (term, u) in terms.iter_mut().zip(us.iter()) {
          *term = *u.relocate(ar);
        }
        ar.term(Term::Sig(terms))
      }
      Term::Tup(bs) => {
        let terms = ar.terms(bs.len());
        for (term, b) in terms.iter_mut().zip(bs.iter()) {
          *term = *b.relocate(ar);
        }
        ar.term(Term::Tup(terms))
      }
      Term::Init(n, x) => ar.term(Term::Init(*n, x.relocate(ar))),
      Term::Proj(n, x) => ar.term(Term::Proj(*n, x.relocate(ar))),
    }
  }
}

impl<'a> Stack<'a> {
  /// Creates an empty stack.
  pub fn new(_: &'a Arena) -> Self {
    Stack::Nil
  }

  /// Returns if the stack is empty.
  pub fn is_empty(&self) -> bool {
    match self {
      Stack::Nil => true,
      Stack::Cons { prev: _, value: _ } => false,
    }
  }

  /// Returns the length of the stack.
  pub fn len(&self) -> usize {
    let mut curr = self;
    let mut len = 0;
    while let Stack::Cons { prev, value: _ } = curr {
      len += 1;
      curr = prev;
    }
    len
  }

  /// Returns the value at the given de Bruijn index, if it exists.
  pub fn get(&self, index: usize, ar: &'a Arena) -> Option<Val<'a>> {
    let mut curr = self;
    let mut index = index;
    ar.inc_lookup_count();
    while let Stack::Cons { prev, value } = curr {
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
  pub fn extend(&self, value: Val<'a>, ar: &'a Arena) -> Self {
    Stack::Cons { prev: ar.frame(*self), value }
  }
}

impl<'a> Term<'a> {
  /// Reduces `self` so that all `let`s are collected into the environment and then frozen at
  /// binders. This is mutually recursive with [`Clos::apply`], forming an eval-apply loop.
  ///
  /// Pre-conditions:
  ///
  /// - `self` is well-typed under a context and environment `env` (to ensure termination).
  pub fn eval(&self, env: &Stack<'a>, ar: &'a Arena) -> Result<Val<'a>, EvalError> {
    match self {
      // Universes are already in normal form.
      Term::Univ(v) => Ok(Val::Univ(*v)),
      // The (δ) rule is always applied.
      // Variables of values are in de Bruijn levels, so weakening is no-op.
      Term::Var(ix) => env.get(*ix, ar).ok_or_else(|| EvalError::env_index(*ix, env.len())),
      // The (τ) rule is always applied.
      Term::Ann(x, _, _) => x.eval(env, ar),
      // For `let`s, we reduce the value, collect it into the environment to reduce the body.
      Term::Let(v, x) => x.eval(&env.extend(v.eval(env, ar)?, ar), ar),
      // For binders, we freeze the whole environment and store the body as a closure.
      Term::Pi(t, u) => Ok(Val::Pi(ar.val(t.eval(env, ar)?), ar.clos(Clos { env: *env, body: u }))),
      Term::Fun(b) => Ok(Val::Fun(ar.clos(Clos { env: *env, body: b }))),
      // For applications, we reduce both operands and combine them back.
      // In the case of a redex, the (β) rule is applied.
      Term::App(f, x) => match (f.eval(env, ar)?, x.eval(env, ar)?) {
        (Val::Fun(b), x) => b.apply(x, ar),
        (f, x) => Ok(Val::App(ar.val(f), ar.val(x))),
      },
      // For binders, we freeze the whole environment and store the body as a closure.
      Term::Sig(us) => {
        let cs = ar.closures(us.len());
        for (i, u) in us.iter().enumerate() {
          cs[i] = Clos { env: *env, body: u };
        }
        Ok(Val::Sig(cs))
      }
      Term::Tup(bs) => {
        let vs = ar.values(bs.len()).as_mut_ptr();
        for (i, b) in bs.iter().enumerate() {
          // SAFETY: the borrowed range `&vs[..i]` is no longer modified.
          let a = Val::Tup(unsafe { from_raw_parts(vs, i) });
          // SAFETY: `i < bs.len()` which is the valid size of `vs`.
          unsafe { *vs.add(i) = b.eval(&env.extend(a, ar), ar)? };
        }
        // SAFETY: the borrowed slice `&vs` has valid size `bs.len()` and is no longer modified.
        Ok(Val::Tup(unsafe { from_raw_parts(vs, bs.len()) }))
      }
      // For initials (i.e. iterated first projections), we reduce the operand and combine it back.
      // In the case of a redex, the (π init) rule is applied.
      Term::Init(n, x) => match x.eval(env, ar)? {
        Val::Init(m, y) => Ok(Val::Init(n + m, y)),
        Val::Tup(bs) => {
          let m = bs.len().checked_sub(*n).ok_or_else(|| EvalError::tup_init(*n, bs.len()))?;
          Ok(Val::Tup(&bs[..m]))
        }
        x => Ok(Val::Init(*n, ar.val(x))),
      },
      // For projections (i.e. second projections after iterated first projections), we reduce the
      // operand and combine it back.
      // In the case of a redex, the (π last) rule is applied.
      Term::Proj(n, x) => match x.eval(env, ar)? {
        Val::Init(m, y) => Ok(Val::Proj(n + m, y)),
        Val::Tup(bs) => {
          let i = bs.len().checked_sub(n + 1).ok_or_else(|| EvalError::tup_proj(*n, bs.len()))?;
          Ok(bs[i])
        }
        x => Ok(Val::Proj(*n, ar.val(x))),
      },
    }
  }
}

impl<'a> Clos<'a> {
  /// Inserts a new `let` around the body after the frozen `let`s, and reduces the body under the
  /// empty environment populated with all `let`s. This is mutually recursive with [`Term::eval`],
  /// forming an eval-apply loop.
  pub fn apply(&self, x: Val<'a>, ar: &'a Arena) -> Result<Val<'a>, EvalError> {
    let Self { env, body } = self;
    body.eval(&env.extend(x, ar), ar)
  }
}

impl<'a> Val<'a> {
  /// Reduces well-typed `self` to eliminate `let`s and convert it back into a [`Term`].
  /// Can be an expensive operation. Expected to be used for outputs and error reporting.
  ///
  /// Pre-conditions:
  ///
  /// - `self` is well-typed under a context with size `len` (to ensure termination).
  pub fn quote(&self, len: usize, ar: &'a Arena) -> Result<&'a Term<'a>, EvalError> {
    match self {
      Val::Univ(v) => Ok(ar.term(Term::Univ(*v))),
      Val::Free(i) => Ok(ar.term(Term::Var(len.checked_sub(i + 1).ok_or_else(|| EvalError::gen_level(*i, len))?))),
      Val::Pi(t, u) => Ok(ar.term(Term::Pi(t.quote(len, ar)?, u.apply(Val::Free(len), ar)?.quote(len + 1, ar)?))),
      Val::Fun(b) => Ok(ar.term(Term::Fun(b.apply(Val::Free(len), ar)?.quote(len + 1, ar)?))),
      Val::App(f, x) => Ok(ar.term(Term::App(f.quote(len, ar)?, x.quote(len, ar)?))),
      Val::Sig(us) => {
        let terms = ar.terms(us.len());
        for (term, u) in terms.iter_mut().zip(us.iter()) {
          *term = *u.apply(Val::Free(len), ar)?.quote(len + 1, ar)?;
        }
        Ok(ar.term(Term::Sig(terms)))
      }
      Val::Tup(bs) => {
        let terms = ar.terms(bs.len());
        for (term, b) in terms.iter_mut().zip(bs.iter()) {
          *term = *b.quote(len + 1, ar)?;
        }
        Ok(ar.term(Term::Tup(terms)))
      }
      Val::Init(n, x) => Ok(ar.term(Term::Init(*n, x.quote(len, ar)?))),
      Val::Proj(n, x) => Ok(ar.term(Term::Proj(*n, x.quote(len, ar)?))),
    }
  }

  /// Returns if `self` and `other` are definitionally equal. Can be an expensive operation if
  /// they are indeed definitionally equal.
  ///
  /// Pre-conditions:
  ///
  /// - `self` and `other` are well-typed under a context with size `len` (to ensure termination).
  pub fn conv(&self, other: &Self, len: usize, ar: &'a Arena) -> Result<bool, EvalError> {
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
      (Val::App(f, x), Val::App(g, y)) => Ok(Val::conv(f, g, len, ar)? && Val::conv(x, y, len, ar)?),
      (Val::Sig(us), Val::Sig(vs)) if us.len() == vs.len() => {
        for (u, v) in us.iter().zip(vs.iter()) {
          if !Val::conv(&u.apply(Val::Free(len), ar)?, &v.apply(Val::Free(len), ar)?, len + 1, ar)? {
            return Ok(false);
          }
        }
        Ok(true)
      }
      (Val::Tup(bs), Val::Tup(cs)) if bs.len() == cs.len() => {
        for (b, c) in bs.iter().zip(cs.iter()) {
          if !Val::conv(b, c, len, ar)? {
            return Ok(false);
          }
        }
        Ok(true)
      }
      (Val::Init(n, x), Val::Init(m, y)) => Ok(n == m && Val::conv(x, y, len, ar)?),
      (Val::Proj(n, x), Val::Proj(m, y)) => Ok(n == m && Val::conv(x, y, len, ar)?),
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
  pub fn as_pi<E>(self, err: impl FnOnce(Self) -> E) -> Result<(&'a Val<'a>, &'a Clos<'a>), E> {
    match self {
      Val::Pi(t, u) => Ok((t, u)),
      ty => Err(err(ty)),
    }
  }

  /// Given `self`, tries elimination as [`Val::Sig`].
  pub fn as_sig<E>(self, err: impl FnOnce(Self) -> E) -> Result<&'a [Clos<'a>], E> {
    match self {
      Val::Sig(us) => Ok(us),
      ty => Err(err(ty)),
    }
  }
}

impl<'a> Term<'a> {
  /// Given universe `u`, returns the universe of its type.
  pub fn univ_univ(u: usize) -> Result<usize, TypeError<'static>> {
    match u {
      #[cfg(feature = "type_in_type")]
      0 => Ok(0),
      #[cfg(not(feature = "type_in_type"))]
      0 => Ok(1),
      _ => Err(TypeError::univ_form(u)),
    }
  }

  /// Given universes `v` and `w`, returns the universe of Pi types from `v` to `w`.
  pub fn pi_univ(v: usize, w: usize) -> Result<usize, TypeError<'static>> {
    Ok(max(v, w))
  }

  /// Given universes `v` and `w`, returns the universe of Sigma types containing `v` and `w`.
  pub fn sig_univ(v: usize, w: usize) -> Result<usize, TypeError<'static>> {
    Ok(max(v, w))
  }

  /// Returns the universe of the unit type.
  pub fn unit_univ() -> Result<usize, TypeError<'static>> {
    Ok(0)
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
  pub fn infer(&self, ctx: &Stack<'a>, env: &Stack<'a>, ar: &'a Arena) -> Result<Val<'a>, TypeError<'a>> {
    match self {
      // The (univ) rule is used.
      Term::Univ(v) => Ok(Val::Univ(Term::univ_univ(*v)?)),
      // The (var) rule is used.
      // Variables of values are in de Bruijn levels, so weakening is no-op.
      Term::Var(ix) => ctx.get(*ix, ar).ok_or_else(|| TypeError::ctx_index(*ix, ctx.len())),
      // The (ann) rule is used.
      // To establish pre-conditions for `eval()` and `check()`, the type of `t` is checked first.
      Term::Ann(x, t, boundary) => {
        let tt = t.infer(ctx, env, ar)?;
        let _ = tt.as_univ(|tt| TypeError::type_expected(t, tt, ctx, env, ar))?;
        let t = t.eval(env, ar)?;
        match boundary {
          false => x.check(t, ctx, env, ar)?,
          true => x.check(t, ctx, env, &Arena::new()).map_err(|e| e.relocate(ar))?,
        };
        Ok(t)
      }
      // The (let) and (extend) rules are used.
      // The (ζ) rule is implicitly used on the value (in normal form) from the recursive call.
      Term::Let(v, x) => {
        let vt = v.infer(ctx, env, ar)?;
        let v = v.eval(env, ar)?;
        let xt = x.infer(&ctx.extend(vt, ar), &env.extend(v, ar), ar)?;
        Ok(xt)
      }
      // The (Π form) and (extend) rules are used.
      Term::Pi(t, u) => {
        let tt = t.infer(ctx, env, ar)?;
        let v = tt.as_univ(|tt| TypeError::type_expected(t, tt, ctx, env, ar))?;
        let t = t.eval(env, ar)?;
        let x = Val::Free(env.len());
        let ut = u.infer(&ctx.extend(t, ar), &env.extend(x, ar), ar)?;
        let w = ut.as_univ(|ut| TypeError::type_expected(u, ut, ctx, env, ar))?;
        Ok(Val::Univ(Term::pi_univ(v, w)?))
      }
      // Function abstractions must be enclosed in type annotations, or appear as an argument.
      Term::Fun(_) => Err(TypeError::ann_expected(ar.term(*self))),
      // The (Π elim) rule is used.
      Term::App(f, x) => {
        let ft = f.infer(ctx, env, ar)?;
        let (t, u) = ft.as_pi(|ft| TypeError::pi_expected(f, ft, ctx, env, ar))?;
        x.check(*t, ctx, env, ar)?;
        Ok(u.apply(x.eval(env, ar)?, ar)?)
      }
      // The (Σ form), (⊤ form) and (extend) rules are used.
      Term::Sig(us) => {
        let mut v = Term::unit_univ()?;
        let cs = ar.closures(us.len()).as_mut_ptr();
        for (i, u) in us.iter().enumerate() {
          // SAFETY: the borrowed range `&cs[..i]` is no longer modified.
          let t = Val::Sig(unsafe { from_raw_parts(cs, i) });
          let x = Val::Free(env.len());
          let ut = u.infer(&ctx.extend(t, ar), &env.extend(x, ar), ar)?;
          let w = ut.as_univ(|ut| TypeError::type_expected(u, ut, ctx, env, ar))?;
          v = Term::sig_univ(v, w)?;
          // SAFETY: `i < us.len()` which is the valid size of `cs`.
          unsafe { *cs.add(i) = Clos { env: *env, body: u } };
        }
        Ok(Val::Univ(v))
      }
      // Tuple constructors must be enclosed in type annotations, or appear as an argument.
      Term::Tup(_) => Err(TypeError::ann_expected(ar.term(*self))),
      // The (Σ init) rule is used.
      Term::Init(n, x) => {
        let xt = x.infer(ctx, env, ar)?;
        let us = xt.as_sig(|xt| TypeError::sig_expected(x, xt, ctx, env, ar))?;
        let m = us.len().checked_sub(*n).ok_or_else(|| TypeError::sig_init(*n, us.len()))?;
        Ok(Val::Sig(&us[..m]))
      }
      // The (Σ proj) rule is used.
      Term::Proj(n, x) => {
        let xt = x.infer(ctx, env, ar)?;
        let us = xt.as_sig(|xt| TypeError::sig_expected(x, xt, ctx, env, ar))?;
        let i = us.len().checked_sub(n + 1).ok_or_else(|| TypeError::sig_proj(*n, us.len()))?;
        Ok(us[i].apply(Term::Init(n + 1, x).eval(env, ar)?, ar)?)
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
  pub fn check(&self, t: Val<'a>, ctx: &Stack<'a>, env: &Stack<'a>, ar: &'a Arena) -> Result<(), TypeError<'a>> {
    match self {
      // The (let) and (extend) rules are used.
      // The (ζ) rule is implicitly inversely used on the `t` passed into the recursive call.
      Term::Let(v, x) => {
        let vt = v.infer(ctx, env, ar)?;
        let v = v.eval(env, ar)?;
        x.check(t, &ctx.extend(vt, ar), &env.extend(v, ar), ar)?;
        Ok(())
      }
      // The (Π intro) and (extend) rules is used.
      // By pre-conditions, `t` is already known to have universe type.
      Term::Fun(b) => {
        let x = Val::Free(env.len());
        let (t, u) = t.as_pi(|t| TypeError::pi_ann_expected(t, ctx, env, ar))?;
        b.check(u.apply(x, ar)?, &ctx.extend(*t, ar), &env.extend(x, ar), ar)?;
        Ok(())
      }
      // The (∑ intro) and (extend) rules are used.
      // By pre-conditions, `t` is already known to have universe type.
      Term::Tup(bs) => {
        let us = t.as_sig(|t| TypeError::sig_ann_expected(t, ctx, env, ar))?;
        if bs.len() == us.len() {
          let vs = ar.values(bs.len()).as_mut_ptr();
          for (i, b) in bs.iter().enumerate() {
            let u = &us[i];
            let t = Val::Sig(&us[..i]);
            // SAFETY: the borrowed range `&vs[..i]` is no longer modified.
            let a = Val::Tup(unsafe { from_raw_parts(vs, i) });
            b.check(u.apply(a, ar)?, &ctx.extend(t, ar), &env.extend(a, ar), ar)?;
            // SAFETY: `i < bs.len()` which is the valid size of `vs`.
            unsafe { *vs.add(i) = b.eval(&env.extend(a, ar), ar)? };
          }
          Ok(())
        } else {
          Err(TypeError::tup_size_mismatch(ar.term(*self), bs.len(), us.len()))
        }
      }
      // The (conv) rule is used.
      // By pre-conditions, `t` is already known to have universe type.
      x => {
        let xt = x.infer(ctx, env, ar)?;
        let res = Val::conv(&xt, &t, env.len(), ar)?.then_some(());
        res.ok_or_else(|| TypeError::type_mismatch(ar.term(*x), xt, t, ctx, env, ar))
      }
    }
  }
}
