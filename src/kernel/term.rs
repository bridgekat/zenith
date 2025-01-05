use std::cell::RefCell;
use std::cmp::max;
use std::rc::Rc;

use super::*;

/// # Terms
///
/// Terms of the core calculus.
///
/// Can be understood as the "source code" given to the evaluator.
#[derive(Debug, Clone)]
pub enum Term {
  /// Universe in levels.
  Univ(usize),
  /// Variables in de Bruijn indices.
  Var(usize),
  /// Type annotations (value, type, arena boundary flag).
  Ann(Rc<Term>, Rc<Term>, bool),
  /// Let expressions (value, *body*).
  Let(Rc<Term>, Rc<Term>),
  /// Function types (parameter type, *return type*).
  Pi(Rc<Term>, Rc<Term>),
  /// Function abstractions (*body*).
  Fun(Rc<Term>),
  /// Function applications (function, argument).
  App(Rc<Term>, Rc<Term>),
  /// Tuple types (*element types*).
  Sig(Rc<[Term]>),
  /// Tuple constructors (*element values*).
  Tup(Rc<[Term]>),
  /// Tuple initial segments (truncation, tuple).
  Init(usize, Rc<Term>),
  /// Tuple projections (index, tuple).
  Proj(usize, Rc<Term>),
}

/// # Values
///
/// Values are terms whose outermost `let`s are already collected and frozen at binders.
///
/// Can be understood as "runtime objects" produced by the evaluator.
#[derive(Debug, Clone)]
pub enum Val {
  /// Universe in levels.
  Univ(usize),
  /// Free variables in de Bruijn *levels* for cheap weakening.
  Free(usize),
  /// Function types (parameter type, *return type*).
  Pi(Rc<Val>, Clos),
  /// Function abstractions (*body*).
  Fun(Clos),
  /// Function applications (function, argument).
  App(Rc<Val>, Rc<Val>),
  /// Tuple types (size, *element types*).
  Sig(usize, Rc<[Clos]>),
  /// Tuple constructors (size, element values).
  Tup(usize, Rc<[RefCell<Val>]>),
  /// Tuple initial segments (truncation, tuple).
  Init(usize, Rc<Val>),
  /// Tuple projections (index, tuple).
  Proj(usize, Rc<Val>),
}

/// # Closures
///
/// Closures are terms annotated with frozen `let`s capturing the whole environment.
///
/// The environment is represented using a special data structure which supports structural sharing
/// and fast random access (in most cases). For more details, see the documentation for [`Stack`].
#[derive(Debug, Clone)]
pub struct Clos {
  pub env: Rc<Stack>,
  pub body: Rc<Term>,
}

/// # Linked list stacks
///
/// The baseline implementation of evaluation environments. Cheap to append and clone, but random
/// access takes linear time. This is acceptable if most of the context is wrapped inside tuples,
/// which have constant-time random access.
#[derive(Debug, Clone)]
pub enum Stack {
  Nil,
  Cons { prev: Rc<Stack>, value: Val },
}

impl Stack {
  /// Creates an empty stack.
  pub fn new() -> Rc<Self> {
    Rc::new(Stack::Nil)
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
  pub fn get(&self, index: usize) -> Option<Val> {
    let mut curr = self;
    let mut index = index;
    while let Stack::Cons { prev, value } = curr {
      if index == 0 {
        return Some(value.clone());
      }
      index -= 1;
      curr = prev;
    }
    None
  }

  /// Extends the stack with a new value.
  pub fn extend(self: Rc<Self>, value: Val) -> Rc<Self> {
    Rc::new(Stack::Cons { prev: self.clone(), value })
  }
}

impl Term {
  /// Reduces `self` so that all `let`s are collected into the environment and then frozen at
  /// binders. This is mutually recursive with [`Clos::apply`], forming an eval-apply loop.
  ///
  /// Pre-conditions:
  ///
  /// - `self` is well-typed under a context and environment `env` (to ensure termination).
  pub fn eval(&self, env: Rc<Stack>) -> Result<Val, EvalError> {
    match self {
      // Universes are already in normal form.
      Term::Univ(v) => Ok(Val::Univ(*v)),
      // The (δ) rule is always applied.
      // Variables of values are in de Bruijn levels, so weakening is no-op.
      Term::Var(ix) => env.get(*ix).ok_or_else(|| EvalError::env_index(*ix, env.len())),
      // The (τ) rule is always applied.
      Term::Ann(x, _, _) => x.eval(env),
      // For `let`s, we reduce the value, collect it into the environment to reduce the body.
      Term::Let(v, x) => x.eval(env.clone().extend(v.eval(env)?)),
      // For binders, we freeze the whole environment and store the body as a closure.
      Term::Pi(t, u) => Ok(Val::Pi(Rc::new(t.eval(env.clone())?), Clos { env, body: u.clone() })),
      Term::Fun(b) => Ok(Val::Fun(Clos { env, body: b.clone() })),
      // For applications, we reduce both operands and combine them back.
      // In the case of a redex, the (β) rule is applied.
      Term::App(f, x) => match (f.eval(env.clone())?, x.eval(env)?) {
        (Val::Fun(Clos { env, body }), x) => body.eval(env.extend(x)),
        (f, x) => Ok(Val::App(Rc::new(f), Rc::new(x))),
      },
      // For binders, we freeze the whole environment and store the body as a closure.
      Term::Sig(us) => {
        let cs = Rc::from_iter(us.iter().map(|u| Clos { env: env.clone(), body: Rc::new(u.clone()) }));
        Ok(Val::Sig(cs.len(), cs))
      }
      Term::Tup(bs) => {
        let vs = Rc::from_iter(std::iter::repeat_with(|| RefCell::new(Val::Univ(0))).take(bs.len()));
        for (i, b) in bs.iter().enumerate() {
          let a = Val::Tup(i, vs.clone());
          let b = b.eval(env.clone().extend(a))?;
          *vs[i].borrow_mut() = b;
        }
        Ok(Val::Tup(vs.len(), vs))
      }
      // For initials (i.e. iterated first projections), we reduce the operand and combine it back.
      // In the case of a redex, the (π init) rule is applied.
      Term::Init(n, x) => match x.eval(env)? {
        Val::Init(m, y) => Ok(Val::Init(n + m, y)),
        Val::Tup(m, bs) => {
          let m = m.checked_sub(*n).ok_or_else(|| EvalError::tup_init(*n, m))?;
          Ok(Val::Tup(m, bs))
        }
        x => Ok(Val::Init(*n, Rc::new(x))),
      },
      // For projections (i.e. second projections after iterated first projections), we reduce the
      // operand and combine it back.
      // In the case of a redex, the (π last) rule is applied.
      Term::Proj(n, x) => match x.eval(env)? {
        Val::Init(m, y) => Ok(Val::Proj(n + m, y)),
        Val::Tup(m, bs) => {
          let i = m.checked_sub(n + 1).ok_or_else(|| EvalError::tup_proj(*n, m))?;
          Ok(bs[i].borrow().clone())
        }
        x => Ok(Val::Proj(*n, Rc::new(x))),
      },
    }
  }
}

impl Clos {
  /// Inserts a new `let` around the body after the frozen `let`s, and reduces the body under the
  /// empty environment populated with all `let`s. This is mutually recursive with [`Term::eval`],
  /// forming an eval-apply loop.
  pub fn apply(&self, x: Val) -> Result<Val, EvalError> {
    let Self { env, body } = self;
    body.eval(env.clone().extend(x))
  }
}

impl Val {
  /// Reduces well-typed `self` to eliminate `let`s and convert it back into a [`Term`].
  /// Can be an expensive operation. Expected to be used for outputs and error reporting.
  ///
  /// Pre-conditions:
  ///
  /// - `self` is well-typed under a context with size `len` (to ensure termination).
  pub fn quote(&self, len: usize) -> Result<Term, EvalError> {
    match self {
      Val::Univ(v) => Ok(Term::Univ(*v)),
      Val::Free(i) => Ok(Term::Var(len.checked_sub(i + 1).ok_or_else(|| EvalError::gen_level(*i, len))?)),
      Val::Pi(t, u) => Ok(Term::Pi(Rc::new(t.quote(len)?), Rc::new(u.apply(Val::Free(len))?.quote(len + 1)?))),
      Val::Fun(b) => Ok(Term::Fun(Rc::new(b.apply(Val::Free(len))?.quote(len + 1)?))),
      Val::App(f, x) => Ok(Term::App(Rc::new(f.quote(len)?), Rc::new(x.quote(len)?))),
      Val::Sig(n, us) => {
        let mut terms = Vec::new();
        for u in us.iter().take(*n) {
          terms.push(u.apply(Val::Free(len))?.quote(len + 1)?);
        }
        Ok(Term::Sig(Rc::from(terms)))
      }
      Val::Tup(n, bs) => {
        let mut terms = Vec::new();
        for b in bs.iter().take(*n) {
          terms.push(b.borrow().quote(len + 1)?);
        }
        Ok(Term::Tup(Rc::from(terms)))
      }
      Val::Init(n, x) => Ok(Term::Init(*n, Rc::new(x.quote(len)?))),
      Val::Proj(n, x) => Ok(Term::Proj(*n, Rc::new(x.quote(len)?))),
    }
  }

  /// Returns if `self` and `other` are definitionally equal. Can be an expensive operation if
  /// they are indeed definitionally equal.
  ///
  /// Pre-conditions:
  ///
  /// - `self` and `other` are well-typed under a context with size `len` (to ensure termination).
  pub fn conv(&self, other: &Self, len: usize) -> Result<bool, EvalError> {
    match (self, other) {
      (Val::Univ(v), Val::Univ(w)) => Ok(v == w),
      (Val::Free(i), Val::Free(j)) => Ok(i == j),
      (Val::Pi(t, v), Val::Pi(u, w)) => {
        Ok(Val::conv(t, u, len)? && Val::conv(&v.apply(Val::Free(len))?, &w.apply(Val::Free(len))?, len + 1)?)
      }
      (Val::Fun(b), Val::Fun(c)) => Ok(Val::conv(&b.apply(Val::Free(len))?, &c.apply(Val::Free(len))?, len + 1)?),
      (Val::App(f, x), Val::App(g, y)) => Ok(Val::conv(f, g, len)? && Val::conv(x, y, len)?),
      (Val::Sig(n, us), Val::Sig(m, vs)) if n == m => {
        for (u, v) in us.iter().zip(vs.iter()).take(*n) {
          if !Val::conv(&u.apply(Val::Free(len))?, &v.apply(Val::Free(len))?, len + 1)? {
            return Ok(false);
          }
        }
        Ok(true)
      }
      (Val::Tup(n, bs), Val::Tup(m, cs)) if n == m => {
        for (b, c) in bs.iter().zip(cs.iter()).take(*n) {
          let (b, c) = (b.borrow(), c.borrow());
          if !Val::conv(&b, &c, len)? {
            return Ok(false);
          }
        }
        Ok(true)
      }
      (Val::Init(n, x), Val::Init(m, y)) => Ok(n == m && Val::conv(x, y, len)?),
      (Val::Proj(n, x), Val::Proj(m, y)) => Ok(n == m && Val::conv(x, y, len)?),
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
  pub fn as_pi<E>(self, err: impl FnOnce(Self) -> E) -> Result<(Rc<Val>, Clos), E> {
    match self {
      Val::Pi(t, u) => Ok((t, u)),
      ty => Err(err(ty)),
    }
  }

  /// Given `self`, tries elimination as [`Val::Sig`].
  pub fn as_sig<E>(self, err: impl FnOnce(Self) -> E) -> Result<(usize, Rc<[Clos]>), E> {
    match self {
      Val::Sig(n, us) => Ok((n, us)),
      ty => Err(err(ty)),
    }
  }
}

impl Term {
  /// Given universe `u`, returns the universe of its type.
  pub fn univ_univ(u: usize) -> Result<usize, TypeError> {
    match u {
      #[cfg(feature = "type_in_type")]
      0 => Ok(0),
      #[cfg(not(feature = "type_in_type"))]
      0 => Ok(1),
      _ => Err(TypeError::univ_form(u)),
    }
  }

  /// Given universes `v` and `w`, returns the universe of Pi types from `v` to `w`.
  pub fn pi_univ(v: usize, w: usize) -> Result<usize, TypeError> {
    Ok(max(v, w))
  }

  /// Given universes `v` and `w`, returns the universe of Sigma types containing `v` and `w`.
  pub fn sig_univ(v: usize, w: usize) -> Result<usize, TypeError> {
    Ok(max(v, w))
  }

  /// Returns the universe of the unit type.
  pub fn unit_univ() -> Result<usize, TypeError> {
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
  pub fn infer(&self, ctx: Rc<Stack>, env: Rc<Stack>) -> Result<Val, TypeError> {
    match self {
      // The (univ) rule is used.
      Term::Univ(v) => Ok(Val::Univ(Term::univ_univ(*v)?)),
      // The (var) rule is used.
      // Variables of values are in de Bruijn levels, so weakening is no-op.
      Term::Var(ix) => ctx.get(*ix).ok_or_else(|| TypeError::ctx_index(*ix, ctx.len())),
      // The (ann) rule is used.
      // To establish pre-conditions for `eval()` and `check()`, the type of `t` is checked first.
      Term::Ann(x, t, _) => {
        let tt = t.infer(ctx.clone(), env.clone())?;
        let _ = tt.as_univ(|tt| TypeError::type_expected(t.clone(), tt, &ctx, &env))?;
        let t = t.eval(env.clone())?;
        x.check(t.clone(), ctx, env)?;
        Ok(t)
      }
      // The (let) and (extend) rules are used.
      // The (ζ) rule is implicitly used on the value (in normal form) from the recursive call.
      Term::Let(v, x) => {
        let vt = v.infer(ctx.clone(), env.clone())?;
        let v = v.eval(env.clone())?;
        let xt = x.infer(ctx.extend(vt), env.extend(v))?;
        Ok(xt)
      }
      // The (Π form) and (extend) rules are used.
      Term::Pi(t, u) => {
        let tt = t.infer(ctx.clone(), env.clone())?;
        let v = tt.as_univ(|tt| TypeError::type_expected(t.clone(), tt, &ctx, &env))?;
        let t = t.eval(env.clone())?;
        let x = Val::Free(env.len());
        let ut = u.infer(ctx.clone().extend(t), env.clone().extend(x))?;
        let w = ut.as_univ(|ut| TypeError::type_expected(u.clone(), ut, &ctx, &env))?;
        Ok(Val::Univ(Term::pi_univ(v, w)?))
      }
      // Function abstractions must be enclosed in type annotations, or appear as an argument.
      Term::Fun(_) => Err(TypeError::ann_expected(Rc::new(self.clone()))),
      // The (Π elim) rule is used.
      Term::App(f, x) => {
        let ft = f.infer(ctx.clone(), env.clone())?;
        let (t, u) = ft.as_pi(|ft| TypeError::pi_expected(f.clone(), ft, &ctx, &env))?;
        x.check(Rc::unwrap_or_clone(t), ctx.clone(), env.clone())?;
        Ok(u.apply(x.eval(env)?)?)
      }
      // The (Σ form), (⊤ form) and (extend) rules are used.
      Term::Sig(us) => {
        let mut v = Term::unit_univ()?;
        let cs = Rc::from_iter(us.iter().map(|u| Clos { env: env.clone(), body: Rc::new(u.clone()) }));
        for (i, u) in us.iter().enumerate() {
          let t = Val::Sig(i, cs.clone());
          let x = Val::Free(env.len());
          let ut = u.infer(ctx.clone().extend(t), env.clone().extend(x))?;
          let w = ut.as_univ(|ut| TypeError::type_expected(Rc::new(u.clone()), ut, &ctx, &env))?;
          v = Term::sig_univ(v, w)?;
        }
        Ok(Val::Univ(v))
      }
      // Tuple constructors must be enclosed in type annotations, or appear as an argument.
      Term::Tup(_) => Err(TypeError::ann_expected(Rc::new(self.clone()))),
      // The (Σ init) rule is used.
      Term::Init(n, x) => {
        let xt = x.infer(ctx.clone(), env.clone())?;
        let (m, us) = xt.as_sig(|xt| TypeError::sig_expected(x.clone(), xt, &ctx, &env))?;
        let m = m.checked_sub(*n).ok_or_else(|| TypeError::sig_init(*n, m))?;
        Ok(Val::Sig(m, us))
      }
      // The (Σ proj) rule is used.
      Term::Proj(n, x) => {
        let xt = x.infer(ctx.clone(), env.clone())?;
        let (m, us) = xt.as_sig(|xt| TypeError::sig_expected(x.clone(), xt, &ctx, &env))?;
        let i = m.checked_sub(n + 1).ok_or_else(|| TypeError::sig_proj(*n, m))?;
        let u = &us[i];
        Ok(u.apply(Term::Init(n + 1, x.clone()).eval(env)?)?)
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
  pub fn check(&self, t: Val, ctx: Rc<Stack>, env: Rc<Stack>) -> Result<(), TypeError> {
    match self {
      // The (let) and (extend) rules are used.
      // The (ζ) rule is implicitly inversely used on the `t` passed into the recursive call.
      Term::Let(v, x) => {
        let vt = v.infer(ctx.clone(), env.clone())?;
        let v = v.eval(env.clone())?;
        x.check(t, ctx.extend(vt), env.extend(v))?;
        Ok(())
      }
      // The (Π intro) and (extend) rules is used.
      // By pre-conditions, `t` is already known to have universe type.
      Term::Fun(b) => {
        let x = Val::Free(env.len());
        let (t, u) = t.as_pi(|t| TypeError::pi_ann_expected(t, &ctx, &env))?;
        b.check(u.apply(x.clone())?, ctx.extend(Rc::unwrap_or_clone(t)), env.extend(x))?;
        Ok(())
      }
      // The (∑ intro) and (extend) rules are used.
      // By pre-conditions, `t` is already known to have universe type.
      Term::Tup(bs) => {
        let (m, us) = t.as_sig(|t| TypeError::sig_ann_expected(t, &ctx, &env))?;
        if bs.len() == m {
          let vs = Rc::from_iter(std::iter::repeat_with(|| RefCell::new(Val::Univ(0))).take(bs.len()));
          for (i, b) in bs.iter().enumerate() {
            let t = Val::Sig(i, us.clone());
            let a = Val::Tup(i, vs.clone());
            let u = &us[i];
            b.check(u.apply(a.clone())?, ctx.clone().extend(t), env.clone().extend(a.clone()))?;
            *vs[i].borrow_mut() = b.eval(env.clone().extend(a))?;
          }
          Ok(())
        } else {
          Err(TypeError::tup_size_mismatch(Rc::new(self.clone()), bs.len(), us.len()))
        }
      }
      // The (conv) rule is used.
      // By pre-conditions, `t` is already known to have universe type.
      x => {
        let xt = x.infer(ctx.clone(), env.clone())?;
        let res = Val::conv(&xt, &t, env.len())?.then_some(());
        res.ok_or_else(|| TypeError::type_mismatch(Rc::new(x.clone()), xt, t, &ctx, &env))
      }
    }
  }
}
