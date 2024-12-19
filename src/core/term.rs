//! # The core type checker
//!
//! This is an implementation of Coquand's type checking algorithm.
//!
//! - See: <https://www.sciencedirect.com/science/article/pii/0167642395000216>
//! - See: <https://github.com/AndrasKovacs/elaboration-zoo/blob/master/02-typecheck-closures-debruijn/Main.hs>

use std::cmp::max;
use typed_arena::Arena;

use super::*;

/// Universe levels.
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct Univ(pub usize);

/// Terms of the core calculus.
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub enum Term<'a> {
  /// Universes.
  Univ(Univ),
  /// Variables in de Bruijn indices.
  Var(usize),
  /// Type annotations (value, type).
  Ann(&'a Term<'a>, &'a Term<'a>),
  /// Let expressions (value, *body*).
  Let(&'a Term<'a>, &'a Term<'a>),
  /// Function types (parameter type, *return type*).
  Pi(&'a Term<'a>, &'a Term<'a>),
  /// Function abstractions (*body*).
  Fun(&'a Term<'a>),
  /// Function applications (function, argument).
  App(&'a Term<'a>, &'a Term<'a>),
  /// Pair types (first type, *second type*).
  Sig(&'a Term<'a>, &'a Term<'a>),
  /// Pair let-constructors (first value, *second value*).
  Pair(&'a Term<'a>, &'a Term<'a>),
  /// Pair projections (pair).
  Fst(&'a Term<'a>),
  /// Pair projections (pair).
  Snd(&'a Term<'a>),
  /// Unit types.
  Unit,
  /// Unit inhabitants.
  Star,
}

/// Closures: terms annotated with frozen `let`s capturing the whole environment.
#[derive(Debug, Clone)]
pub struct Clos<'a>(pub Env<'a>, pub &'a Term<'a>);

/// Values: terms where `let`s are already collected and frozen at binders.
#[derive(Debug, Clone)]
pub enum Val<'a> {
  /// Universes.
  Univ(Univ),
  /// Generic variables in de Bruijn *levels* for cheap weakening.
  Gen(usize),
  /// Function types (parameter type, *return type*).
  Pi(&'a Val<'a>, Clos<'a>),
  /// Function abstractions (*body*).
  Fun(Clos<'a>),
  /// Function applications (function, argument).
  App(&'a Val<'a>, &'a Val<'a>),
  /// Pair types (first type, *second type*).
  Sig(&'a Val<'a>, Clos<'a>),
  /// Pair let-constructors (first value, *second value*).
  Pair(&'a Val<'a>, Clos<'a>),
  /// Pair projections (pair).
  Fst(&'a Val<'a>),
  /// Pair projections (pair).
  Snd(&'a Val<'a>),
  /// Unit types.
  Unit,
  /// Unit inhabitants.
  Star,
}

/// Typing contexts: lists of types.
pub type Ctx<'a> = Stack<'a>;

/// Evaluation environments: lists of definitions.
pub type Env<'a> = Stack<'a>;

impl<'a> Term<'a> {
  /// Reduces well-typed `self` so that all `let`s are collected into the environment and then
  /// frozen at binders.
  pub fn eval(self, env: &Env<'a>, vals: &'a Arena<Val<'a>>) -> Result<Val<'a>, EvalError> {
    match self {
      // Universes are already in normal form.
      Term::Univ(u) => Ok(Val::Univ(u)),
      // The (δ) rule is always applied.
      Term::Var(ix) => env.get(ix).ok_or(EvalError::EnvIndex { ix, len: env.len() }),
      // The (τ) rule is always applied.
      Term::Ann(x, _) => x.eval(env, vals),
      // For `let`s, we reduce the value, collect it into the environment to reduce the body.
      Term::Let(v, x) => x.eval(&env.extend(v.eval(env, vals)?), vals),
      // For binders, we freeze the whole environment and store the body as a closure.
      Term::Pi(s, t) => Ok(Val::Pi(vals.alloc(s.eval(env, vals)?), Clos(env.clone(), t))),
      Term::Fun(b) => Ok(Val::Fun(Clos(env.clone(), b))),
      // For applications, we reduce both operands and combine them back.
      // In the case of a redex, the (β) rule is applied.
      Term::App(f, x) => match (f.eval(env, vals)?, x.eval(env, vals)?) {
        (Val::Fun(b), x) => Ok(b.apply(x, vals)?),
        (f, x) => Ok(Val::App(vals.alloc(f), vals.alloc(x))),
      },
      // For binders, we freeze the whole environment and store the body as a closure.
      Term::Sig(s, t) => Ok(Val::Sig(vals.alloc(s.eval(env, vals)?), Clos(env.clone(), t))),
      Term::Pair(a, b) => Ok(Val::Pair(vals.alloc(a.eval(env, vals)?), Clos(env.clone(), b))),
      // For projections, we reduce the operand and combine it back.
      // In the case of a redex, the (π) rules are applied.
      Term::Fst(x) => match x.eval(env, vals)? {
        Val::Pair(a, _) => Ok(a.clone()),
        x => Ok(Val::Fst(vals.alloc(x))),
      },
      Term::Snd(x) => match x.eval(env, vals)? {
        Val::Pair(a, b) => Ok(b.apply(a.clone(), vals)?),
        x => Ok(Val::Snd(vals.alloc(x))),
      },
      // The unit type and its inhabitant are already in normal form.
      Term::Unit => Ok(Val::Unit),
      Term::Star => Ok(Val::Star),
    }
  }
}

impl<'a> Clos<'a> {
  /// Inserts a new `let` around the body after the frozen `let`s, and reduces the body under the
  /// empty environment populated with all `let`s.
  pub fn apply(self, x: Val<'a>, vals: &'a Arena<Val<'a>>) -> Result<Val<'a>, EvalError> {
    let Self(env, body) = self;
    body.eval(&env.extend(x), vals)
  }
}

impl<'a> Val<'a> {
  /// Given well-typed `self` and `other`, returns if they are definitionally equal.
  pub fn conv(&self, other: &Self, lvl: usize, vals: &'a Arena<Val<'a>>) -> Result<bool, EvalError> {
    let mut lhs = self.clone();
    let mut rhs = other.clone();
    let mut lvl = lvl;
    loop {
      match (lhs, rhs) {
        (Val::Univ(u), Val::Univ(v)) if u == v => return Ok(true),
        (Val::Gen(i), Val::Gen(j)) if i == j => return Ok(true),
        (Val::Pi(s, u), Val::Pi(t, v)) if s.conv(t, lvl, vals)? => {
          (lhs, rhs, lvl) = (u.apply(Val::Gen(lvl), vals)?, v.apply(Val::Gen(lvl), vals)?, lvl + 1)
        }
        (Val::Fun(b), Val::Fun(c)) => {
          (lhs, rhs, lvl) = (b.apply(Val::Gen(lvl), vals)?, c.apply(Val::Gen(lvl), vals)?, lvl + 1)
        }
        (Val::App(f, x), Val::App(g, y)) if f.conv(g, lvl, vals)? => (lhs, rhs, lvl) = (x.clone(), y.clone(), lvl),
        (Val::Sig(s, u), Val::Sig(t, v)) if s.conv(t, lvl, vals)? => {
          (lhs, rhs, lvl) = (u.apply(Val::Gen(lvl), vals)?, v.apply(Val::Gen(lvl), vals)?, lvl + 1)
        }
        (Val::Pair(a, c), Val::Pair(b, d)) if a.conv(b, lvl, vals)? => {
          (lhs, rhs, lvl) = (c.apply(Val::Gen(lvl), vals)?, d.apply(Val::Gen(lvl), vals)?, lvl + 1)
        }
        (Val::Fst(x), Val::Fst(y)) => (lhs, rhs, lvl) = (x.clone(), y.clone(), lvl),
        (Val::Snd(x), Val::Snd(y)) => (lhs, rhs, lvl) = (x.clone(), y.clone(), lvl),
        (Val::Unit, Val::Unit) => return Ok(true),
        (Val::Star, Val::Star) => return Ok(true),
        _ => return Ok(false),
      };
    }
  }

  /// Reduces well-typed `self` to eliminate `let`s and convert it back into a [`Term`].
  /// Can be an expensive operation.
  pub fn quote(&self, lvl: usize, terms: &'a Arena<Term<'a>>, vals: &'a Arena<Val<'a>>) -> Result<Term<'a>, EvalError> {
    match self {
      Val::Univ(u) => Ok(Term::Univ(*u)),
      Val::Gen(x) => Ok(Term::Var(lvl - 1 - x)),
      Val::Pi(s, t) => Ok(Term::Pi(
        terms.alloc(s.quote(lvl, terms, vals)?),
        terms.alloc(t.clone().apply(Val::Gen(lvl), vals)?.quote(lvl + 1, terms, vals)?),
      )),
      Val::Fun(b) => Ok(Term::Fun(terms.alloc(b.clone().apply(Val::Gen(lvl), vals)?.quote(lvl + 1, terms, vals)?))),
      Val::App(f, x) => Ok(Term::App(terms.alloc(f.quote(lvl, terms, vals)?), terms.alloc(x.quote(lvl, terms, vals)?))),
      Val::Sig(s, t) => Ok(Term::Sig(
        terms.alloc(s.quote(lvl, terms, vals)?),
        terms.alloc(t.clone().apply(Val::Gen(lvl), vals)?.quote(lvl + 1, terms, vals)?),
      )),
      Val::Pair(a, b) => Ok(Term::Pair(
        terms.alloc(a.quote(lvl, terms, vals)?),
        terms.alloc(b.clone().apply(Val::Gen(lvl), vals)?.quote(lvl + 1, terms, vals)?),
      )),
      Val::Fst(x) => Ok(Term::Fst(terms.alloc(x.quote(lvl, terms, vals)?))),
      Val::Snd(x) => Ok(Term::Snd(terms.alloc(x.quote(lvl, terms, vals)?))),
      Val::Unit => Ok(Term::Unit),
      Val::Star => Ok(Term::Star),
    }
  }

  /// Given well-typed `self`, tries elimination as [`Val::Univ`].
  pub fn as_univ(&self) -> Option<Univ> {
    match self {
      Val::Univ(u) => Some(*u),
      _ => None,
    }
  }

  /// Given well-typed `self`, tries elimination as [`Val::Pi`].
  pub fn as_pi(&self) -> Option<(&'a Val<'a>, Clos<'a>)> {
    match self {
      Val::Pi(s, t) => Some((*s, t.clone())),
      _ => None,
    }
  }

  /// Given well-typed `self`, tries elimination as [`Val::Sig`].
  pub fn as_sig(&self) -> Option<(&'a Val<'a>, Clos<'a>)> {
    match self {
      Val::Sig(s, t) => Some((*s, t.clone())),
      _ => None,
    }
  }
}

impl Univ {
  /// Universe formation rule.
  pub fn univ_rule(u: Self) -> Option<Self> {
    match u {
      Self(0) => Some(Self(1)),
      _ => None,
    }
  }

  /// Function type formation rule.
  pub fn pi_rule(u: Self, v: Self) -> Option<Self> {
    let (Self(u), Self(v)) = (u, v);
    Some(Self(max(u, v)))
  }

  /// Pair type formation rule.
  pub fn sig_rule(u: Self, v: Self) -> Option<Self> {
    let (Self(u), Self(v)) = (u, v);
    Some(Self(max(u, v)))
  }

  /// Unit type formation rule.
  pub fn unit_rule() -> Self {
    Self(0)
  }
}

impl<'a> Term<'a> {
  /// Given preterm `self`, returns the type of `self`.
  pub fn infer(&'a self, ctx: &Ctx<'a>, env: &Env<'a>, vals: &'a Arena<Val<'a>>) -> Result<Val<'a>, TypeError<'a>> {
    match self {
      Term::Univ(u) => Ok(Val::Univ(Univ::univ_rule(*u).ok_or(TypeError::UnivForm { univ: *u })?)),
      Term::Var(ix) => ctx.get(*ix).ok_or(TypeError::CtxIndex { ix: *ix, len: ctx.len() }),
      Term::Ann(x, t) => {
        let tt = t.infer(ctx, env, vals)?;
        let _ = tt.as_univ().ok_or(TypeError::TypeExpected { term: t, ty: tt })?;
        let t = t.eval(env, vals)?;
        x.check(t.clone(), ctx, env, vals)?;
        Ok(t)
      }
      Term::Let(v, x) => {
        let vt = v.infer(ctx, env, vals)?;
        let v = v.eval(env, vals)?;
        x.infer(&ctx.extend(vt), &env.extend(v), vals)
      }
      Term::Pi(s, t) => {
        let st = s.infer(ctx, env, vals)?;
        let u = st.as_univ().ok_or(TypeError::TypeExpected { term: s, ty: st })?;
        let tt = t.infer(&ctx.extend(s.eval(env, vals)?), &env.extend(Val::Gen(env.len())), vals)?;
        let v = tt.as_univ().ok_or(TypeError::TypeExpected { term: t, ty: tt })?;
        Ok(Val::Univ(Univ::pi_rule(u, v).ok_or(TypeError::PiForm { from: u, to: v })?))
      }
      Term::Fun(_) => Err(TypeError::AnnExpected { term: self }),
      Term::App(f, x) => {
        let ft = f.infer(ctx, env, vals)?;
        let (s, t) = ft.as_pi().ok_or(TypeError::PiExpected { term: f, ty: ft })?;
        x.check(s.clone(), ctx, env, vals)?;
        Ok(t.apply(x.eval(env, vals)?, vals)?)
      }
      Term::Sig(s, t) => {
        let st = s.infer(ctx, env, vals)?;
        let u = st.as_univ().ok_or(TypeError::TypeExpected { term: s, ty: st })?;
        let tt = t.infer(&ctx.extend(s.eval(env, vals)?), &env.extend(Val::Gen(env.len())), vals)?;
        let v = tt.as_univ().ok_or(TypeError::TypeExpected { term: t, ty: tt })?;
        Ok(Val::Univ(Univ::sig_rule(u, v).ok_or(TypeError::SigForm { fst: u, snd: v })?))
      }
      Term::Pair(_, _) => Err(TypeError::AnnExpected { term: self }),
      Term::Fst(x) => {
        let xt = x.infer(ctx, env, vals)?;
        let (s, _) = xt.as_sig().ok_or(TypeError::SigExpected { term: x, ty: xt })?;
        Ok(s.clone())
      }
      Term::Snd(x) => {
        let xt = x.infer(ctx, env, vals)?;
        let (_, t) = xt.as_sig().ok_or(TypeError::SigExpected { term: x, ty: xt })?;
        Ok(t.apply(Term::Fst(x).eval(env, vals)?, vals)?)
      }
      Term::Unit => Ok(Val::Univ(Univ::unit_rule())),
      Term::Star => Ok(Val::Unit),
    }
  }

  /// Given preterms `self`, `t`, checks if `self` has type `t`.
  pub fn check(
    &'a self,
    t: Val<'a>,
    ctx: &Ctx<'a>,
    env: &Env<'a>,
    vals: &'a Arena<Val<'a>>,
  ) -> Result<(), TypeError<'a>> {
    match self {
      Term::Let(v, x) => x.check(t, &ctx.extend(v.infer(ctx, env, vals)?), &env.extend(v.eval(env, vals)?), vals),
      Term::Fun(b) => match t {
        Val::Pi(s, t) => {
          let c = Val::Gen(env.len());
          b.check(t.apply(c.clone(), vals)?, &ctx.extend(s.clone()), &env.extend(c), vals)
        }
        t => Err(TypeError::PiAnnExpected { ty: t }),
      },
      Term::Pair(a, b) => match t {
        Val::Sig(s, t) => {
          a.check(s.clone(), ctx, env, vals)?;
          let a = a.eval(env, vals)?;
          b.check(t.apply(a.clone(), vals)?, &ctx.extend(s.clone()), &env.extend(a), vals)
        }
        t => Err(TypeError::SigAnnExpected { ty: t }),
      },
      x => {
        let xt = x.infer(ctx, env, vals)?;
        xt.conv(&t, env.len(), vals)?.then_some(()).ok_or(TypeError::TypeMismatch { term: x, ty: xt, expect: t })
      }
    }
  }
}
