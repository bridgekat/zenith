use std::cmp::max;

use super::*;

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
      Term::Univ(u) => Ok(Val::Univ(*u)),
      // The (δ) rule is always applied.
      Term::Var(ix) => env.get(*ix, ar).ok_or_else(|| EvalError::env_index(*ix, env.len())),
      // The (τ) rule is always applied.
      Term::Ann(x, _) => x.eval(env, ar),
      // For `let`s, we reduce the value, collect it into the environment to reduce the body.
      Term::Let(v, x) => x.eval(&env.extend(v.eval(env, ar)?, ar), ar),
      // For binders, we freeze the whole environment and store the body as a closure.
      Term::Pi(s, t) => Ok(Val::Pi(ar.val(s.eval(env, ar)?), Clos { env: env.clone(), body: t })),
      Term::Fun(b) => Ok(Val::Fun(Clos { env: env.clone(), body: b })),
      // For applications, we reduce both operands and combine them back.
      // In the case of a redex, the (β) rule is applied.
      Term::App(f, x) => match (f.eval(env, ar)?, x.eval(env, ar)?) {
        (Val::Fun(b), x) => b.apply(x, ar),
        (f, x) => Ok(Val::App(ar.val(f), ar.val(x))),
      },
      // For binders, we freeze the whole environment and store the body as a closure.
      Term::Sig(s, t) => Ok(Val::Sig(ar.val(s.eval(env, ar)?), Clos { env: env.clone(), body: t })),
      Term::Pair(a, b) => Ok(Val::Pair(ar.val(a.eval(env, ar)?), Clos { env: env.clone(), body: b })),
      // For projections, we reduce the operand and combine it back.
      // In the case of a redex, the (π fst) and (π snd) rules are applied.
      Term::Fst(x) => match x.eval(env, ar)? {
        Val::Pair(a, _) => Ok(a.clone()),
        x => Ok(Val::Fst(ar.val(x))),
      },
      Term::Snd(x) => match x.eval(env, ar)? {
        Val::Pair(a, b) => b.apply(a.clone(), ar),
        x => Ok(Val::Snd(ar.val(x))),
      },
      // The unit type and its inhabitant are already in normal form.
      Term::Unit => Ok(Val::Unit),
      Term::Star => Ok(Val::Star),
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
  /// Returns if `self` and `other` are definitionally equal. Can be an expensive operation if
  /// they are indeed definitionally equal.
  ///
  /// Pre-conditions:
  ///
  /// - `self` and `other` are well-typed under a context with size `len` (to ensure termination).
  pub fn conv(&self, other: &Self, len: usize, ar: &'a Arena) -> Result<bool, EvalError> {
    match (self, other) {
      (Val::Univ(u), Val::Univ(v)) => Ok(u == v),
      (Val::Gen(i), Val::Gen(j)) => Ok(i == j),
      (Val::Pi(s, u), Val::Pi(t, v)) => {
        // Go under a binder, reducing the body without assigning a value to the argument.
        Ok(s.conv(t, len, ar)? && u.apply(Val::Gen(len), ar)?.conv(&v.apply(Val::Gen(len), ar)?, len + 1, ar)?)
      }
      (Val::Fun(b), Val::Fun(c)) => {
        // Go under a binder, reducing the body without assigning a value to the argument.
        Ok(b.apply(Val::Gen(len), ar)?.conv(&c.apply(Val::Gen(len), ar)?, len + 1, ar)?)
      }
      (Val::App(f, x), Val::App(g, y)) => Ok(f.conv(g, len, ar)? && x.conv(y, len, ar)?),
      (Val::Sig(s, u), Val::Sig(t, v)) => {
        // Go under a binder, reducing the body without assigning a value to the argument.
        Ok(s.conv(t, len, ar)? && u.apply(Val::Gen(len), ar)?.conv(&v.apply(Val::Gen(len), ar)?, len + 1, ar)?)
      }
      (Val::Pair(a, c), Val::Pair(b, d)) => {
        // Go under a binder, reducing the body without assigning a value to the argument.
        Ok(a.conv(b, len, ar)? && c.apply(Val::Gen(len), ar)?.conv(&d.apply(Val::Gen(len), ar)?, len + 1, ar)?)
      }
      (Val::Fst(x), Val::Fst(y)) => Ok(x.conv(y, len, ar)?),
      (Val::Snd(x), Val::Snd(y)) => Ok(x.conv(y, len, ar)?),
      (Val::Unit, Val::Unit) => Ok(true),
      (Val::Star, Val::Star) => Ok(true),
      _ => Ok(false),
    }
  }

  /// Reduces well-typed `self` to eliminate `let`s and convert it back into a [`Term`].
  /// Can be an expensive operation.
  ///
  /// Pre-conditions:
  ///
  /// - `self` is well-typed under a context with size `len` (to ensure termination).
  pub fn quote(&self, len: usize, ar: &'a Arena) -> Result<Term<'a>, EvalError> {
    match self {
      Val::Univ(u) => Ok(Term::Univ(*u)),
      Val::Gen(lvl) => match *lvl < len {
        // For generic (i.e. unassigned) variables, convert de Bruijn levels to de Bruijn indices.
        true => Ok(Term::Var(len - 1 - lvl)),
        false => Err(EvalError::gen_level(*lvl, len)),
      },
      Val::Pi(s, t) => {
        // Go under a binder, reducing the body without assigning a value to the argument.
        Ok(Term::Pi(ar.term(s.quote(len, ar)?), ar.term(t.apply(Val::Gen(len), ar)?.quote(len + 1, ar)?)))
      }
      Val::Fun(b) => {
        // Go under a binder, reducing the body without assigning a value to the argument.
        Ok(Term::Fun(ar.term(b.apply(Val::Gen(len), ar)?.quote(len + 1, ar)?)))
      }
      Val::App(f, x) => Ok(Term::App(ar.term(f.quote(len, ar)?), ar.term(x.quote(len, ar)?))),
      Val::Sig(s, t) => {
        // Go under a binder, reducing the body without assigning a value to the argument.
        Ok(Term::Sig(ar.term(s.quote(len, ar)?), ar.term(t.apply(Val::Gen(len), ar)?.quote(len + 1, ar)?)))
      }
      Val::Pair(a, b) => {
        // Go under a binder, reducing the body without assigning a value to the argument.
        Ok(Term::Pair(ar.term(a.quote(len, ar)?), ar.term(b.apply(Val::Gen(len), ar)?.quote(len + 1, ar)?)))
      }
      Val::Fst(x) => Ok(Term::Fst(ar.term(x.quote(len, ar)?))),
      Val::Snd(x) => Ok(Term::Snd(ar.term(x.quote(len, ar)?))),
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
  pub fn as_pi<'b>(&'b self) -> Option<(&'b Val<'a>, &'b Clos<'a>)> {
    match self {
      Val::Pi(s, t) => Some((s, t)),
      _ => None,
    }
  }

  /// Given well-typed `self`, tries elimination as [`Val::Sig`].
  pub fn as_sig<'b>(&'b self) -> Option<(&'b Val<'a>, &'b Clos<'a>)> {
    match self {
      Val::Sig(s, t) => Some((s, t)),
      _ => None,
    }
  }
}

impl Univ {
  /// Universe formation rule.
  pub fn univ_rule(u: Self) -> Option<Self> {
    match u {
      #[cfg(feature = "type_in_type")]
      Self(0) => Some(Self(0)),
      #[cfg(not(feature = "type_in_type"))]
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
  pub fn infer(&'a self, ctx: &Stack<'a>, env: &Stack<'a>, ar: &'a Arena) -> Result<Val<'a>, TypeError<'a>> {
    match self {
      // The (univ) rule is used.
      Term::Univ(u) => Ok(Val::Univ(Univ::univ_rule(*u).ok_or_else(|| TypeError::univ_form(*u))?)),
      // The (var) rule is used.
      // Variables in `ctx` are in de Bruijn levels, so weakening is no-op.
      Term::Var(ix) => ctx.get(*ix, ar).ok_or_else(|| TypeError::ctx_index(*ix, ctx.len())),
      // The (ann) rule is used.
      // To establish pre-conditions for `check()`, the type of `t` is checked first.
      Term::Ann(x, t) => {
        let tt = t.infer(ctx, env, ar)?;
        let _ = tt.as_univ().ok_or_else(|| TypeError::type_expected(t, tt, ctx.len(), ar))?;
        let t = t.eval(env, ar)?;
        x.check(t.clone(), ctx, env, ar)?;
        Ok(t)
      }
      // The (let) and (extend) rules are used.
      // The (ζ) rule is implicitly used on the value (in normal form) from the recursive call.
      Term::Let(v, x) => {
        let vt = v.infer(ctx, env, ar)?;
        let v = v.eval(env, ar)?;
        x.infer(&ctx.extend(vt, ar), &env.extend(v, ar), ar)
      }
      // The (Π form) and (extend) rules are used.
      Term::Pi(s, t) => {
        let st = s.infer(ctx, env, ar)?;
        let u = st.as_univ().ok_or_else(|| TypeError::type_expected(s, st, ctx.len(), ar))?;
        let tt = t.infer(&ctx.extend(s.eval(env, ar)?, ar), &env.extend(Val::Gen(env.len()), ar), ar)?;
        let v = tt.as_univ().ok_or_else(|| TypeError::type_expected(t, tt, ctx.len(), ar))?;
        Ok(Val::Univ(Univ::pi_rule(u, v).ok_or_else(|| TypeError::pi_form(u, v))?))
      }
      // Function abstractions must be enclosed in type annotations, or appear as an argument.
      Term::Fun(_) => Err(TypeError::ann_expected(self)),
      // The (Π elim) rule is used.
      Term::App(f, x) => {
        let ft = f.infer(ctx, env, ar)?;
        let (s, t) = ft.as_pi().ok_or_else(|| TypeError::pi_expected(f, ft.clone(), ctx.len(), ar))?;
        x.check(s.clone(), ctx, env, ar)?;
        Ok(t.apply(x.eval(env, ar)?, ar)?)
      }
      // The (Σ form) and (extend) rules are used.
      Term::Sig(s, t) => {
        let st = s.infer(ctx, env, ar)?;
        let u = st.as_univ().ok_or_else(|| TypeError::type_expected(s, st, ctx.len(), ar))?;
        let tt = t.infer(&ctx.extend(s.eval(env, ar)?, ar), &env.extend(Val::Gen(env.len()), ar), ar)?;
        let v = tt.as_univ().ok_or_else(|| TypeError::type_expected(t, tt, ctx.len(), ar))?;
        Ok(Val::Univ(Univ::sig_rule(u, v).ok_or_else(|| TypeError::sig_form(u, v))?))
      }
      // Pair constructors must be enclosed in type annotations, or appear as an argument.
      Term::Pair(_, _) => Err(TypeError::ann_expected(self)),
      // The (Σ fst) rule is used.
      Term::Fst(x) => {
        let xt = x.infer(ctx, env, ar)?;
        let (s, _) = xt.as_sig().ok_or_else(|| TypeError::sig_expected(x, xt.clone(), ctx.len(), ar))?;
        Ok(s.clone())
      }
      // The (Σ snd) rule is used.
      Term::Snd(x) => {
        let xt = x.infer(ctx, env, ar)?;
        let (_, t) = xt.as_sig().ok_or_else(|| TypeError::sig_expected(x, xt.clone(), ctx.len(), ar))?;
        Ok(t.apply(Term::Fst(x).eval(env, ar)?, ar)?)
      }
      // The (⊤ form) rule is used.
      Term::Unit => Ok(Val::Univ(Univ::unit_rule())),
      // The (⊤ intro) rule is used.
      Term::Star => Ok(Val::Unit),
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
  pub fn check(&'a self, t: Val<'a>, ctx: &Stack<'a>, env: &Stack<'a>, ar: &'a Arena) -> Result<(), TypeError<'a>> {
    match self {
      // The (let) and (extend) rules are used.
      // The (ζ) rule is implicitly inversely used on the `t` passed into the recursive call.
      Term::Let(v, x) => {
        let vt = v.infer(ctx, env, ar)?;
        let v = v.eval(env, ar)?;
        x.check(t, &ctx.extend(vt, ar), &env.extend(v, ar), ar)
      }
      // The (Π intro) and (extend) rules is used.
      // By pre-conditions, `t` is already known to have universe type.
      Term::Fun(b) => match t {
        Val::Pi(s, t) => {
          let g = Val::Gen(env.len());
          b.check(t.apply(g.clone(), ar)?, &ctx.extend(s.clone(), ar), &env.extend(g, ar), ar)
        }
        t => Err(TypeError::pi_ann_expected(t, ctx.len(), ar)),
      },
      // The (∑ intro) and (extend) rules are used.
      // By pre-conditions, `t` is already known to have universe type.
      Term::Pair(a, b) => match t {
        Val::Sig(s, t) => {
          a.check(s.clone(), ctx, env, ar)?;
          let a = a.eval(env, ar)?;
          b.check(t.apply(a.clone(), ar)?, &ctx.extend(s.clone(), ar), &env.extend(a, ar), ar)
        }
        t => Err(TypeError::sig_ann_expected(t, ctx.len(), ar)),
      },
      // The (conv) rule is used.
      // By pre-conditions, `t` is already known to have universe type.
      x => {
        let xt = x.infer(ctx, env, ar)?;
        let res = xt.conv(&t, env.len(), ar)?.then_some(());
        res.ok_or_else(|| TypeError::type_mismatch(x, xt, t, ctx.len(), ar))
      }
    }
  }
}
