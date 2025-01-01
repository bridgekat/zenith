use std::cmp::max;
use std::slice::from_raw_parts;

use super::*;
use crate::arena::Arena;
use crate::ir;

#[derive(Debug, Clone, Copy)]
pub enum Var<'a> {
  Ix(usize),
  Name(&'a str, usize, usize),
}

pub type Bound<'a> = ir::Bound<'a>;
pub type Field<'a> = ir::Field<'a>;

#[derive(Debug, Clone, Copy)]
pub enum Term<'a> {
  /// Universe in levels.
  Univ(usize),
  /// Variables in names.
  Var(Var<'a>),
  /// Type annotations (value, type, arena boundary flag).
  Ann(&'a Term<'a>, &'a Term<'a>, bool),
  /// Let expressions (binder info, value, *body*).
  Let(Bound<'a>, &'a Term<'a>, &'a Term<'a>),
  /// Function types (binder info, parameter type, *return type*).
  Pi(Bound<'a>, &'a Term<'a>, &'a Term<'a>),
  /// Function abstractions (binder info, *body*).
  Fun(Bound<'a>, &'a Term<'a>),
  /// Function applications (function, argument, dot-syntax flag).
  App(&'a Term<'a>, &'a Term<'a>, bool),
  /// Tuple types (field info, initial types, *last type*).
  Sig(Field<'a>, &'a Term<'a>, &'a Term<'a>),
  /// Tuple constructors (field info, initial values, *last value*).
  Tup(Field<'a>, &'a Term<'a>, &'a Term<'a>),
  /// Tuple initial segments (truncation, tuple).
  Init(usize, &'a Term<'a>),
  /// Tuple last element (tuple).
  Last(&'a Term<'a>),
  /// Empty tuple types.
  Unit,
  /// Empty tuple constructors.
  Star,
  /// Holes in unique identifiers.
  Meta(usize),
}

impl Var<'_> {
  /// Clones `self` to given arena.
  pub fn relocate<'b>(&self, ar: &'b Arena) -> Var<'b> {
    match self {
      Var::Ix(ix) => Var::Ix(*ix),
      Var::Name(name, len, ix) => Var::Name(ar.string(name), *len, *ix),
    }
  }
}

impl Term<'_> {
  /// Clones `self` to given arena.
  pub fn relocate<'b>(&self, ar: &'b Arena) -> &'b Term<'b> {
    match self {
      Term::Univ(v) => ar.named(Term::Univ(*v)),
      Term::Var(var) => ar.named(Term::Var(var.relocate(ar))),
      Term::Ann(x, t, b) => ar.named(Term::Ann(x.relocate(ar), t.relocate(ar), *b)),
      Term::Let(i, v, x) => ar.named(Term::Let(i.relocate(ar), v.relocate(ar), x.relocate(ar))),
      Term::Pi(i, t, u) => ar.named(Term::Pi(i.relocate(ar), t.relocate(ar), u.relocate(ar))),
      Term::Fun(i, b) => ar.named(Term::Fun(i.relocate(ar), b.relocate(ar))),
      Term::App(f, x, b) => ar.named(Term::App(f.relocate(ar), x.relocate(ar), *b)),
      Term::Sig(i, t, u) => ar.named(Term::Sig(i.relocate(ar), t.relocate(ar), u.relocate(ar))),
      Term::Tup(i, a, b) => ar.named(Term::Tup(i.relocate(ar), a.relocate(ar), b.relocate(ar))),
      Term::Init(n, x) => ar.named(Term::Init(*n, x.relocate(ar))),
      Term::Last(x) => ar.named(Term::Last(x.relocate(ar))),
      Term::Unit => ar.named(Term::Unit),
      Term::Star => ar.named(Term::Star),
      Term::Meta(m) => ar.named(Term::Meta(*m)),
    }
  }
}

impl Var<'_> {
  /// Resolves a variable to a core term and its type.
  pub fn resolve<'a, 'b>(
    &self,
    ctx: &ir::Stack<'a, 'b>,
    ar: &'b Arena,
  ) -> Result<(&'b ir::Term<'b>, ir::Val<'a, 'b>), TypeError<'b>> {
    match self {
      Var::Ix(ix) => {
        let t = ctx.get(*ix, ar).ok_or_else(|| TypeError::ctx_index(*ix, ctx.len()))?;
        Ok((ar.term(ir::Term::Var(*ix)), t))
      }
      Var::Name(name, _, _) => {
        todo!()
      }
    }
  }
}

impl<'a, 'b> ir::Val<'a, 'b> {
  /// Reduces well-typed `self` to eliminate `let`s and convert it back into a [`Term`].
  /// Can be an expensive operation.
  ///
  /// Pre-conditions:
  ///
  /// - `self` is well-typed under a context with size `len` (to ensure termination).
  pub fn quote(&self, len: usize, ar: &'b Arena) -> Result<&'b Term<'b>, ir::EvalError<'b>> {
    let bound = Bound { name: "_", attrs: &[] }; // TODO: implement binder info
    let field = Field { name: "_", attrs: &[] }; // TODO: implement field info
    match self {
      ir::Val::Univ(v) => Ok(ar.named(Term::Univ(*v))),
      ir::Val::Gen(i) => todo!(), // Ok(ar.named(Term::Var(len.checked_sub(i + 1).ok_or_else(|| EvalError::gen_level(*i, len))?))),
      ir::Val::Pi(t, u) => {
        Ok(ar.named(Term::Pi(bound, t.quote(len, ar)?, u.apply(ir::Val::Gen(len), ar)?.quote(len + 1, ar)?)))
      }
      ir::Val::Fun(b) => Ok(ar.named(Term::Fun(bound, b.apply(ir::Val::Gen(len), ar)?.quote(len + 1, ar)?))),
      ir::Val::App(f, x) => Ok(ar.named(Term::App(f.quote(len, ar)?, x.quote(len, ar)?, false))),
      ir::Val::Sig(us) => {
        let mut init = ar.named(Term::Unit);
        for u in us.iter() {
          init = ar.named(Term::Sig(field, init, u.apply(ir::Val::Gen(len), ar)?.quote(len + 1, ar)?));
        }
        Ok(init)
      }
      ir::Val::Tup(bs) => {
        let mut init = ar.named(Term::Star);
        for b in bs.iter() {
          init = ar.named(Term::Tup(field, init, b.quote(len + 1, ar)?));
        }
        Ok(init)
      }
      ir::Val::Init(n, x) => Ok(ar.named(Term::Init(*n, x.quote(len, ar)?))),
      ir::Val::Last(x) => Ok(ar.named(Term::Last(x.quote(len, ar)?))),
      ir::Val::Meta(_, m) => {
        // TODO
        // let mut res = ar.named(Term::Meta(*m));
        // let mut env = *env;
        // let mut len = len + env.len();
        // while let ir::Stack::Cons { prev, value } = env {
        //   len -= 1;
        //   res = ar.named(Term::Let(binder, value.quote(len, ar)?, res));
        //   env = *prev;
        // }
        // Ok(res)
        Ok(ar.named(Term::Meta(*m)))
      }
    }
  }

  /// Given `self`, eliminates as [`Val::Univ`].
  pub fn as_univ(self, term: &'b Term<'b>, len: usize, ar: &'b Arena) -> Result<usize, TypeError<'b>> {
    match self {
      ir::Val::Univ(v) => Ok(v),
      ty => Err(TypeError::type_expected(term, ty, len, ar)),
    }
  }

  /// Given `self`, eliminates as [`Val::Pi`].
  pub fn as_pi(
    self,
    term: Option<&'b Term<'b>>,
    len: usize,
    ar: &'b Arena,
  ) -> Result<(&'a ir::Val<'a, 'b>, &'a ir::Clos<'a, 'b>), TypeError<'b>> {
    match self {
      ir::Val::Pi(t, u) => Ok((t, u)),
      ty => match term {
        Some(term) => Err(TypeError::pi_expected(term, ty, len, ar)),
        None => Err(TypeError::pi_ann_expected(ty, len, ar)),
      },
    }
  }

  /// Given `self`, eliminates as [`Val::Sig`].
  pub fn as_sig(
    self,
    term: Option<&'b Term<'b>>,
    len: usize,
    ar: &'b Arena,
  ) -> Result<&'a [ir::Clos<'a, 'b>], TypeError<'b>> {
    match self {
      ir::Val::Sig(us) => Ok(us),
      ty => match term {
        Some(term) => Err(TypeError::sig_expected(term, ty, len, ar)),
        None => Err(TypeError::sig_ann_expected(ty, len, ar)),
      },
    }
  }
}

impl<'b> Term<'b> {
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
  pub fn infer<'a>(
    &self,
    ctx: &ir::Stack<'a, 'b>,
    env: &ir::Stack<'a, 'b>,
    ar: &'b Arena,
  ) -> Result<(&'b ir::Term<'b>, ir::Val<'a, 'b>), TypeError<'b>> {
    match self {
      // The (univ) rule is used.
      Term::Univ(v) => Ok((ar.term(ir::Term::Univ(*v)), ir::Val::Univ(Term::univ_univ(*v)?))),
      // The (var) rule is used.
      // Variables of values are in de Bruijn levels, so weakening is no-op.
      Term::Var(var) => var.resolve(ctx, ar),
      // The (ann) rule is used.
      // To establish pre-conditions for `eval()` and `check()`, the type of `t` is checked first.
      Term::Ann(x_named, t_named, arena_boundary) => {
        let (t, tt) = t_named.infer(ctx, env, ar)?;
        let _ = tt.as_univ(t_named, ctx.len(), ar)?;
        let tv = t.eval(env, ar)?;
        let x = match arena_boundary {
          false => x_named.check(tv, ctx, env, ar)?,
          true => x_named.check(tv, ctx, env, &Arena::new()).map(|x| x.relocate(ar)).map_err(|e| e.relocate(ar))?,
        };
        Ok((ar.term(ir::Term::Ann(x, t, *arena_boundary)), tv))
      }
      // The (let) and (extend) rules are used.
      // The (ζ) rule is implicitly used on the value (in normal form) from the recursive call.
      Term::Let(_, v_named, x_named) => {
        let (v, vt) = v_named.infer(ctx, env, ar)?;
        let v = v.eval(env, ar)?;
        x_named.infer(&ctx.extend(vt, ar), &env.extend(v, ar), ar)
      }
      // The (Π form) and (extend) rules are used.
      Term::Pi(i, t_named, u_named) => {
        let (t, tt) = t_named.infer(ctx, env, ar)?;
        let v = tt.as_univ(t_named, ctx.len(), ar)?;
        let (u, ut) = u_named.infer(&ctx.extend(t.eval(env, ar)?, ar), &env.extend(ir::Val::Gen(env.len()), ar), ar)?;
        let w = ut.as_univ(u_named, ctx.len() + 1, ar)?;
        Ok((ar.term(ir::Term::Pi(*i, t, u)), ir::Val::Univ(Term::pi_univ(v, w)?)))
      }
      // Function abstractions must be enclosed in type annotations, or appear as an argument.
      Term::Fun(_, _) => todo!(),
      // The (Π elim) rule is used.
      Term::App(f_named, x_named, b) => {
        let (f, ft) = f_named.infer(ctx, env, ar)?;
        let (t, u) = ft.as_pi(Some(f_named), ctx.len(), ar)?;
        let x = x_named.check(*t, ctx, env, ar)?;
        Ok((ar.term(ir::Term::App(f, x, *b)), u.apply(x.eval(env, ar)?, ar)?))
      }
      // The (Σ form), (⊤ form) and (extend) rules are used.
      Term::Unit | Term::Sig(_, _, _) => {
        let mut init = self;
        let mut is = Vec::new();
        let mut us = Vec::new();
        while let Term::Sig(i, t_named, u_named) = init {
          init = t_named;
          is.push(*i);
          us.push(u_named);
        }
        if let Term::Unit = init {
          is.reverse();
          us.reverse();
          let mut init = ar.term(ir::Term::Unit);
          let mut t = Vec::new();
          let mut v = Term::unit_univ()?;
          for (i, u_named) in is.into_iter().zip(us.into_iter()) {
            let (u, ut) =
              u_named.infer(&ctx.extend(ir::Val::Sig(&t), ar), &env.extend(ir::Val::Gen(env.len()), ar), ar)?;
            let w = ut.as_univ(u_named, ctx.len() + 1, ar)?;
            t.push(ir::Clos { env: *env, body: u });
            init = ar.term(ir::Term::Sig(i, init, u));
            v = Term::sig_univ(v, w)?;
          }
          Ok((init, ir::Val::Univ(v)))
        } else {
          Err(TypeError::sig_improper(ar.named(*self)))
        }
      }
      // Tuple constructors must be enclosed in type annotations, or appear as an argument.
      Term::Star | Term::Tup(_, _, _) => todo!(),
      // The (Σ init) rule is used.
      Term::Init(n, x_named) => {
        let (x, xt) = x_named.infer(ctx, env, ar)?;
        let us = xt.as_sig(Some(x_named), ctx.len(), ar)?;
        let m = us.len().checked_sub(*n).ok_or_else(|| TypeError::sig_init(*n, us.len()))?;
        Ok((ar.term(ir::Term::Init(*n, x)), ir::Val::Sig(&us[..m])))
      }
      // The (Σ last) rule is used.
      Term::Last(x_named) => {
        let (x, xt) = x_named.infer(ctx, env, ar)?;
        let us = xt.as_sig(Some(x_named), ctx.len(), ar)?;
        let i = us.len().checked_sub(1).ok_or_else(|| TypeError::sig_last(1, us.len()))?;
        Ok((ar.term(ir::Term::Last(x)), us[i].apply(ir::Term::Init(1, x).eval(env, ar)?, ar)?))
      }
      // TODO
      Term::Meta(_) => todo!(),
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
  pub fn check<'a>(
    &self,
    t: ir::Val<'a, 'b>,
    ctx: &ir::Stack<'a, 'b>,
    env: &ir::Stack<'a, 'b>,
    ar: &'b Arena,
  ) -> Result<&'b ir::Term<'b>, TypeError<'b>> {
    match self {
      // The (let) and (extend) rules are used.
      // The (ζ) rule is implicitly inversely used on the `t` passed into the recursive call.
      Term::Let(_, v_named, x_named) => {
        let (v, vt) = v_named.infer(ctx, env, ar)?;
        let v = v.eval(env, ar)?;
        x_named.check(t, &ctx.extend(vt, ar), &env.extend(v, ar), ar)
      }
      // The (Π intro) and (extend) rules is used.
      // By pre-conditions, `t` is already known to have universe type.
      Term::Fun(_, b_named) => {
        let x = ir::Val::Gen(env.len());
        let (t, u) = t.as_pi(None, ctx.len(), ar)?;
        b_named.check(u.apply(x, ar)?, &ctx.extend(*t, ar), &env.extend(x, ar), ar)
      }
      // The (∑ intro) and (extend) rules are used.
      // By pre-conditions, `t` is already known to have universe type.
      Term::Star | Term::Tup(_, _, _) => {
        let us = t.as_sig(None, ctx.len(), ar)?;
        let mut init = self;
        let mut is = Vec::new();
        let mut bs = Vec::new();
        while let Term::Tup(i, a_named, b_named) = init {
          init = a_named;
          is.push(*i);
          bs.push(b_named);
        }
        if let Term::Star = init {
          is.reverse();
          bs.reverse();
          let mut init = ar.term(ir::Term::Star);
          if bs.len() == us.len() {
            // Eagerly evaluate tuple elements.
            let vs = ar.values(bs.len(), ir::Val::Gen(0));
            for (i, (b_named, u)) in bs.iter().zip(us.iter()).enumerate() {
              // SAFETY: the borrowed range `&vs[..i]` is no longer modified.
              let a = ir::Val::Tup(unsafe { from_raw_parts(vs.as_ptr(), i) });
              let t = ir::Val::Sig(&us[..i]);
              let b = b_named.check(u.apply(a, ar)?, &ctx.extend(t, ar), &env.extend(a, ar), ar)?;
              vs[i] = b.eval(&env.extend(a, ar), ar)?;
              init = ar.term(ir::Term::Tup(is[i], init, b));
            }
            Ok(init)
          } else {
            Err(TypeError::tup_size_mismatch(ar.named(*self), bs.len(), us.len()))
          }
        } else {
          Err(TypeError::tup_improper(ar.named(*self)))
        }
      }
      // The (conv) rule is used.
      // By pre-conditions, `t` is already known to have universe type.
      x_named => {
        let (x, xt) = x_named.infer(ctx, env, ar)?;
        let res = ir::Val::conv(&xt, &t, env.len(), ar)?.then_some(x);
        res.ok_or_else(|| TypeError::type_mismatch(ar.named(*x_named), xt, t, ctx.len(), ar))
      }
    }
  }
}
