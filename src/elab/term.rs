use std::cmp::max;
use std::slice::from_raw_parts;

use super::*;
use crate::arena::Arena;
use crate::ir;

#[derive(Debug, Clone, Copy)]
pub struct Name<'a> {
  pub segments: &'a [&'a str],
}

pub type Bound<'a> = ir::Bound<'a>;
pub type Field<'a> = ir::Field<'a>;

#[derive(Debug, Clone, Copy)]
pub enum Term<'a> {
  /// Universe in levels.
  Univ(usize),
  /// Variables in de Bruijn indices.
  Var(usize),
  /// Type annotations (value, type, arena boundary flag).
  Ann(&'a Term<'a>, &'a Term<'a>, bool),
  /// Let expressions (binder info, value, *body*).
  Let(&'a Bound<'a>, &'a Term<'a>, &'a Term<'a>),
  /// Function types (binder info, parameter type, *return type*).
  Pi(&'a Bound<'a>, &'a Term<'a>, &'a Term<'a>),
  /// Function abstractions (binder info, *body*).
  Fun(&'a Bound<'a>, &'a Term<'a>),
  /// Function applications (function, argument, dot-syntax flag).
  App(&'a Term<'a>, &'a Term<'a>, bool),
  /// Tuple types (field info, initial types, *last type*).
  Sig(&'a Field<'a>, &'a Term<'a>, &'a Term<'a>),
  /// Tuple constructors (field info, initial values, *last value*).
  Tup(&'a Field<'a>, &'a Term<'a>, &'a Term<'a>),
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
  /// Unresolved names.
  Name(Name<'a>),
}

impl<'a> Name<'a> {
  /// Creates a new name in the given arena.
  pub fn new(raw: &str, ar: &'a Arena) -> Self {
    Self { segments: ar.strings(&raw.split("::").filter(|s| !s.is_empty()).collect::<Vec<_>>()) }
  }

  /// Clones `self` to given arena.
  pub fn relocate<'b>(&self, ar: &'b Arena) -> Name<'b> {
    Name { segments: ar.strings(self.segments) }
  }
}

impl Term<'_> {
  /// Clones `self` to given arena.
  pub fn relocate<'b>(&self, ar: &'b Arena) -> &'b Term<'b> {
    match self {
      Term::Univ(v) => ar.named(Term::Univ(*v)),
      Term::Var(ix) => ar.named(Term::Var(*ix)),
      Term::Ann(x, t, b) => ar.named(Term::Ann(x.relocate(ar), t.relocate(ar), *b)),
      Term::Let(i, v, x) => ar.named(Term::Let(i.relocate(ar), v.relocate(ar), x.relocate(ar))),
      Term::Pi(i, t, u) => ar.named(Term::Pi(i.relocate(ar), t.relocate(ar), u.relocate(ar))),
      Term::Fun(i, b) => ar.named(Term::Fun(i.relocate(ar), b.relocate(ar))),
      Term::App(g, x, b) => ar.named(Term::App(g.relocate(ar), x.relocate(ar), *b)),
      Term::Sig(i, t, u) => ar.named(Term::Sig(i.relocate(ar), t.relocate(ar), u.relocate(ar))),
      Term::Tup(i, a, b) => ar.named(Term::Tup(i.relocate(ar), a.relocate(ar), b.relocate(ar))),
      Term::Init(n, x) => ar.named(Term::Init(*n, x.relocate(ar))),
      Term::Last(x) => ar.named(Term::Last(x.relocate(ar))),
      Term::Unit => ar.named(Term::Unit),
      Term::Star => ar.named(Term::Star),
      Term::Meta(m) => ar.named(Term::Meta(*m)),
      Term::Name(name) => ar.named(Term::Name(name.relocate(ar))),
    }
  }
}

impl<'b> Name<'b> {
  /// Splits the first segment from the rest.
  pub fn split_first(&self) -> Option<(&'b str, Name<'b>)> {
    self.segments.split_first().map(|(first, rest)| (*first, Name { segments: rest }))
  }

  /// Resolves a name suffix given a core term and its type.
  fn resolve_rest<'a>(
    &self,
    env: &ir::Stack<'a, 'b>,
    ar: &'b Arena,
    x: &'b ir::Term<'b>,
    ty: ir::Val<'a, 'b>,
  ) -> Result<(&'b ir::Term<'b>, ir::Val<'a, 'b>), TypeError<'b>> {
    match self.split_first() {
      None => Ok((x, ty)),
      Some((first, rest)) => {
        if let ir::Val::Sig(us) = ty {
          for (ix, (i, u)) in us.iter().rev().enumerate() {
            if i.name == first {
              let ty = u.apply(ir::Term::Init(ix + 1, x).eval(env, ar)?, ar)?;
              return rest.resolve_rest(env, ar, ar.term(ir::Term::Last(ar.term(ir::Term::Init(ix, x)))), ty);
            }
          }
        }
        Err(TypeError::ctx_name(*self))
      }
    }
  }

  /// Resolves a named variable to a core term and its type.
  pub fn resolve<'a>(
    &self,
    ctx: &ir::Stack<'a, 'b>,
    env: &ir::Stack<'a, 'b>,
    ar: &'b Arena,
  ) -> Result<(&'b ir::Term<'b>, ir::Val<'a, 'b>), TypeError<'b>> {
    match self.split_first() {
      None => Err(TypeError::ctx_name(*self)),
      Some((first, rest)) => {
        let mut curr = ctx;
        let mut ix = 0;
        // Resolve the first segment in the context.
        ar.inc_lookup_count();
        while let ir::Stack::Cons { prev, info, value: ty } = curr {
          ar.inc_link_count();
          if info.name == first {
            // Resolve the rest of the name in the type.
            return rest.resolve_rest(env, ar, ar.term(ir::Term::Var(ix)), *ty);
          }
          if info.name.is_empty() {
            if let ir::Val::Sig(us) = ty {
              if us.iter().any(|(i, _)| i.name == first) {
                // Resolve the whole name in the type.
                return self.resolve_rest(env, ar, ar.term(ir::Term::Var(ix)), *ty);
              }
            }
          }
          ix += 1;
          curr = prev;
        }
        Err(TypeError::ctx_name(*self))
      }
    }
  }

  // /// Presents a projection as a named variable.
  // pub fn present<'a>(ix: usize, proj: &[usize], ctx: &ir::Stack<'a, 'b>, ar: &'b Arena) -> Option<&'b Term<'b>> {
  //   todo!()
  // }
}

impl<'a, 'b> ir::Val<'a, 'b> {
  /// Reduces well-typed `self` to eliminate `let`s and convert it back into a [`Term`].
  /// Can be an expensive operation. Expected to be used for outputs and error reporting.
  ///
  /// Pre-conditions:
  ///
  /// - `self` is well-typed under a context with size `len` (to ensure termination).
  pub fn quote(&self, len: usize, ar: &'b Arena) -> Result<&'b Term<'b>, ir::EvalError<'b>> {
    match self {
      ir::Val::Univ(v) => Ok(ar.named(Term::Univ(*v))),
      ir::Val::Gen(i) => {
        Ok(ar.named(Term::Var(len.checked_sub(i + 1).ok_or_else(|| ir::EvalError::gen_level(*i, len))?)))
      }
      ir::Val::Pi(t, u) => {
        Ok(ar.named(Term::Pi(u.info, t.quote(len, ar)?, u.apply(ir::Val::Gen(len), ar)?.quote(len + 1, ar)?)))
      }
      ir::Val::Fun(b) => Ok(ar.named(Term::Fun(b.info, b.apply(ir::Val::Gen(len), ar)?.quote(len + 1, ar)?))),
      ir::Val::App(f, x, b) => Ok(ar.named(Term::App(f.quote(len, ar)?, x.quote(len, ar)?, *b))),
      ir::Val::Sig(us) => {
        let mut init = ar.named(Term::Unit);
        for (i, u) in us.iter() {
          init = ar.named(Term::Sig(i, init, u.apply(ir::Val::Gen(len), ar)?.quote(len + 1, ar)?));
        }
        Ok(init)
      }
      ir::Val::Tup(bs) => {
        let mut init = ar.named(Term::Star);
        for (i, b) in bs.iter() {
          init = ar.named(Term::Tup(i, init, b.quote(len + 1, ar)?));
        }
        Ok(init)
      }
      ir::Val::Init(n, x) => Ok(ar.named(Term::Init(*n, x.quote(len, ar)?))),
      ir::Val::Last(x) => Ok(ar.named(Term::Last(x.quote(len, ar)?))),
      ir::Val::Meta(_, _) => todo!(),
    }
  }

  /// Given `self`, eliminates as [`Val::Univ`].
  pub fn as_univ(
    self,
    term: &'b Term<'b>,
    ctx: &ir::Stack<'a, 'b>,
    env: &ir::Stack<'a, 'b>,
    ar: &'b Arena,
  ) -> Result<usize, TypeError<'b>> {
    match self {
      ir::Val::Univ(v) => Ok(v),
      ty => Err(TypeError::type_expected(term, ty, ctx, env, ar)),
    }
  }

  /// Given `self`, eliminates as [`Val::Pi`].
  pub fn as_pi(
    self,
    term: Option<&'b Term<'b>>,
    ctx: &ir::Stack<'a, 'b>,
    env: &ir::Stack<'a, 'b>,
    ar: &'b Arena,
  ) -> Result<(&'a ir::Val<'a, 'b>, &'a ir::Clos<'a, 'b>), TypeError<'b>> {
    match self {
      ir::Val::Pi(t, u) => Ok((t, u)),
      ty => match term {
        Some(term) => Err(TypeError::pi_expected(term, ty, ctx, env, ar)),
        None => Err(TypeError::pi_ann_expected(ty, ctx, env, ar)),
      },
    }
  }

  /// Given `self`, eliminates as [`Val::Sig`].
  pub fn as_sig(
    self,
    term: Option<&'b Term<'b>>,
    ctx: &ir::Stack<'a, 'b>,
    env: &ir::Stack<'a, 'b>,
    ar: &'b Arena,
  ) -> Result<&'a [(&'b Field<'b>, ir::Clos<'a, 'b>)], TypeError<'b>> {
    match self {
      ir::Val::Sig(us) => Ok(us),
      ty => match term {
        Some(term) => Err(TypeError::sig_expected(term, ty, ctx, env, ar)),
        None => Err(TypeError::sig_ann_expected(ty, ctx, env, ar)),
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
      Term::Var(ix) => {
        let t = ctx.get(*ix, ar).ok_or_else(|| TypeError::ctx_index(*ix, ctx.len()))?;
        Ok((ar.term(ir::Term::Var(*ix)), t))
      }
      // The (ann) rule is used.
      // To establish pre-conditions for `eval()` and `check()`, the type of `t` is checked first.
      Term::Ann(xn, tn, arena_boundary) => {
        let (t, tt) = tn.infer(ctx, env, ar)?;
        let _ = tt.as_univ(tn, ctx, env, ar)?;
        let tv = t.eval(env, ar)?;
        let x = match arena_boundary {
          false => xn.check(tv, ctx, env, ar)?,
          true => xn.check(tv, ctx, env, &Arena::new()).map(|x| x.relocate(ar)).map_err(|e| e.relocate(ar))?,
        };
        Ok((ar.term(ir::Term::Ann(x, t, *arena_boundary)), tv))
      }
      // The (let) and (extend) rules are used.
      // The (ζ) rule is implicitly used on the value (in normal form) from the recursive call.
      Term::Let(i, vn, xn) => {
        let (v, vt) = vn.infer(ctx, env, ar)?;
        let vv = v.eval(env, ar)?;
        let ctx_ext = ctx.extend(i, vt, ar);
        let env_ext = env.extend(i, vv, ar);
        let (x, t) = xn.infer(&ctx_ext, &env_ext, ar)?;
        Ok((ar.term(ir::Term::Let(i, v, x)), t))
      }
      // The (Π form) and (extend) rules are used.
      Term::Pi(i, tn, un) => {
        let (t, tt) = tn.infer(ctx, env, ar)?;
        let v = tt.as_univ(tn, ctx, env, ar)?;
        let ctx_ext = ctx.extend(i, t.eval(env, ar)?, ar);
        let env_ext = env.extend(i, ir::Val::Gen(env.len()), ar);
        let (u, ut) = un.infer(&ctx_ext, &env_ext, ar)?;
        let w = ut.as_univ(un, &ctx_ext, &env_ext, ar)?;
        Ok((ar.term(ir::Term::Pi(i, t, u)), ir::Val::Univ(Term::pi_univ(v, w)?)))
      }
      // Function abstractions must be enclosed in type annotations, or appear as an argument.
      Term::Fun(_, _) => todo!(),
      // The (Π elim) rule is used.
      Term::App(gn, xn, b) => {
        let (g, gt) = gn.infer(ctx, env, ar)?;
        let (t, u) = gt.as_pi(Some(gn), ctx, env, ar)?;
        let x = xn.check(*t, ctx, env, ar)?;
        Ok((ar.term(ir::Term::App(g, x, *b)), u.apply(x.eval(env, ar)?, ar)?))
      }
      // The (Σ form), (⊤ form) and (extend) rules are used.
      Term::Unit | Term::Sig(_, _, _) => {
        let mut init = self;
        let mut uns = Vec::new();
        while let Term::Sig(i, tn, un) = init {
          init = tn;
          uns.push((*i, un));
        }
        if let Term::Unit = init {
          uns.reverse();
          let mut init = ar.term(ir::Term::Unit);
          let mut us = Vec::new();
          let mut v = Term::unit_univ()?;
          for (i, un) in uns.into_iter() {
            let ctx_ext = ctx.extend(Bound::empty(), ir::Val::Sig(&us), ar);
            let env_ext = env.extend(Bound::empty(), ir::Val::Gen(env.len()), ar);
            let (u, ut) = un.infer(&ctx_ext, &env_ext, ar)?;
            let w = ut.as_univ(un, &ctx_ext, &env_ext, ar)?;
            init = ar.term(ir::Term::Sig(i, init, u));
            us.push((i, ir::Clos { info: Bound::empty(), env: *env, body: u }));
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
      Term::Init(n, xn) => {
        let (x, xt) = xn.infer(ctx, env, ar)?;
        let us = xt.as_sig(Some(xn), ctx, env, ar)?;
        let m = us.len().checked_sub(*n).ok_or_else(|| TypeError::sig_init(*n, us.len()))?;
        Ok((ar.term(ir::Term::Init(*n, x)), ir::Val::Sig(&us[..m])))
      }
      // The (Σ last) rule is used.
      Term::Last(xn) => {
        let (x, xt) = xn.infer(ctx, env, ar)?;
        let us = xt.as_sig(Some(xn), ctx, env, ar)?;
        let i = us.len().checked_sub(1).ok_or_else(|| TypeError::sig_last(1, us.len()))?;
        Ok((ar.term(ir::Term::Last(x)), us[i].1.apply(ir::Term::Init(1, x).eval(env, ar)?, ar)?))
      }
      // Holes must be enclosed in type annotations, or appear as an argument.
      Term::Meta(_) => todo!(),
      // Unresolved names are resolved.
      Term::Name(name) => name.resolve(ctx, env, ar),
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
      Term::Let(i, vn, xn) => {
        let (v, vt) = vn.infer(ctx, env, ar)?;
        let vv = v.eval(env, ar)?;
        let ctx_ext = ctx.extend(i, vt, ar);
        let env_ext = env.extend(i, vv, ar);
        let x = xn.check(t, &ctx_ext, &env_ext, ar)?;
        Ok(ar.term(ir::Term::Let(i, v, x)))
      }
      // The (Π intro) and (extend) rules is used.
      // By pre-conditions, `t` is already known to have universe type.
      Term::Fun(i, bn) => {
        let x = ir::Val::Gen(env.len());
        let (t, u) = t.as_pi(None, ctx, env, ar)?;
        let ctx_ext = ctx.extend(i, *t, ar);
        let env_ext = env.extend(i, x, ar);
        let b = bn.check(u.apply(x, ar)?, &ctx_ext, &env_ext, ar)?;
        Ok(ar.term(ir::Term::Fun(i, b)))
      }
      // The (∑ intro) and (extend) rules are used.
      // By pre-conditions, `t` is already known to have universe type.
      Term::Star | Term::Tup(_, _, _) => {
        let us = t.as_sig(None, ctx, env, ar)?;
        let mut init = self;
        let mut bns = Vec::new();
        while let Term::Tup(i, an, bn) = init {
          init = an;
          bns.push((*i, *bn));
        }
        if let Term::Star = init {
          bns.reverse();
          if bns.len() == us.len() {
            // Eagerly evaluate tuple elements.
            let mut init = ar.term(ir::Term::Star);
            let bs = ar.values(bns.len());
            for (k, ((i, bn), (j, u))) in bns.into_iter().zip(us.iter()).enumerate() {
              if i.name != j.name {
                return Err(TypeError::tup_field_mismatch(ar.named(*self), i.name, j.name));
              }
              // SAFETY: the borrowed range `&bs[..k]` is no longer modified.
              let a = ir::Val::Tup(unsafe { from_raw_parts(bs.as_ptr(), k) });
              let t = ir::Val::Sig(&us[..k]);
              let ctx_ext = ctx.extend(Bound::empty(), t, ar);
              let env_ext = env.extend(Bound::empty(), a, ar);
              let b = bn.check(u.apply(a, ar)?, &ctx_ext, &env_ext, ar)?;
              init = ar.term(ir::Term::Tup(i, init, b));
              bs[k] = (i, b.eval(&env_ext, ar)?);
            }
            Ok(init)
          } else {
            Err(TypeError::tup_size_mismatch(ar.named(*self), bns.len(), us.len()))
          }
        } else {
          Err(TypeError::tup_improper(ar.named(*self)))
        }
      }
      // The (conv) rule is used.
      // By pre-conditions, `t` is already known to have universe type.
      xn => {
        let (x, xt) = xn.infer(ctx, env, ar)?;
        let res = ir::Val::conv(&xt, &t, env.len(), ar)?.then_some(x);
        res.ok_or_else(|| TypeError::type_mismatch(ar.named(*xn), xt, t, ctx, env, ar))
      }
    }
  }
}
