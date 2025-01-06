use std::slice::from_raw_parts;

use super::*;
use crate::arena::{Arena, Relocate};
use crate::ir::{Bound, Clos, Core, Name, Named, Stack, Term, TypeError, Val};

impl<'a, 'b> Stack<'a, 'b> {
  /// Returns the value with the given name, if it exists.
  ///
  /// Pre-conditions:
  ///
  /// - `self` is well-formed context.
  pub fn get_by_name(&self, name: Name<'b>, env: &Self, ar: &'a Arena) -> Option<(usize, Option<usize>, Val<'a, 'b>)> {
    let mut curr = self;
    let mut ix = 0;
    ar.inc_lookup_count();
    while let Stack::Cons { prev, info, value: t } = curr {
      ar.inc_link_count();
      // Check for direct bindings.
      if info.name == name {
        // The (var) rule is used.
        return Some((ix, None, *t));
      }
      // Check for direct transparent bindings.
      if info.name.is_empty() {
        if let Val::Sig(us) = t {
          for (n, (info, u)) in us.iter().rev().enumerate() {
            if info.name == name {
              // The (var) and (Σ proj) rules are used.
              let u = u.apply(Term::Init(n + 1, ar.term(Term::Var(ix))).eval(env, ar).unwrap(), ar).unwrap();
              return Some((ix, Some(n), u));
            }
          }
        }
      }
      ix += 1;
      curr = prev;
    }
    None
  }

  /// Checks if a name can be directly used as a named variable.
  ///
  /// Pre-conditions:
  ///
  /// - `self` is well-formed context.
  pub fn is_name_valid(&self, ix: usize, proj: Option<usize>, name: Name<'b>, _env: &Self, ar: &'a Arena) -> bool {
    // Only non-empty names may be used.
    if !name.is_empty() {
      let mut curr = self;
      let mut ix = ix;
      ar.inc_lookup_count();
      while let Stack::Cons { prev, info, value } = curr {
        ar.inc_link_count();
        // Already reached the desired index.
        if ix == 0 {
          return match proj {
            None => info.name == name,
            Some(n) => {
              if let Val::Sig(us) = value {
                let mut n = n;
                for (info, _) in us.iter().rev() {
                  // Already reached the desired index.
                  if n == 0 {
                    return info.name == name;
                  }
                  // Check for shadowing in direct fields.
                  if info.name == name {
                    return false;
                  }
                  n -= 1;
                }
              }
              false
            }
          };
        }
        // Check for shadowing in direct bindings.
        if info.name == name {
          return false;
        }
        // Check for shadowing in direct transparent bindings.
        if info.name.is_empty() {
          if let Val::Sig(us) = value {
            if us.iter().any(|(info, _)| info.name == name) {
              return false;
            }
          }
        }
        ix -= 1;
        curr = prev;
      }
    }
    false
  }
}

impl<'b> Name<'b> {
  /// Resolves a named variable to a core term and its type.
  pub fn resolve_named_var<'a>(
    &self,
    ctx: &Stack<'a, 'b>,
    env: &Stack<'a, 'b>,
    ar: &'a Arena,
  ) -> Result<(Term<'a, 'b, Core>, Val<'a, 'b>), ElabError<'a, 'b>> {
    let (ix, proj, x_type) = ctx.get_by_name(*self, env, ar).ok_or_else(|| ElabError::ctx_name(*self))?;
    match proj {
      None => Ok((Term::Var(ix), x_type)),
      Some(n) => Ok((Term::Proj(n, ar.term(Term::Var(ix))), x_type)),
    }
  }

  /// Resolves a named projection to a core term and its type.
  pub fn resolve_named_proj<'a>(
    &self,
    x_old: &'a Term<'a, 'b, Named>,
    x_new: Term<'a, 'b, Core>,
    x_type: Val<'a, 'b>,
    ctx: &Stack<'a, 'b>,
    env: &Stack<'a, 'b>,
    ar: &'a Arena,
  ) -> Result<(Term<'a, 'b, Core>, Val<'a, 'b>), ElabError<'a, 'b>> {
    match x_type {
      Val::Sig(us) => {
        for (n, (info, u)) in us.iter().rev().enumerate() {
          // Check for direct fields.
          if info.name == *self {
            // The (Σ proj) rule is used.
            let t = u.apply(Term::Init(n + 1, ar.term(x_new)).eval(env, ar)?, ar)?;
            return Ok((Term::Proj(n, ar.term(x_new)), t));
          }
        }
        Err(ElabError::sig_name(*self, x_old, x_type, ctx, env, ar))
      }
      _ => Err(ElabError::sig_expected(*self, x_old, x_type, ctx, env, ar)),
    }
  }

  /// Presents a variable as a named variable and returns its type.
  pub fn present_named_var<'a>(
    ix: usize,
    proj: Option<usize>,
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
        let us_val = t_val.as_sig(|t_val| TypeError::sig_expected(ar.term(Term::Var(ix)), t_val, ctx, env, ar))?;
        let i =
          us_val.len().checked_sub(n + 1).ok_or_else(|| TypeError::sig_proj(n, Val::Sig(us_val), ctx, env, ar))?;
        let (info, u_val) = &us_val[i];
        let u_val = u_val.apply(Term::Init(n + 1, ar.term(Term::Var(ix))).eval(env, ar)?, ar)?;
        match ctx.is_name_valid(ix, proj, info.name, env, ar) {
          true => Ok((Term::NamedVar(info.name, ()), u_val)),
          false => Ok((Term::Proj(n, ar.term(Term::Var(ix))), u_val)),
        }
      }
    }
  }

  /// Presents a projection as a named projection and returns its type.
  pub fn present_named_proj<'a>(
    n: usize,
    x_old: &'a Term<'a, 'b, Core>,
    x_new: Term<'a, 'b, Named>,
    x_type: Val<'a, 'b>,
    ctx: &Stack<'a, 'b>,
    env: &Stack<'a, 'b>,
    ar: &'a Arena,
  ) -> Result<(Term<'a, 'b, Named>, Val<'a, 'b>), TypeError<'a, 'b, Core>> {
    let us_val = x_type.as_sig(|x_type| TypeError::sig_expected(x_old, x_type, ctx, env, ar))?;
    let i = us_val.len().checked_sub(n + 1).ok_or_else(|| TypeError::sig_proj(n, Val::Sig(us_val), ctx, env, ar))?;
    let (info, u_val) = &us_val[i];
    let u_val = u_val.apply(Term::Init(n + 1, x_old).eval(env, ar)?, ar)?;
    match !info.name.is_empty() && !us_val.iter().rev().take(n).any(|(i, _)| i.name == info.name) {
      true => Ok((Term::NamedProj(info.name, ar.term(x_new), ()), u_val)),
      false => Ok((Term::Proj(n, ar.term(x_new)), u_val)),
    }
  }
}

impl<'a, 'b> Term<'a, 'b, Named> {
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
  ) -> Result<(Term<'a, 'b, Core>, Val<'a, 'b>), ElabError<'a, 'b>> {
    match self {
      // The garbage collection mark forces the subterm to be inferred inside a new arena.
      Term::Gc(x) => {
        x.infer(ctx, env, &Arena::new()).map(|(x, v)| (x.relocate(ar), v.relocate(ar))).map_err(|e| e.relocate(ar))
      }
      // The (univ) rule is used.
      Term::Univ(v) => Ok(((Term::Univ(*v)), Val::Univ(Term::univ_univ(*v)?))),
      // The (ann) rule is used.
      // To establish pre-conditions for `eval()` and `check()`, the type of `t` is checked first.
      Term::Ann(x_old, t_old) => {
        let (t_new, t_type) = t_old.infer(ctx, env, ar)?;
        let _ = t_type.as_univ(|t_type| TypeError::type_expected(t_old, t_type, ctx, env, ar))?;
        let t_val = t_new.eval(env, ar)?;
        let x_new = x_old.check(t_val, ctx, env, ar)?;
        Ok(((Term::Ann(ar.term(x_new), ar.term(t_new))), t_val))
      }
      // The (let) and (extend) rules are used.
      // The (ζ) rule is implicitly used on the value (in normal form) from the recursive call.
      Term::Let(info, v_old, x_old) => {
        let (v_new, v_type) = v_old.infer(ctx, env, ar)?;
        let v_val = v_new.eval(env, ar)?;
        let ctx_ext = ctx.extend(info, v_type, ar);
        let env_ext = env.extend(info, v_val, ar);
        let (x_new, x_type) = x_old.infer(&ctx_ext, &env_ext, ar)?;
        Ok(((Term::Let(info, ar.term(v_new), ar.term(x_new))), x_type))
      }
      // The (Π form) and (extend) rules are used.
      Term::Pi(info, t_old, u_old) => {
        let (t_new, t_type) = t_old.infer(ctx, env, ar)?;
        let t_lvl = t_type.as_univ(|t_type| TypeError::type_expected(t_old, t_type, ctx, env, ar))?;
        let ctx_ext = ctx.extend(info, t_new.eval(env, ar)?, ar);
        let env_ext = env.extend(info, Val::Free(env.len()), ar);
        let (u_new, u_type) = u_old.infer(&ctx_ext, &env_ext, ar)?;
        let u_lvl = u_type.as_univ(|u_type| TypeError::type_expected(u_old, u_type, ctx, env, ar))?;
        Ok(((Term::Pi(info, ar.term(t_new), ar.term(u_new))), Val::Univ(Term::pi_univ(t_lvl, u_lvl)?)))
      }
      // Function abstractions must be enclosed in type annotations, or appear as an argument.
      Term::Fun(_, _) => Err(TypeError::ann_expected(ar.term(*self)).into()),
      // The (Π elim) rule is used.
      Term::App(f_old, x_old, dot) => {
        let (f_new, f_type) = f_old.infer(ctx, env, ar)?;
        let (t_val, u_val) = f_type.as_pi(|f_type| TypeError::pi_expected(f_old, f_type, ctx, env, ar))?;
        let x_new = x_old.check(*t_val, ctx, env, ar)?;
        Ok(((Term::App(ar.term(f_new), ar.term(x_new), *dot)), u_val.apply(x_new.eval(env, ar)?, ar)?))
      }
      // The (Σ form), (⊤ form) and (extend) rules are used.
      Term::Sig(us_old) => {
        let mut lvl = Term::unit_univ()?;
        let us_new = ar.terms(us_old.len());
        let us_val = ar.closures(us_old.len()).as_mut_ptr();
        for (i, (info, u_old)) in us_old.iter().enumerate() {
          // SAFETY: the borrowed range `&us_val[..i]` is no longer modified.
          let t_val = Val::Sig(unsafe { from_raw_parts(us_val, i) });
          let x_val = Val::Free(env.len());
          let ctx_ext = ctx.extend(Bound::empty(), t_val, ar);
          let env_ext = env.extend(Bound::empty(), x_val, ar);
          let (u_new, u_type) = u_old.infer(&ctx_ext, &env_ext, ar)?;
          let u_lvl = u_type.as_univ(|u_type| TypeError::type_expected(u_old, u_type, ctx, env, ar))?;
          lvl = Term::sig_univ(lvl, u_lvl)?;
          us_new[i] = (*info, u_new);
          let u_val = Clos { info: Bound::empty(), env: env.clone(), body: ar.term(u_new) };
          // SAFETY: `i < us_old.len()` which is the valid size of `us_val`.
          unsafe { *us_val.add(i) = (info, u_val) };
        }
        Ok(((Term::Sig(us_new)), Val::Univ(lvl)))
      }
      // Tuple constructors must be enclosed in type annotations, or appear as an argument.
      Term::Tup(_) => Err(TypeError::ann_expected(ar.term(*self)).into()),
      // The (Σ init) rule is used.
      Term::Init(n, x_old) => {
        let (x_new, x_type) = x_old.infer(ctx, env, ar)?;
        let us_val = x_type.as_sig(|x_type| TypeError::sig_expected(x_old, x_type, ctx, env, ar))?;
        let m = us_val.len().checked_sub(*n).ok_or_else(|| TypeError::sig_init(*n, Val::Sig(us_val), ctx, env, ar))?;
        Ok(((Term::Init(*n, ar.term(x_new))), Val::Sig(&us_val[..m])))
      }
      // Holes must be enclosed in type annotations, or appear as an argument.
      Term::Meta(_) => Err(TypeError::ann_expected(ar.term(*self)).into()),
      // The (var) and (Σ proj) rules are used.
      // Unresolved names are resolved.
      Term::Var(ix) => {
        let (_, t_val) = ctx.get(*ix, ar).ok_or_else(|| TypeError::ctx_index(*ix, ctx.len()))?;
        Ok(((Term::Var(*ix)), t_val))
      }
      Term::Proj(n, x_old) => {
        let (x_new, x_type) = x_old.infer(ctx, env, ar)?;
        let us_val = x_type.as_sig(|x_type| TypeError::sig_expected(x_old, x_type, ctx, env, ar))?;
        let i =
          us_val.len().checked_sub(n + 1).ok_or_else(|| TypeError::sig_proj(*n, Val::Sig(us_val), ctx, env, ar))?;
        Ok(((Term::Proj(*n, ar.term(x_new))), us_val[i].1.apply(Term::Init(n + 1, ar.term(x_new)).eval(env, ar)?, ar)?))
      }
      Term::NamedVar(name, _) => name.resolve_named_var(ctx, env, ar),
      Term::NamedProj(name, x_old, _) => {
        let (x_new, x_type) = x_old.infer(ctx, env, ar)?;
        name.resolve_named_proj(x_old, x_new, x_type, ctx, env, ar)
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
    ctx: &Stack<'a, 'b>,
    env: &Stack<'a, 'b>,
    ar: &'a Arena,
  ) -> Result<Term<'a, 'b, Core>, ElabError<'a, 'b>> {
    match self {
      // The (let) and (extend) rules are used.
      // The (ζ) rule is implicitly inversely used on the `t` passed into the recursive call.
      Term::Let(info, v_old, x_old) => {
        let (v_new, v_type) = v_old.infer(ctx, env, ar)?;
        let v_val = v_new.eval(env, ar)?;
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
              return Err(TypeError::tup_field_mismatch(ar.term(*self), info.name, u_info.name).into());
            }
            let t_val = Val::Sig(&us_val[..i]);
            // SAFETY: the borrowed range `&bs_val[..i]` is no longer modified.
            let a_val = Val::Tup(unsafe { from_raw_parts(bs_val, i) });
            let ctx_ext = ctx.extend(Bound::empty(), t_val, ar);
            let env_ext = env.extend(Bound::empty(), a_val, ar);
            let b_new = b_old.check(u_val.apply(a_val, ar)?, &ctx_ext, &env_ext, ar)?;
            bs_new[i] = (info, b_new);
            let b_val = b_new.eval(&env_ext, ar)?;
            // SAFETY: `i < bs_old.len()` which is the valid size of `bs_val`.
            unsafe { *bs_val.add(i) = (info, b_val) };
          }
          Ok(Term::Tup(bs_new))
        } else {
          Err(TypeError::tup_size_mismatch(ar.term(*self), bs_old.len(), us_val.len()).into())
        }
      }
      // TODO
      Term::Meta(_) => todo!(),
      // The (conv) rule is used.
      // By pre-conditions, `t` is already known to have universe type.
      x_old => {
        let (x_new, x_type) = x_old.infer(ctx, env, ar)?;
        let res = Val::conv(&x_type, &t, env.len(), ar)?.then_some(x_new);
        res.ok_or_else(|| TypeError::type_mismatch(ar.term(*x_old), x_type, t, ctx, env, ar).into())
      }
    }
  }
}
