//! # Stacks
//!
//! This module implements a generic stack for both environments and contexts.

use super::*;
use crate::arena::Arena;

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
  pub fn get(&self, ix: usize, ar: &'a Arena) -> Option<(Bound<'b>, Val<'a, 'b>)> {
    let mut curr = self;
    let mut ix = ix;
    ar.inc_lookup_count();
    while let Stack::Cons { prev, info, value } = curr {
      ar.inc_link_count();
      if ix == 0 {
        return Some((**info, *value));
      }
      ix -= 1;
      curr = prev;
    }
    None
  }

  /// Extends the stack with a new value.
  pub fn extend(&self, info: &'b Bound<'b>, value: Val<'a, 'b>, ar: &'a Arena) -> Self {
    Stack::Cons { prev: ar.frame(self.clone()), info, value }
  }

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
        return Some((ix, None, *t));
      }
      // Check for direct transparent bindings.
      if info.name.is_empty() {
        if let Val::Sig(us) = t {
          for (n, (info, u)) in us.iter().rev().enumerate() {
            if info.name == name {
              let u =
                Val::apply(u, Val::eval(&Term::Init(n + 1, ar.term(Term::Var(ix))), env, ar).unwrap(), ar).unwrap();
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
