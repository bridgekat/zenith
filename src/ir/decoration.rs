//! # Term decorations
//!
//! This module defines possible [`Decoration`]s that can be applied to core terms.

use std::fmt::Debug;

use crate::arena::Arena;

/// # Variable and field names
///
/// This is simply a wrapper around a string reference.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Name<'a>(pub &'a str);

/// # Binder information
///
/// Auxiliary information for bound variables (e.g. names, attributes).
#[derive(Debug, Clone, Copy)]
pub struct Bound<'b> {
  pub name: Name<'b>,
  pub attrs: &'b [&'b str],
}

/// # Field information
///
/// Auxiliary information for field variables (e.g. names, attributes).
#[derive(Debug, Clone, Copy)]
pub struct Field<'b> {
  pub name: Name<'b>,
  pub attrs: &'b [&'b str],
}

/// # Term decorations
///
/// Specifies decorations to the core terms.
pub trait Decoration: Debug + Clone + Copy {
  type NamedVar<'b>: Debug + Clone + Copy;
  type NamedProj<'b>: Debug + Clone + Copy;
}

/// # Core term decoration
///
/// The core calculus does not support named variables or projections.
#[derive(Debug, Clone, Copy)]
pub struct Core;

/// # Named term decoration
///
/// The named calculus supports named variables and projections.
#[derive(Debug, Clone, Copy)]
pub struct Named;

impl Decoration for Core {
  type NamedVar<'b> = !;
  type NamedProj<'b> = !;
}

impl Decoration for Named {
  type NamedVar<'b> = ();
  type NamedProj<'b> = ();
}

impl Name<'_> {
  /// Returns if the name is empty (i.e. transparent).
  pub fn is_empty(&self) -> bool {
    let Self(name) = self;
    name.is_empty()
  }
}

impl<'b> Bound<'b> {
  /// Creates a new bound variable info with empty name (i.e. transparent).
  pub fn empty() -> &'b Self {
    &Self { name: Name(""), attrs: &[] }
  }

  /// Creates a new bound variable info in the given arena.
  pub fn new(name: Name<'b>, attrs: &[&str], ar: &'b Arena) -> Self {
    Self { name, attrs: ar.strings(attrs) }
  }
}

impl<'b> Field<'b> {
  /// Creates a new field variable info with empty name (for writing).
  pub fn empty() -> &'b Self {
    &Self { name: Name(""), attrs: &[] }
  }

  /// Creates a new field variable info in the given arena.
  pub fn new(name: Name<'b>, attrs: &[&str], ar: &'b Arena) -> Self {
    Self { name, attrs: ar.strings(attrs) }
  }
}
