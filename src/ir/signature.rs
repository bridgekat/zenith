//! # Term signature
//!
//! This module implements the core term signature. It contains a list of records for holes.

use super::*;

#[derive(Debug, Clone)]
pub struct Hole<'a, 'b> {
  pub ctx: Stack<'a, 'b>,
  pub env: Stack<'a, 'b>,
  pub ty: Val<'a, 'b>,
  pub solution: Option<Term<'a, 'b, Core>>,
}

/// # Signatures
///
/// Signatures contain records for holes. The records are not necessarily in the same order as
/// in the mathematical formulation. This means solutions of earlier holes may contain later ones,
/// although a linear ordering that respects dependencies should still exist.
#[derive(Debug, Clone)]
pub struct Signature<'a, 'b> {
  holes: Vec<Hole<'a, 'b>>,
}

impl<'a, 'b> Default for Signature<'a, 'b> {
  fn default() -> Self {
    Self::new()
  }
}

impl<'a, 'b> Signature<'a, 'b> {
  pub fn new() -> Self {
    Self { holes: Vec::new() }
  }

  pub fn add_hole(&mut self, ctx: Stack<'a, 'b>, env: Stack<'a, 'b>, ty: Val<'a, 'b>) {
    self.holes.push(Hole { ctx, env, ty, solution: None });
  }

  pub fn solve_hole(&mut self, i: usize, solution: Term<'a, 'b, Core>) {
    if let Some(hole) = self.holes.get_mut(i) {
      hole.solution = Some(solution);
    }
  }

  pub fn get_hole(&self, i: usize) -> Option<&Hole<'a, 'b>> {
    self.holes.get(i)
  }
}
