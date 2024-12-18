use typed_arena::Arena;

use super::*;

/// Variable entries.
pub struct Var<'a> {
  pub ty: &'a Term<'a>,
  pub def: Option<&'a Term<'a>>,
  pub info: BinderInfo,
}

/// Metavariable entries.
pub struct Meta<'a> {
  pub ty: &'a Term<'a>,
  pub def: Option<&'a Term<'a>>,
  pub level: usize,
}

/// One of the two central data structures of the elaborator. The other one is [`Term`].
///
/// It contains the following kinds of entries:
///
/// * [`Context::vars`]: the variable entries. Each contains a type term [`Var::ty`], and an optional definition term
///   [`Var::def`]. For the `i`-th variable entry `vars[i]`, both terms are to be associated with the context
///   with variable entries being `vars[0..i]` (note that the `i`-th variable entry itself is not included).
///
/// * [`Context::metas`]: the metavariable entries. Each contains a type term [`Meta::ty`], and an optional definition
///   term [`Meta::def`] (also called the "solution" if exists). Both terms are to be associated with the context
///   with variable entries being `vars[0..n]`, where `n` is the value of [`Meta::level`].
///
///   * Unlike variable entries which are pushed and popped like a stack when traversing through a term, metavariable
///     entries are created but never removed as elaboration progresses. Unsolved metavariables can remain indefinitely,
///     allowing them to be solved later. They are otherwise very much similar to free variables.
///
///   * The context level specifies the permitted dependencies of a metavariable. It is a frequent operation that
///     when leaving a scope, all unsolved metavariables associated with the current context are strengthened
///     (i.e. the dependencies on the last variable entry are removed). To reduce overhead, we keep a mapping
///     [`Context::meta_by_level`] from context levels to unsolved metavariables.
pub struct Context<'a> {
  vars: Vec<Var<'a>>,
  metas: Vec<Meta<'a>>,
  meta_by_level: Vec<Vec<usize>>,
}

impl<'a> Context<'a> {
  pub fn new() -> Self {
    Self { vars: Vec::new(), metas: Vec::new(), meta_by_level: Vec::from([Vec::new()]) }
  }

  pub fn is_empty(&self) -> bool {
    self.vars.is_empty()
  }

  // /// Returns the type of the `i`-th last variable, appropriately weakened.
  // pub fn var_ty(&self, i: usize, pool: &'a Arena<Term<'a>>) -> Option<&'a Term<'a>> {
  //   self.vars.get(self.vars.len() - 1 - i).map(|e| e.ty.shift(0, i + 1, pool))
  // }

  // /// Returns the definition of the `i`-th last variable, appropriately weakened.
  // pub fn var_def(&self, i: usize, pool: &'a Arena<Term<'a>>) -> Option<&'a Term<'a>> {
  //   self.vars.get(self.vars.len() - 1 - i).and_then(|e| e.def.map(|def| def.shift(0, i + 1, pool)))
  // }

  // /// Returns the binder info of the `i`-th last variable.
  // pub fn var_info(&self, i: usize) -> Option<BinderInfo> {
  //   self.vars.get(self.vars.len() - 1 - i).map(|e| e.info)
  // }

  // /// Returns the type of the `i`-th metavariable, appropriately weakened.
  // pub fn meta_ty(&self, i: usize, pool: &'a Arena<Term<'a>>) -> Option<&'a Term<'a>> {
  //   self.metas.get(i).map(|e| e.ty.shift(0, self.vars.len() - e.level, pool))
  // }

  // /// Returns the definition of the `i`-th metavariable, appropriately weakened.
  // pub fn meta_def(&self, i: usize, pool: &'a Arena<Term<'a>>) -> Option<&'a Term<'a>> {
  //   self.metas.get(i).and_then(|e| e.def.map(|def| def.shift(0, self.vars.len() - e.level, pool)))
  // }

  // /// Returns the context level of the `i`-th metavariable.
  // pub fn meta_level(&self, i: usize) -> Option<usize> {
  //   self.metas.get(i).map(|e| e.level)
  // }

  // /// Pushes a new variable entry.
  // pub fn push(&mut self, ty: &'a Term<'a>, def: Option<&'a Term<'a>>, info: BinderInfo) {
  //   self.vars.push(Var { ty, def, info });
  //   self.meta_by_level.push(Vec::new());
  // }

  // /// Creates a new unsolved metavariable entry and returns its ID.
  // pub fn meta(&mut self, ty: &'a Term<'a>) -> usize {
  //   let id = self.metas.len();
  //   self.metas.push(Meta { ty, def: None, level: self.vars.len() });
  //   self.meta_by_level.last_mut().unwrap().push(id);
  //   id
  // }

  // /// Pops the last variable entry.
  // pub fn pop(&mut self) -> Var<'a> {
  //   let res = self.vars.pop().unwrap();
  //   let mut last_metas = self.meta_by_level.pop().unwrap();
  //   for &id in &last_metas {
  //     self.metas[id].level = self.vars.len();
  //   }
  //   self.meta_by_level.last_mut().unwrap().append(&mut last_metas);
  //   todo!();
  //   res
  // }
}

impl<'a> Default for Context<'a> {
  fn default() -> Self {
    Self::new()
  }
}
