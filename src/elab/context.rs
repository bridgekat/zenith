use bumpalo::Bump;

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
  pub ctx: usize,
}

/// Typing contexts.
pub struct Context<'a> {
  meta: Vec<Meta<'a>>,
  metactx: Vec<Vec<usize>>,
  ctx: Vec<Var<'a>>,
}

impl<'a> Context<'a> {
  pub fn new() -> Self {
    Self { meta: Vec::new(), metactx: Vec::from([Vec::new()]), ctx: Vec::new() }
  }

  pub fn is_empty(&self) -> bool {
    self.ctx.is_empty()
  }

  pub fn meta_ty(&self, i: usize, pool: &'a Bump) -> Option<&'a Term<'a>> {
    self.meta.get(i).map(|e| e.ty.shift(0, self.ctx.len() - e.ctx, pool))
  }

  pub fn meta_def(&self, i: usize, pool: &'a Bump) -> Option<&'a Term<'a>> {
    todo!();
    self.meta.get(i).and_then(|e| e.def).map(|def| def.shift(0, i + 1, pool))
  }

  pub fn meta_ctx(&self, i: usize) -> Option<usize> {
    self.meta.get(i).map(|e| e.ctx)
  }

  pub fn var_ty(&self, i: usize, pool: &'a Bump) -> Option<&'a Term<'a>> {
    self.ctx.get(self.ctx.len() - 1 - i).map(|e| e.ty.shift(0, i + 1, pool))
  }

  pub fn var_def(&self, i: usize, pool: &'a Bump) -> Option<&'a Term<'a>> {
    self.ctx.get(self.ctx.len() - 1 - i).and_then(|e| e.def).map(|def| def.shift(0, i + 1, pool))
  }

  pub fn var_info(&self, i: usize) -> Option<BinderInfo> {
    self.ctx.get(self.ctx.len() - 1 - i).map(|e| e.info)
  }

  /// Creates new meta at current context.
  pub fn meta(&mut self, ty: &'a Term<'a>) -> usize {
    todo!();
    let meta = self.meta.len();
    self.meta.push(Meta { ty, def: None, ctx: self.ctx.len() });
    meta
  }

  pub fn push(&mut self, ty: &'a Term<'a>, def: Option<&'a Term<'a>>, info: BinderInfo) {
    self.ctx.push(Var { ty, def, info });
    self.metactx.push(Vec::new());
  }

  pub fn pop(&mut self) -> Option<Var<'a>> {
    if let Some(res) = self.ctx.pop() {
      let mut last_metas = self.metactx.pop().unwrap();
      for &meta in &last_metas {
        self.meta[meta].ctx = self.ctx.len();
      }
      self.metactx.last_mut().unwrap().append(&mut last_metas);
      todo!();
      Some(res)
    } else {
      None
    }
  }
}

impl<'a> Default for Context<'a> {
  fn default() -> Self {
    Self::new()
  }
}
