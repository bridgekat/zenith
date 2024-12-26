use super::*;

impl<'a, 'b> Stack<'a, 'b> {
  pub fn new() -> Self {
    Stack::Nil
  }

  pub fn is_empty(&self) -> bool {
    match self {
      Stack::Nil => true,
      Stack::Cons { prev: _, value: _ } => false,
    }
  }

  pub fn len(&self) -> usize {
    let mut curr = self;
    let mut len = 0;
    while let Stack::Cons { prev, value: _ } = curr {
      len += 1;
      curr = prev;
    }
    len
  }

  pub fn get(&self, index: usize, ar: &'a Arena) -> Option<Val<'a, 'b>> {
    let mut curr = self;
    let mut index = index;
    ar.inc_lookup_count();
    while let Stack::Cons { prev, value } = curr {
      ar.inc_link_count();
      if index == 0 {
        return Some(**value);
      }
      index -= 1;
      curr = prev;
    }
    None
  }

  pub fn extend(&self, value: Val<'a, 'b>, ar: &'a Arena) -> Self {
    Stack::Cons { prev: ar.frame(*self), value: ar.val(value) }
  }
}

impl Default for Stack<'_, '_> {
  fn default() -> Self {
    Self::new()
  }
}
