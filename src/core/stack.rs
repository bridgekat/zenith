use super::*;

#[cfg(not(feature = "linked_frame_stacks"))]
mod linked_list_stack_impl {
  use super::*;

  impl<'a> Stack<'a> {
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

    pub fn get(&self, index: usize, ar: &'a Arena) -> Option<Val<'a>> {
      let mut curr = self;
      let mut index = index;
      ar.inc_lookup_count();
      while let Stack::Cons { prev, value } = curr {
        ar.inc_link_count();
        if index == 0 {
          return Some((*value).clone());
        }
        index -= 1;
        curr = prev;
      }
      None
    }

    pub fn truncate(&self, amount: usize, ar: &'a Arena) -> Option<Self> {
      let mut curr = self;
      let mut remaining = amount;
      ar.inc_lookup_count();
      while let Stack::Cons { prev, value: _ } = curr {
        ar.inc_link_count();
        if remaining == 0 {
          return Some(curr.clone());
        }
        remaining -= 1;
        curr = prev;
      }
      if remaining == 0 {
        return Some(Stack::Nil);
      }
      None
    }

    pub fn extend(&self, value: Val<'a>, ar: &'a Arena) -> Self {
      Stack::Cons { prev: ar.frame(self.clone()), value: ar.val(value) }
    }
  }

  impl Default for Stack<'_> {
    fn default() -> Self {
      Self::new()
    }
  }
}

#[cfg(feature = "linked_frame_stacks")]
mod linked_frame_stack_impl {
  use super::*;
  use std::num::NonZeroUsize;

  impl<'a> Stack<'a> {
    pub fn new() -> Self {
      Stack::Empty
    }

    pub fn is_empty(&self) -> bool {
      match self {
        Stack::Empty => true,
        Stack::Ptr { frame: _, position: _ } => false,
      }
    }

    pub fn len(&self) -> usize {
      let mut curr = self;
      let mut len = 0;
      while let Stack::Ptr { frame, position } = curr {
        len += position.get();
        curr = &frame.prev;
      }
      len
    }

    pub fn get(&self, index: usize, ar: &'a Arena) -> Option<Val<'a>> {
      let mut curr = self;
      let mut index = index;
      ar.inc_lookup_count();
      while let Stack::Ptr { frame, position } = curr {
        ar.inc_link_count();
        if index < position.get() {
          // SAFETY: no reference to the inside of the cell outlives the statement, which consists
          // of a move and never re-enters `self` through indirect calls.
          let value = unsafe { std::mem::take(&mut (*frame.entries.get())[position.get() - 1 - index].value) };
          // Cloning must be done separately: re-entering through `clone()` is possible.
          let res = value.as_ref().unwrap().clone();
          // SAFETY: no reference to the inside of the cell outlives the statement, which consists
          // of a move and never re-enters `self` through indirect calls.
          unsafe { (*frame.entries.get())[position.get() - 1 - index].value = value };
          // The cloned value is returned.
          return Some(res);
        }
        index -= position.get();
        curr = &frame.prev;
      }
      None
    }

    pub fn truncate(&self, amount: usize, ar: &'a Arena) -> Option<Self> {
      let mut curr = self;
      let mut remaining = amount;
      ar.inc_lookup_count();
      while let Stack::Ptr { frame, position } = curr {
        ar.inc_link_count();
        if remaining < position.get() {
          // SAFETY: no reference to the inside of the cell outlives the statement, which consists
          // of an increment and never re-enters `self` through indirect calls.
          unsafe { (*frame.entries.get())[position.get() - 1 - remaining].refcount += 1 };
          // A new pointer is returned. Reference counting done in the previous line.
          return Some(Stack::Ptr { frame, position: NonZeroUsize::new(position.get() - remaining).unwrap() });
        }
        remaining -= position.get();
        curr = &frame.prev;
      }
      if remaining == 0 {
        return Some(Stack::Empty);
      }
      None
    }

    pub fn extend(&self, value: Val<'a>, ar: &'a Arena) -> Self {
      // If the current pointer is at the end of a frame, we can append to it.
      // Otherwise, we need to branch off or create a new frame.
      let entry = Entry { value: Some(value), refcount: 1 };
      ar.inc_val_count();
      match self {
        Stack::Ptr { frame, position } => {
          // SAFETY: no reference to the inside of the cell outlives the statement, which consists
          // of a data access and never re-enters `self` through indirect calls.
          if unsafe { (*frame.entries.get()).len() == position.get() } {
            // SAFETY: no reference to the inside of the cell outlives the statement, which consists
            // of moves and never re-enters `self` through indirect calls.
            unsafe { (*frame.entries.get()).push(entry) };
            // A new pointer is returned. Reference counting done in the first line.
            Stack::Ptr { frame, position: NonZeroUsize::new(position.get() + 1).unwrap() }
          } else {
            // SAFETY: no reference to the inside of the cell outlives the statement, which consists
            // of an increment and never re-enters `self` through indirect calls.
            unsafe { (*frame.entries.get())[position.get() - 1].refcount += 1 };
            // A new pointer is created. Reference counting done in the previous line.
            let prev = Stack::Ptr { frame, position: *position };
            let frame = ar.frame(prev, entry);
            let position = NonZeroUsize::new(1).unwrap();
            // A new pointer is returned. Reference counting done in the first line.
            Stack::Ptr { frame, position }
          }
        }
        Stack::Empty => {
          let frame = ar.frame(Stack::Empty, entry);
          let position = NonZeroUsize::new(1).unwrap();
          // A new pointer is returned. Reference counting done in the first line.
          Stack::Ptr { frame, position }
        }
      }
    }
  }

  impl Default for Stack<'_> {
    fn default() -> Self {
      Self::new()
    }
  }

  impl Clone for Stack<'_> {
    fn clone(&self) -> Self {
      match self {
        Stack::Empty => Stack::Empty,
        Stack::Ptr { frame, position } => {
          // SAFETY: no reference to the inside of the cell outlives the statement, which consists
          // of an increment and never re-enters `self` through indirect calls.
          unsafe { (*frame.entries.get())[position.get() - 1].refcount += 1 };
          // A new pointer is created. Reference counting done in the previous line.
          Stack::Ptr { frame, position: *position }
        }
      }
    }
  }

  impl Drop for Stack<'_> {
    fn drop(&mut self) {
      match self {
        Stack::Empty => {}
        Stack::Ptr { frame, position } => {
          // SAFETY: no reference to the inside of the cell outlives the statement, which consists
          // of a decrement and never re-enters `self` through indirect calls.
          unsafe { (*frame.entries.get())[position.get() - 1].refcount -= 1 };
          // SAFETY: no reference to the inside of the cell outlives the statement, which consists
          // of a data access and never re-enters `self` through indirect calls.
          while unsafe { (*frame.entries.get()).last().is_some_and(|entry| entry.refcount == 0) } {
            // SAFETY: no reference to the inside of the cell outlives the statement, which consists
            // of a move and never re-enters `self` through indirect calls.
            let value = unsafe { std::mem::take(&mut (*frame.entries.get()).last_mut().unwrap().value) };
            // SAFETY: no reference to the inside of the cell outlives the statement, which consists
            // of a decrement and never re-enters `self` through indirect calls.
            unsafe { (*frame.entries.get()).pop() };
            // Dropping must be done separately: re-entering through `drop()` is possible.
            // In particular, dropping a value containing a closure causes a recursive call to this
            // function. The reference counting invariant must hold at this point.
            std::mem::drop(value);
          }
        }
      }
    }
  }
}
