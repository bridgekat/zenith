//! # Linked frame stacks
//!
//! In the simplest implementation of NbE, evaluation environments are represented as linked lists
//! of definitions. This becomes infeasible when the environment grows large, as indexing into a
//! linked list is O(n). On the other hand, environments should support fast pushing and cloning
//! (for the creation of closures), and arrays cannot be cloned efficiently. The same tension arises
//! in functional programming language interpreters, and is known as the
//! [upwards funarg problem](https://en.wikipedia.org/wiki/Funarg_problem#Upwards_funarg_problem).
//!
//! The situation is worse in theorem provers, where environments are frequently updated. A common
//! solution is to separate the *top-level* context from the *local* context, the former being
//! represented as a hash map or array for fast indexing, while the latter being linked lists.
//! However, dividing the context into two levels is not as flexible and leads to code duplication.
//!
//! As a simple but general solution, we use linked lists but store an array of definitions in each
//! node, so that pushing work on arrays whenever possible, and new nodes are created only when
//! strictly necessary (i.e. when branching occurs). Moreover, to reduce the chance of branching,
//! entries at the end of the array are dropped when they are no longer referenced.

use std::cell::RefCell;
use std::rc::Rc;

use super::*;

#[derive(Debug)]
struct Entry<'a> {
  value: Val<'a>,
  rc: usize,
}

#[derive(Debug)]
pub struct Frame<'a> {
  prev: Option<Stack<'a>>,
  entries: RefCell<Vec<Entry<'a>>>,
}

#[derive(Debug)]
pub struct Stack<'a> {
  frame: Rc<Frame<'a>>,
  position: usize,
}

impl Default for Stack<'_> {
  fn default() -> Self {
    Self::new()
  }
}

impl<'a> Stack<'a> {
  pub fn new() -> Self {
    let entries = Vec::new();
    let frame = Rc::new(Frame { prev: None, entries: RefCell::new(entries) });
    Self { frame, position: 0 }
  }

  pub fn is_empty(&self) -> bool {
    self.position == 0 && self.frame.prev.is_none()
  }

  pub fn len(&self) -> usize {
    let mut curr = Some(self);
    let mut len = 0;
    while let Some(stack) = curr {
      len += stack.position;
      curr = stack.frame.prev.as_ref();
    }
    len
  }

  pub fn get(&self, index: usize) -> Option<Val<'a>> {
    let mut curr = Some(self);
    let mut index = index;
    while let Some(stack) = curr {
      if index < stack.position {
        let entries = stack.frame.entries.borrow();
        return Some(entries[stack.position - 1 - index].value.clone());
      }
      index -= stack.position;
      curr = stack.frame.prev.as_ref();
    }
    None
  }

  pub fn truncate(&self, amount: usize) -> Option<Self> {
    let mut curr = Some(self);
    let mut remaining = amount;
    while let Some(stack) = curr {
      if remaining < stack.position {
        let mut entries = stack.frame.entries.borrow_mut();
        entries[stack.position - 1 - remaining].rc += 1;
        return Some(Self { frame: stack.frame.clone(), position: stack.position - remaining });
      }
      remaining -= stack.position;
      curr = stack.frame.prev.as_ref();
    }
    if remaining == 0 {
      return Some(Self::new());
    }
    None
  }

  pub fn extend(&self, value: Val<'a>) -> Self {
    // If the current pointer is at the end of a frame, we can append to it.
    // Otherwise, we need to branch off and create a new frame.
    let mut entries = self.frame.entries.borrow_mut();
    if entries.len() == self.position {
      entries.push(Entry { value, rc: 1 });
      Self { frame: self.frame.clone(), position: self.position + 1 }
    } else {
      std::mem::drop(entries);
      let entries = Vec::from([Entry { value, rc: 1 }]);
      let frame = Rc::new(Frame { prev: Some(self.clone()), entries: RefCell::new(entries) });
      Self { frame, position: 1 }
    }
  }
}

impl Clone for Stack<'_> {
  fn clone(&self) -> Self {
    if self.position > 0 {
      let mut entries = self.frame.entries.borrow_mut();
      entries[self.position - 1].rc += 1;
    }
    Self { frame: self.frame.clone(), position: self.position }
  }
}

#[allow(clippy::needless_lifetimes)]
unsafe impl<#[may_dangle] 'a> Drop for Stack<'a> {
  fn drop(&mut self) {
    if self.position > 0 {
      let mut entries = self.frame.entries.borrow_mut();
      entries[self.position - 1].rc -= 1;
      while entries.last().is_some_and(|entry| entry.rc == 0) {
        entries.pop();
      }
    }
  }
}
