//! # Linked zipper stacks
//!
//! In many functional programming language interpreters, evaluation environments are represented
//! as linked lists of closures. This becomes infeasible when the environment grows large, as
//! indexing into a linked list is O(n). On the other hand, environments should support fast
//! pushing, popping and cloning (for the creation of closures), and arrays cannot be cloned
//! efficiently. This tension is known as the "upwards funarg problem".
//!
//! The situation is worse in theorem provers, where environments are frequently updated. A common
//! solution is to separate the *top-level* context from the *local* context, the former being
//! represented as a hash map or array for fast indexing, while the latter being linked lists.
//! However, dividing the context into two levels is not as flexible and leads to code duplication.
//! Here we refine the idea of linked closures, so that pushing and popping work on arrays, and
//! linked list nodes are created only when necessary.
//!
//! ## Data structure
//!
//! The evaluation environment is a persistent stack, which is simply a tree. We divide the tree
//! into paths (contiguous sets of nodes), each represented as an array. Each path can either go
//! upwards (to the root) or downwards (away from the root), and has a parent pointer that points
//! to some position in the path directly above it. Downward paths also have mutable child pointers
//! at every position.
//!
//! ## Invariants
//!
//! - The parent of each downward path must be an upward path.
//! - All children of each downward path must be upward paths.

use std::rc::Rc;

/// Reference implementation using linked lists.
#[derive(Debug, Clone)]
pub struct ListStack<T: Clone> {
  head: Option<Rc<ListNode<T>>>,
}

#[derive(Debug, Clone)]
struct ListNode<T: Clone> {
  elem: T,
  next: Option<Rc<ListNode<T>>>,
}

impl<T: Clone> Default for ListStack<T> {
  fn default() -> Self {
    Self::new()
  }
}

impl<T: Clone> ListStack<T> {
  pub fn new() -> Self {
    ListStack { head: None }
  }

  pub fn is_empty(&self) -> bool {
    self.head.is_none()
  }

  pub fn len(&self) -> usize {
    let mut len = 0;
    let mut head = &self.head;
    while let Some(node) = head {
      len += 1;
      head = &node.next;
    }
    len
  }

  pub fn get(&self, index: usize) -> Option<T> {
    let mut index = index;
    let mut head = &self.head;
    while let Some(node) = head {
      if index == 0 {
        return Some(node.elem.clone());
      }
      index -= 1;
      head = &node.next;
    }
    None
  }

  pub fn extend(&self, elem: T) -> ListStack<T> {
    ListStack { head: Some(Rc::new(ListNode { elem, next: self.head.clone() })) }
  }
}

// struct Up<T> {
//   data: Vec<T>,
// }

// struct Down<T> {
//   data: Vec<(T, Option<Rc<RefCell<Up<T>>>>)>,
// }

pub struct TreeStack {}
