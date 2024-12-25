// use std::cmp::max;

// /// Universes.
// #[derive(Debug, Clone, Copy, PartialEq, Eq)]
// pub struct Sort(pub usize);

// impl Sort {
//   /// Universe formation rule.
//   pub fn univ_rule(u: Sort) -> Option<Sort> {
//     let Sort(u) = u;
//     match u < 2 {
//       true => Some(Sort(u + 1)),
//       _ => None,
//     }
//   }

//   /// Function type formation rule.
//   pub fn pi_rule(u: Sort, v: Sort) -> Option<Sort> {
//     let (Sort(u), Sort(v)) = (u, v);
//     match v == 0 {
//       true => Some(Sort(0)),
//       _ => Some(Sort(max(u, v))),
//     }
//   }
// }
