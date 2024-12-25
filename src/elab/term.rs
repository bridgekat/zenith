// use super::*;

// /// One of the two central data structures of the elaborator. The other one is [`Context`].
// ///
// /// A [`Term`] is conceptually associated with a unique [`Context`], under which should it be interpreted.
// /// A [`Fun`], [`Pi`] or [`Let`] binder introduces a new layer in the associated context of the enclosed sub-term,
// /// compared with the parent term.
// ///
// ///
// #[derive(Debug, Clone, Copy)]
// pub enum Term<'a> {
//   /// Universes.
//   Univ(Sort),
//   /// Variables in de Bruijn indices.
//   Var(usize),
//   /// Type annotations.
//   Ann(&'a Term<'a>, &'a Term<'a>),
//   /// Definitions.
//   Let(&'a Term<'a>, &'a Term<'a>, BinderInfo),
//   /// Function types.
//   Pi(&'a Term<'a>, &'a Term<'a>, BinderInfo),
//   /// Function descriptions.
//   Fun(&'a Term<'a>, BinderInfo),
//   /// Function applications.
//   App(&'a Term<'a>, &'a Term<'a>),
//   /// Metavariables.
//   Meta(usize),
//   /// Source info.
//   Src(&'a Term<'a>, SourceInfo),
// }

// /// Dictionary index and implicitness of the bound variable.
// #[derive(Debug, Clone, Copy)]
// pub struct BinderInfo {
//   pub name_id: usize,
//   pub is_implicit: bool,
// }

// /// Starting and ending positions in input source code.
// #[derive(Debug, Clone, Copy)]
// pub struct SourceInfo {
//   pub begin: usize,
//   pub end: usize,
// }
