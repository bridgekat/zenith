-- ========================
-- Notations for meta-logic
-- ========================

-- TODO: update syntax.

letrec context_names' = fun (n) =>
  if n == 0 then `()
  else [match (context_get [n - 1]) with (name _) => (cons name (context_names' [n - 1]))]
in (define context_names [fun () => (context_names' (context_size))])

letrec context_fprint' = fun (n) =>
  if n == (context_size) then `()
  else [begin
    [match (context_get n) with (name e) => (display [(print name) .++ ": " .++ (expr_fprint e)])];
    (context_fprint' [n + 1])
  ]
in (define context_fprint [fun () => (context_fprint' 0)])

(add_pattern [_ <op_left_brace>  ::= (word "{")])
(add_pattern [_ <op_right_brace> ::= (word "}")])
(add_pattern [_ <op_backslash>   ::= (word "\\")])
(add_pattern [_ <op_question_b>  ::= (word "?b")])
(add_pattern [_ <op_question_f>  ::= (word "?f")])
(add_pattern [_ <op_question_m>  ::= (word "?m")])

// TODO: make a helper function for this...
(add_pattern  [_            <kw_prop>   ::= (word "Prop")])
(add_rule     [prop_tree'   <tree>      ::= <kw_prop>])
(define_macro  prop_tree'   [fun (_) => (string_symbol "Prop")])
(add_pattern  [_            <kw_type>   ::= (word "Type")])
(add_rule     [type_tree'   <tree>      ::= <kw_type>])
(define_macro  type_tree'   [fun (_) => (string_symbol "Type")])
(add_pattern  [_            <kw_kind>   ::= (word "Kind")])
(add_rule     [kind_tree'   <tree>      ::= <kw_kind>])
(define_macro  kind_tree'   [fun (_) => (string_symbol "Kind")])

(add_rule [_ <sym_lambda> ::= <op_backslash>])
(add_rule [_ <sym_lambda> ::= <kw_fun>])

(add_rule [tree'       <logic_expr 100> ::= <op_left_paren> <logic_expr 0> <op_right_paren>])
(add_rule [prop'       <logic_expr 100> ::= <kw_prop>])
(add_rule [type'       <logic_expr 100> ::= <kw_type>])
(add_rule [kind'       <logic_expr 100> ::= <kw_kind>])
(add_rule [free_var'   <logic_expr 100> ::= <op_question_f> <nat64>])
(add_rule [bound_var'  <logic_expr 100> ::= <op_question_b> <nat64>])
(add_rule [meta_var'   <logic_expr 100> ::= <op_question_m> <nat64>])
(add_rule [named_var'  <logic_expr 100> ::= <symbol>])
(add_rule [app'        <logic_expr 99>  ::= <logic_expr 99> <logic_expr 100>])
(add_rule [lam'        <logic_expr 50>  ::= <sym_lambda> <symbol> <op_colon> <logic_expr 0> <op_double_right_arrow> <logic_expr 0>])
(add_rule [pi'         <logic_expr 50>  ::= <op_left_paren> <symbol> <op_colon> <logic_expr 0> <op_right_paren> <op_right_arrow> <logic_expr 0>])
(add_rule [logic_expr' <tree>           ::= <op_left_brace> <logic_expr 0> <op_right_brace>])

letrec lookup' = fun (key ls acc) => [
  match ls with
  ()       => `()
  (x . xs) => if (symbol_eq key x) then acc else (lookup' key xs [acc + 1])
] in (define lookup [fun (key ls) => (lookup' key ls 0)])

letrec resolve_names' = fun (x stk) => [
  match x with
  (`Sort _)       => x
  (`Var `Free _)  => x
  (`Var `Bound _) => x
  (`Var `Meta _)  => x
  (`Var `Named s) => [
    match (lookup s stk) with
    () => [
      match (lookup s (context_names)) with
      () => `(Var Unknown) // Unknown variable!
      id => `(Var Free ,[(context_size) - 1 - id])
    ]
    id => `(Var Bound ,id)
  ]
  (`App l r)      => `(App ,(resolve_names' l stk) ,(resolve_names' r stk))
  (`Lam s t r)    => `(Lam ,s ,(resolve_names' t stk) ,(resolve_names' r (cons s stk)))
  (`Pi s t r)     => `(Pi ,s ,(resolve_names' t stk) ,(resolve_names' r (cons s stk)))
] in (define resolve_names [fun (x) => (resolve_names' x `())])

(define_macro prop'       [fun (_) => `(Sort Prop)])
(define_macro type'       [fun (_) => `(Sort Type)])
(define_macro kind'       [fun (_) => `(Sort Kind)])
(define_macro free_var'   [fun (_ id) => `(Var Free  ,id)])
(define_macro bound_var'  [fun (_ id) => `(Var Bound ,id)])
(define_macro meta_var'   [fun (_ id) => `(Var Meta  ,id)])
(define_macro named_var'  [fun (name) => `(Var Named ,name)])
(define_macro app'        [fun (l r) => `(App ,l ,r)])
(define_macro lam'        [fun (_ name _ t _ r) => `(Lam ,name ,t ,r)])
(define_macro pi'         [fun (_ name _ t _ _ r) => `(Pi ,name ,t ,r)])
(define_macro logic_expr' [fun (_ x _) => (resolve_names x)]) // TEMP CODE

// ===============================
// Notations for first-order logic
// ===============================

(add_pattern [_ <op_tilde>        ::= (word "~")])
(add_pattern [_ <op_wedge>        ::= (word "/\\")])
(add_pattern [_ <op_vee>          ::= (word "\\/")])
(add_pattern [_ <op_colon_equals> ::= (word ":=")])
(add_pattern [_ <op_double_colon> ::= (word "::")])

(add_pattern [_ <kw_not>     ::= (word "not")])
(add_pattern [_ <kw_and>     ::= (word "and")])
(add_pattern [_ <kw_or>      ::= (word "or")])
(add_pattern [_ <kw_implies> ::= (word "implies")])
(add_pattern [_ <kw_iff>     ::= (word "iff")])
(add_pattern [_ <kw_forall>  ::= (word "forall")])
(add_pattern [_ <kw_exists>  ::= (word "exists")])
(add_pattern [_ <kw_unique>  ::= (word "unique")])

(add_rule [_ <sym_not>     ::= <op_tilde>])
(add_rule [_ <sym_not>     ::= <op_bang>])
(add_rule [_ <sym_not>     ::= <kw_not>])
(add_rule [_ <sym_and>     ::= <op_wedge>])
(add_rule [_ <sym_and>     ::= <kw_and>])
(add_rule [_ <sym_or>      ::= <op_vee>])
(add_rule [_ <sym_or>      ::= <kw_or>])
(add_rule [_ <sym_implies> ::= <op_right_arrow>])
(add_rule [_ <sym_implies> ::= <kw_implies>])
(add_rule [_ <sym_iff>     ::= <op_left_right_arrow>])
(add_rule [_ <sym_iff>     ::= <kw_iff>])
(add_rule [_ <sym_forall>  ::= <kw_forall>])
(add_rule [_ <sym_exists>  ::= <kw_exists>])
(add_rule [_ <sym_unique>  ::= <kw_unique>])

(add_rule [equals'  <logic_expr 90> ::= <logic_expr 91> <op_equals> <logic_expr 91>])
(add_rule [not'     <logic_expr 90> ::= <sym_not> <logic_expr 90>])
(add_rule [and'     <logic_expr 89> ::= <logic_expr 89> <sym_and>     <logic_expr 90>])
(add_rule [or'      <logic_expr 88> ::= <logic_expr 88> <sym_or>      <logic_expr 89>])
(add_rule [implies' <logic_expr 87> ::= <logic_expr 88> <sym_implies> <logic_expr 87>])
(add_rule [iff'     <logic_expr 86> ::= <logic_expr 87> <sym_iff>     <logic_expr 87>])
(add_rule [forall'  <logic_expr 50> ::= <sym_forall> <symbol> <op_comma> <logic_expr 0>])
(add_rule [exists'  <logic_expr 50> ::= <sym_exists> <symbol> <op_comma> <logic_expr 0>])
(add_rule [unique'  <logic_expr 50> ::= <sym_unique> <symbol> <op_comma> <logic_expr 0>])

(define_macro equals'  [fun (x _ y)   => `(App (App (Var Free 2) ,x) ,y)])
(define_macro not'     [fun (_ x)     => `(App (Var Free 5) ,x)])
(define_macro and'     [fun (x _ y)   => `(App (App (Var Free 6) ,x) ,y)])
(define_macro or'      [fun (x _ y)   => `(App (App (Var Free 7) ,x) ,y)])
(define_macro implies' [fun (x _ y)   => `(App (App (Var Free 8) ,x) ,y)])
(define_macro iff'     [fun (x _ y)   => `(App (App (Var Free 9) ,x) ,y)])
(define_macro forall'  [fun (_ s _ r) => `(App (Var Free 10) (Lam ,s (Var Free 0) ,r))])
(define_macro exists'  [fun (_ s _ r) => `(App (Var Free 11) (Lam ,s (Var Free 0) ,r))])
(define_macro unique'  [fun (_ s _ r) => `(App (Var Free 12) (Lam ,s (Var Free 0) ,r))])

/*
(define e (tree_expr (forall "x" (exists "y" (equals (bv 1) (bv 0))))))
e
(display (expr_print e))
(display (expr_fprint e))
(display (expr_print (expr_check e)))
(expr_tree (expr_check e))
*/

// And left
(context_push `(ax_1 ,(tree_expr `{ (P: Prop) -> (Q: Prop) -> P /\ Q -> P })))
(display (expr_fprint (expr_check (tree_expr `{ ax_1 (forall x, x = x) (forall y, y = y) }))))

