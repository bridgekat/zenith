// =====================================
// Enhanced syntax for the base language
// =====================================

// Lexical patterns
(define patterns `(

  // Blank, line comment and block comment
  (_ (star (char " \f\n\r\t\v")))
  (_ (concat (word "--") (star (except "\n\r"))))
  (_ (concat (word "/-")
             (star (concat (star (except "-"))
                           (plus (char "-"))
                           (except "/")))
             (star (except "-"))
             (plus (char "-"))
             (char "/")))

  // Identifiers
  (tok_symbol
    (concat (alt (range 97 122) (range 65 90) (char "_.'") (utf8seg))
            (star (alt (range 97 122) (range 65 90) (range 48 57) (char "_.'") (utf8seg)))))

  // Non-negative integers
  (tok_nat64
    (alt (plus (range 48 57))
         (concat (char "0")
                 (char "xX")
                 (plus (alt (range 48 57) (range 97 102) (range 65 70))))))

  // Strings
  (tok_string
    (concat (char "\"")
            (star (alt (except "\\\"")
                      (concat (char "\\") (char "\\\"abfnrtv"))))
            (char "\"")))

  // Operators and keywords
  (op_left_paren (word "("))
  (op_right_paren (word ")"))
  (op_left_bracket (word "["))
  (op_right_bracket (word "]"))
  (op_period (word "."))
  (op_quote (word "`"))
  (op_comma (word ","))
  (op_colon (word ":"))
  (op_semicolon (word ";"))

  (op_double_colon_equals (word "::="))
  (op_plus (word "+"))
  (op_minus (word "-"))
  (op_asterisk (word "*"))
  (op_slash (word "/"))
  (op_amp (word "&"))
  (op_bar (word "|"))
  (op_caret (word "^"))
  (op_less_equals (word "<="))
  (op_less (word "<"))
  (op_greater_equals (word ">="))
  (op_greater (word ">"))
  (op_equals (word "="))
  (op_double_equals (word "=="))
  (op_bang_equals (word "!="))
  (op_bang (word "!"))
  (op_amp_amp (word "&&"))
  (op_bar_bar (word "||"))
  (op_left_arrow (word "<-"))
  (op_right_arrow (word "->"))
  (op_left_right_arrow (word "<->"))
  (op_double_right_arrow (word "=>"))
  (op_double_left_right_arrow (word "<=>"))

  (kw_let (word "let"))
  (kw_letrec (word "letrec"))
  (kw_in (word "in"))
  (kw_fun (word "fun"))
  (kw_if (word "if"))
  (kw_then (word "then"))
  (kw_else (word "else"))
  (kw_match (word "match"))
  (kw_with (word "with"))
  (kw_begin (word "begin"))
  (kw_end (word "end"))

))

// Grammar rules
(define rules `(

  // Basic part
  (symbol' (symbol 0) ((tok_symbol 0)))
  (nat64' (nat64 0) ((tok_nat64 0)))
  (string' (string 0) ((tok_string 0)))
  (id' (tree 0) ((symbol 0)))
  (id' (tree 0) ((nat64 0)))
  (id' (tree 0) ((string 0)))
  (nil' (list 0) ())
  (cons' (list 0) ((tree 0) (list 0)))
  (period' (list 0) ((tree 0) (op_period 0) (tree 0)))
  (quote' (tree 0) ((op_quote 0) (tree 0)))
  (unquote' (tree 0) ((op_comma 0) (tree 0)))
  (tree' (tree 0) ((op_left_bracket 0) (list 0) (op_right_bracket 0)))

  // Extended part
  // A more natural way (with less parentheses) to write expressions
  (list_init' (expr_list 0) ((expr 100) (expr 100)))
  (list_cons' (expr_list 0) ((expr 100) (expr_list 0)))
  (id' (expr 99) ((expr_list 0)))
  (minus' (expr 90) ((op_minus 0) (expr 90)))
  (mul' (expr 80) ((expr 80) (op_asterisk 0) (expr 81)))
  (div' (expr 80) ((expr 80) (op_slash 0) (expr 81)))
  (add' (expr 70) ((expr 70) (op_plus 0) (expr 71)))
  (sub' (expr 70) ((expr 70) (op_minus 0) (expr 71)))
  (le' (expr 40) ((expr 41) (op_less_equals 0) (expr 41)))
  (lt' (expr 40) ((expr 41) (op_less 0) (expr 41)))
  (ge' (expr 40) ((expr 41) (op_greater_equals 0) (expr 41)))
  (gt' (expr 40) ((expr 41) (op_greater 0) (expr 41)))
  (eq' (expr 40) ((expr 41) (op_double_equals 0) (expr 41)))
  (neq' (expr 40) ((expr 41) (op_bang_equals 0) (expr 41)))
  (not' (expr 40) ((op_bang 0) (expr 40)))
  (and' (expr 43) ((expr 43) (op_amp_amp 0) (expr 44)))
  (or' (expr 42) ((expr 42) (op_bar_bar 0) (expr 43)))
  (implies' (expr 41) ((expr 41) (op_right_arrow 0) (expr 42)))
  (iff' (expr 40) ((expr 40) (op_left_right_arrow 0) (expr 41)))

  (_ (opt_semicolon 0) ())
  (_ (opt_semicolon 0) ((op_semicolon 0)))

  (binding' (binding 0) ((symbol 0) (op_equals 0) (expr 0)))
  (single' (bindings 0) ((binding 0)))
  (period' (bindings 0) ((binding 0) (op_semicolon 0) (bindings 0)))
  (let' (expr 0) ((kw_let 0) (bindings 0) (opt_semicolon 0) (kw_in 0) (expr 0)))
  (letrec' (expr 0) ((kw_letrec 0) (bindings 0) (opt_semicolon 0) (kw_in 0) (expr 0)))
  (fun' (expr 0) ((kw_fun 0) (expr 100) (op_double_right_arrow 0) (expr 0)))
  (if' (expr 0) ((kw_if 0) (expr 1) (kw_then 0) (expr 1) (kw_else 0) (expr 0)))
  (clause' (clause 0) ((expr 100) (op_double_right_arrow 0) (expr 0)))
  (single' (clauses 0) ((clause 0)))
  (period' (clauses 0) ((clause 0) (op_bar 0) (clauses 0)))
  (match' (expr 0) ((kw_match 0) (expr 1) (kw_with 0) (op_bar 0) (clauses 0) (kw_end 0)))
  (match1' (expr 0) ((kw_match 0) (expr 1) (kw_with 0) (clause 0)))
  (single' (begin 0) ((expr 0)))
  (period' (begin 0) ((expr 0) (op_semicolon 0) (begin 0)))
  (set' (expr 0) ((symbol 0) (op_equals 0) (expr 0)))
  (begin' (expr 0) ((kw_begin 0) (begin 0) (opt_semicolon 0) (kw_end 0)))

  (id' (expr 100) ((tree 0)))
  (tree' (tree 0) ((op_left_paren 0) (expr 0) (op_right_paren 0)))
  (stmt' (_ 0) ((expr 0) (op_semicolon 0)))

))

// Syntax expansion macros
(define_macro list_init' (lambda (l r) (list l r)))
(define_macro list_cons' (lambda (l r) (cons l r)))
(define_macro minus' (lambda (_ x) `(minus ,x)))
(define_macro add' (lambda (l _ r) `(add ,l ,r)))
(define_macro sub' (lambda (l _ r) `(sub ,l ,r)))
(define_macro mul' (lambda (l _ r) `(mul ,l ,r)))
(define_macro div' (lambda (l _ r) `(div ,l ,r)))
(define_macro le' (lambda (l _ r) `(le ,l ,r)))
(define_macro lt' (lambda (l _ r) `(lt ,l ,r)))
(define_macro ge' (lambda (l _ r) `(ge ,l ,r)))
(define_macro gt' (lambda (l _ r) `(gt ,l ,r)))
(define_macro eq' (lambda (l _ r) `(eq ,l ,r)))
(define_macro neq' (lambda (l _ r) `(neq ,l ,r)))
(define_macro not' (lambda (_ x) `(not ,x)))
(define_macro and' (lambda (l _ r) `(and ,l ,r)))
(define_macro or' (lambda (l _ r) `(or ,l ,r)))
(define_macro implies' (lambda (l _ r) `(implies ,l ,r)))
(define_macro iff' (lambda (l _ r) `(iff ,l ,r)))
(define_macro single' (lambda (l) (list l)))
(define_macro binding' (lambda (sym _ val) `(,sym ,val)))
(define_macro let' (lambda (_ bindings _ _ body) `(let ,bindings ,body)))
(define_macro letrec' (lambda (_ bindings _ _ body) `(letrec ,bindings ,body)))
(define_macro fun' (lambda (_ arg _ body) `(lambda ,arg ,body)))
(define_macro if' (lambda (_ c _ t _ f) `(cond ,c ,t ,f)))
(define_macro clause' (lambda (pat _ val) `(,pat ,val)))
(define_macro match' (lambda (_ e _ _ clauses _) `(match ,e ,clauses)))
(define_macro match1' (lambda (_ e _ clause) `(match ,e (,clause))))
(define_macro set' (lambda (s _ e) `(set ,s ,e)))
(define_macro begin' (lambda (_ x _ _) (cons `begin x)))
(define_macro stmt' (lambda (s _) s))

// Update syntax
(set_syntax patterns rules) -- After this right parenthesis, we can write everything in the enhanced syntax!

-- ============================
-- Syntax definition facilities
-- ============================

letrec
  staging_patterns = `[];
  staging_rules = `[];

  concat = fun [l r] =>
    match l with
    | []       => r
    | [x . xs] => cons x (concat xs r)
    end;

  declare_pattern = fun [pattern] =>
    set staging_patterns (concat staging_patterns (list pattern));

  declare_rule = fun [rule] =>
    set staging_rules (concat staging_rules (list rule));

  split_rule_rhs = fun [syncats n] =>
    match syncats with
    | []       => list `[] `[] `[]
    | [x . xs] => match split_rule_rhs xs (n + 1) with [rhs arg_list body] =>
      match x with
      | [x]        => list (cons x rhs) (cons `_ arg_list) body
      | [sym prec] => let var_sym = string_symbol (string_concat "_" (print n)) in list (cons x rhs) (cons var_sym arg_list) (cons (list `unquote var_sym) body)
      end
    end;

  declare_simple_rule = fun [[func_name lhs rhs]] =>
    let macro_name = string_symbol (string_concat "macro_generated_by_'declare_simple_rule'." (print func_name)) in
    match split_rule_rhs rhs 0 with [rhs arg_list body] =>
    begin
      set staging_rules (concat staging_rules (list (list macro_name lhs rhs)));
      eval `[define_macro ,macro_name (fun ,arg_list => `,[cons func_name body])];
    end;

  update_syntax = fun [] => match [get_syntax] with [patterns rules] =>
    begin
      set_syntax (concat patterns staging_patterns) (concat rules staging_rules);
      display (string_concat "Added patterns: " (print staging_patterns));
      display (string_concat "Added rules: " (print staging_rules));
      set staging_patterns `[];
      set staging_rules `[];
    end;

in begin
  define declare_pattern declare_pattern;
  define declare_rule declare_rule;
  define declare_simple_rule declare_simple_rule;
  define update_syntax update_syntax;
end;

declare_pattern `[kw_declare_pattern [word "declare_pattern"]];
declare_pattern `[kw_declare_rule [word "declare_rule"]];
declare_pattern `[kw_declare_simple_rule [word "declare_simple_rule"]];

declare_rule `[syncat_default' [syncat 0] [[op_less 0] [symbol 0] [op_greater 0]]];
declare_rule `[syncat_prec' [syncat 0] [[op_less 0] [symbol 0] [nat64 0] [op_greater 0]]];
declare_rule `[syncat_ignored' [syncat 0] [[syncat 0] [op_asterisk 0]]]; -- For use with `declare_simple_rule` only
declare_rule `[nil' [syncats 0] []];
declare_rule `[cons' [syncats 0] [[syncat 0] [syncats 0]]];
declare_rule `[pattern' [syntax_pattern 0] [[op_less 0] [symbol 0] [op_greater 0] [op_double_colon_equals 0] [tree 0]]];
declare_rule `[rule' [syntax_rule 0] [[symbol 0] [syncat 0] [op_double_colon_equals 0] [syncats 0]]];
declare_rule `[declare_pattern' [tree 0] [[kw_declare_pattern 0] [syntax_pattern 0]]];
declare_rule `[declare_rule' [tree 0] [[kw_declare_rule 0] [syntax_rule 0]]];
declare_rule `[declare_simple_rule' [tree 0] [[kw_declare_simple_rule 0] [syntax_rule 0]]];

define_macro syncat_default'      [lambda [_ x _] `[,x 0]];
define_macro syncat_prec'         [lambda [_ l r _] `[,l ,r]];
define_macro syncat_ignored'      [lambda [x _] `[,x]];
define_macro pattern'             [lambda [_ l _ _ r] ``[,l ,r]];
define_macro rule'                [lambda [m l _ r] ``[,m ,l ,r]];
define_macro declare_pattern'     [lambda [_ x] `[declare_pattern ,x]];
define_macro declare_rule'        [lambda [_ x] `[declare_rule ,x]];
define_macro declare_simple_rule' [lambda [_ x] `[declare_simple_rule ,x]];

[update_syntax];

-- =================
-- Utility functions
-- =================

define symbol_eq (fun [a b] => string_eq (print a) (print b));
define max (fun [a b] => if a >= b then a else b);
define concat (fun [l r] =>
  match l with
  | []       => r
  | [x . xs] => cons x (concat xs r)
  end);

declare_pattern                   <op_double_plus>        ::= [word "++"];
declare_pattern                   <op_period_double_plus> ::= [word ".++"];
declare_simple_rule concat        <expr 70>               ::= <expr 71> <op_double_plus>* <expr 70>;
declare_simple_rule string_concat <expr 70>               ::= <expr 71> <op_period_double_plus>* <expr 70>;

[update_syntax];

-- ========================
-- Notations for meta-logic
-- ========================

letrec
  context_names' = fun [n] =>
    if n == 0 then `[]
    else match context_get (n - 1) with [name _] => cons name (context_names' (n - 1));

  context_names = fun [] =>
    context_names' [context_size];

  context_fprint' = fun [n] =>
    if n == [context_size] then `[]
    else begin
      match context_get n with [name e] => display (print name .++ ": " .++ expr_fprint e);
      context_fprint' (n + 1);
    end;

  context_fprint = fun [] =>
    context_fprint' 0;

  lookup' = fun [key ls acc] =>
    match ls with
    | []       => `[]
    | [x . xs] => if symbol_eq key x then acc else lookup' key xs (acc + 1)
    end;

  lookup = fun [key ls] =>
    lookup' key ls 0;

  resolve_names' = fun [x stk] =>
    match x with
    | [`Sort _]       => x
    | [`Var `Free _]  => x
    | [`Var `Bound _] => x
    | [`Var `Meta _]  => x
    | [`Var `Named s] =>
      match [lookup s stk] with
      | [] =>
        match [lookup s [context_names]] with
        | [] => `[Var Unknown] -- Unknown variable!
        | id => `[Var Free ,([context_size] - 1 - id)]
        end
      | id => `[Var Bound ,id]
      end
    | [`App l r]      => `[App ,[resolve_names' l stk] ,[resolve_names' r stk]]
    | [`Lam s t r]    => `[Lam ,s ,[resolve_names' t stk] ,[resolve_names' r [cons s stk]]]
    | [`Pi s t r]     => `[Pi ,s ,[resolve_names' t stk] ,[resolve_names' r [cons s stk]]]
    end;

  resolve_names = fun [x] =>
    resolve_names' x `[];

in begin
  define context_names context_names;
  define context_fprint context_fprint;
  define lookup lookup;
  define resolve_names resolve_names;
end;

declare_pattern           <op_left_brace>   ::= [word "{"];
declare_pattern           <op_right_brace>  ::= [word "}"];
declare_pattern           <op_backslash>    ::= [word "\\"];
declare_pattern           <op_question_b>   ::= [word "?b"];
declare_pattern           <op_question_f>   ::= [word "?f"];
declare_pattern           <op_question_m>   ::= [word "?m"];
declare_pattern           <kw_prop>         ::= [word "Prop"];
declare_pattern           <kw_type>         ::= [word "Type"];
declare_pattern           <kw_kind>         ::= [word "Kind"];
declare_pattern           <kw_assume>       ::= [word "assume"];
declare_pattern           <kw_unassume>     ::= [word "unassume"];

declare_rule _            <sym_lambda>      ::= <kw_fun>;
declare_rule _            <sym_lambda>      ::= <op_backslash>;
declare_rule tree'        <logic_expr 100>  ::= <op_left_paren> <logic_expr 0> <op_right_paren>;
declare_rule prop'        <logic_expr 100>  ::= <kw_prop>;
declare_rule type'        <logic_expr 100>  ::= <kw_type>;
declare_rule kind'        <logic_expr 100>  ::= <kw_kind>;
declare_rule free_var'    <logic_expr 100>  ::= <op_question_f> <nat64>;
declare_rule bound_var'   <logic_expr 100>  ::= <op_question_b> <nat64>;
declare_rule meta_var'    <logic_expr 100>  ::= <op_question_m> <nat64>;
declare_rule named_var'   <logic_expr 100>  ::= <symbol>;
declare_rule app'         <logic_expr 99>   ::= <logic_expr 99> <logic_expr 100>;
declare_rule lam'         <logic_expr 10>   ::= <sym_lambda> <symbol> <op_colon> <logic_expr 0> <op_double_right_arrow> <logic_expr 10>;
declare_rule pi'          <logic_expr 10>   ::= <op_left_paren> <symbol> <op_colon> <logic_expr 0> <op_right_paren> <op_right_arrow> <logic_expr 10>;
declare_rule logic_expr'  <expr 100>        ::= <op_left_brace> <logic_expr 0> <op_right_brace>;
declare_rule assume'      <expr 0>          ::= <kw_assume> <symbol> <op_colon> <logic_expr 0>;
declare_rule unassume'    <expr 0>          ::= <kw_unassume>;

define_macro prop'        (fun [_] => `[Sort Prop]);
define_macro type'        (fun [_] => `[Sort Type]);
define_macro kind'        (fun [_] => `[Sort Kind]);
define_macro free_var'    (fun [_ id] => `[Var Free  ,id]);
define_macro bound_var'   (fun [_ id] => `[Var Bound ,id]);
define_macro meta_var'    (fun [_ id] => `[Var Meta  ,id]);
define_macro named_var'   (fun [name] => `[Var Named ,name]);
define_macro app'         (fun [l r] => `[App ,l ,r]);
define_macro lam'         (fun [_ name _ t _ r] => `[Lam ,name ,t ,r]);
define_macro pi'          (fun [_ name _ t _ _ r] => `[Pi ,name ,t ,r]);
define_macro logic_expr'  (fun [_ x _] => tree_expr (resolve_names x));
define_macro assume'      (fun [_ name _ lo] => `[context_push `[,name ,(tree_expr (resolve_names lo))]]);
define_macro unassume'    (fun [_] => `[context_pop]);

-- ===============================
-- Notations for first-order logic
-- ===============================

declare_pattern                   <op_tilde>        ::= [word "~"];
declare_pattern                   <op_wedge>        ::= [word "/\\"];
declare_pattern                   <op_vee>          ::= [word "\\/"];
declare_pattern                   <op_colon_equals> ::= [word ":="];
declare_pattern                   <op_double_colon> ::= [word "::"];
declare_pattern                   <kw_setvar>       ::= [word "setvar"];
declare_pattern                   <kw_arbitrary>    ::= [word "arbitrary"];
declare_pattern                   <kw_true>         ::= [word "true"];
declare_pattern                   <kw_false>        ::= [word "false"];
declare_pattern                   <kw_not>          ::= [word "not"];
declare_pattern                   <kw_and>          ::= [word "and"];
declare_pattern                   <kw_or>           ::= [word "or"];
declare_pattern                   <kw_implies>      ::= [word "implies"];
declare_pattern                   <kw_iff>          ::= [word "iff"];
declare_pattern                   <kw_forall>       ::= [word "forall"];
declare_pattern                   <kw_exists>       ::= [word "exists"];
declare_pattern                   <kw_unique>       ::= [word "unique"];

declare_rule _                    <logic_setvar>    ::= <kw_setvar>;
declare_rule _                    <logic_arbitrary> ::= <kw_arbitrary>;
declare_rule _                    <logic_equals>    ::= <op_equals>;
declare_rule _                    <logic_true>      ::= <kw_true>;
declare_rule _                    <logic_false>     ::= <kw_false>;
declare_rule _                    <logic_not>       ::= <op_tilde>;
declare_rule _                    <logic_not>       ::= <op_bang>;
declare_rule _                    <logic_not>       ::= <kw_not>;
declare_rule _                    <logic_and>       ::= <op_wedge>;
declare_rule _                    <logic_and>       ::= <kw_and>;
declare_rule _                    <logic_or>        ::= <op_vee>;
declare_rule _                    <logic_or>        ::= <kw_or>;
declare_rule _                    <logic_implies>   ::= <op_right_arrow>;
declare_rule _                    <logic_implies>   ::= <kw_implies>;
declare_rule _                    <logic_iff>       ::= <op_left_right_arrow>;
declare_rule _                    <logic_iff>       ::= <kw_iff>;
declare_rule _                    <logic_forall>    ::= <kw_forall>;
declare_rule _                    <logic_exists>    ::= <kw_exists>;
declare_rule _                    <logic_unique>    ::= <kw_unique>;
declare_rule logic_setvar'        <logic_expr 100>  ::= <kw_setvar>;
declare_rule logic_arbitrary'     <logic_expr 100>  ::= <kw_arbitrary>;
declare_rule logic_equals'        <logic_expr 90>   ::= <logic_expr 91> <logic_equals> <logic_expr 91>;
declare_rule logic_true'          <logic_expr 90>   ::= <logic_true>;
declare_rule logic_false'         <logic_expr 90>   ::= <logic_false>;
declare_rule logic_not'           <logic_expr 90>   ::= <logic_not> <logic_expr 90>;
declare_rule logic_and'           <logic_expr 89>   ::= <logic_expr 89> <logic_and> <logic_expr 90>;
declare_rule logic_or'            <logic_expr 88>   ::= <logic_expr 88> <logic_or> <logic_expr 89>;
declare_rule logic_implies'       <logic_expr 87>   ::= <logic_expr 88> <logic_implies> <logic_expr 87>;
declare_rule logic_iff'           <logic_expr 86>   ::= <logic_expr 87> <logic_iff> <logic_expr 87>;
declare_rule logic_forall'        <logic_expr 50>   ::= <logic_forall> <symbol> <op_comma> <logic_expr 50>;
declare_rule logic_exists'        <logic_expr 50>   ::= <logic_exists> <symbol> <op_comma> <logic_expr 50>;
declare_rule logic_unique'        <logic_expr 50>   ::= <logic_unique> <symbol> <op_comma> <logic_expr 50>;

define_macro logic_setvar'        (fun [_]       => `[Var Free 0]);
define_macro logic_arbitrary'     (fun [_]       => `[Var Free 1]);
define_macro logic_equals'        (fun [x _ y]   => `[App [App [Var Free 2] ,x] ,y]);
define_macro logic_true'          (fun [_]       => `[Var Free 3]);
define_macro logic_false'         (fun [_]       => `[Var Free 4]);
define_macro logic_not'           (fun [_ x]     => `[App [Var Free 5] ,x]);
define_macro logic_and'           (fun [x _ y]   => `[App [App [Var Free 6] ,x] ,y]);
define_macro logic_or'            (fun [x _ y]   => `[App [App [Var Free 7] ,x] ,y]);
define_macro logic_implies'       (fun [x _ y]   => `[App [App [Var Free 8] ,x] ,y]);
define_macro logic_iff'           (fun [x _ y]   => `[App [App [Var Free 9] ,x] ,y]);
define_macro logic_forall'        (fun [_ s _ r] => `[App [Var Free 10] [Lam ,s [Var Free 0] ,r]]);
define_macro logic_exists'        (fun [_ s _ r] => `[App [Var Free 11] [Lam ,s [Var Free 0] ,r]]);
define_macro logic_unique'        (fun [_ s _ r] => `[App [Var Free 12] [Lam ,s [Var Free 0] ,r]]);

[update_syntax];

-- ===========================
-- Axioms of first-order logic
-- ===========================

assume and.i: (P: Prop) -> (Q: Prop) -> (hp: P) -> (hq: Q) -> P /\ Q;
assume and.l: (P: Prop) -> (Q: Prop) -> (h: P /\ Q) -> P;
assume and.r: (P: Prop) -> (Q: Prop) -> (h: P /\ Q) -> Q;
assume or.l: (P: Prop) -> (Q: Prop) -> (hp: P) -> P \/ Q;
assume or.r: (P: Prop) -> (Q: Prop) -> (hq: Q) -> P \/ Q;
assume or.e: (P: Prop) -> (Q: Prop) -> (R: Prop) -> (h: P \/ Q) -> (hpr: (hp: P) -> R) -> (hqr: (hq: Q) -> R) -> R;
assume implies.i: (P: Prop) -> (Q: Prop) -> (h: (hp: P) -> Q) -> P -> Q;
assume implies.e: (P: Prop) -> (Q: Prop) -> (h: P -> Q) -> (hp: P) -> Q;
assume not.i: (P: Prop) -> (h: (hp: P) -> false) -> ~P;
assume not.e: (P: Prop) -> (hnp: ~P) -> (hp: P) -> false;
assume iff.i: (P: Prop) -> (Q: Prop) -> (hpq: (hp: P) -> Q) -> (hqp: (hq: Q) -> P) -> (P <-> Q);
assume iff.l: (P: Prop) -> (Q: Prop) -> (h: P <-> Q) -> (hp: P) -> Q;
assume iff.r: (P: Prop) -> (Q: Prop) -> (h: P <-> Q) -> (hq: Q) -> P;
assume true.i: true;
assume false.e: (P: Prop) -> (h: false) -> P;
assume raa: (P: Prop) -> (h: (hnp: ~P) -> false) -> P;
assume eq.i: (t: setvar) -> t = t;
assume eq.e: (P: (x: setvar) -> Prop) -> (a: setvar) -> (b: setvar) -> (heq: a = b) -> (hpa: P a) -> P b;
assume forall.i: (P: (_: setvar) -> Prop) -> (h: (x: setvar) -> P x) -> forall x, P x;
assume forall.e: (P: (_: setvar) -> Prop) -> (h: forall x, P x) -> (x: setvar) -> P x;
assume exists.i: (P: (_: setvar) -> Prop) -> (t: setvar) -> (h: P t) -> exists x, P x;
assume exists.e: (P: (_: setvar) -> Prop) -> (Q: Prop) -> (h: exists x, P x) -> (hq: (hp: (x: setvar) -> P x) -> Q) -> Q;
assume unique.i: (P: (_: setvar) -> Prop) -> (hl: exists x, P x) -> (hr: (x: setvar) -> (hx: P x) -> (y: setvar) -> (hy: P y) -> x = y) -> unique x, P x;
assume unique.l: (P: (_: setvar) -> Prop) -> (h: unique x, P x) -> exists x, P x;
assume unique.r: (P: (_: setvar) -> Prop) -> (h: unique x, P x) -> (x: setvar) -> (hx: P x) -> (y: setvar) -> (hy: P y) -> x = y;

-- =====================================
-- Axioms of Zermelo-Fraenkel set theory
-- =====================================

assume mem: (x: setvar) -> (s: setvar) -> Prop;
declare_rule mem' <logic_expr 90> ::= <logic_expr 91> <kw_in> <logic_expr 91>;
define_macro mem' (fun [l _ r] => `[App [App [Var Named mem] ,l] ,r]);
[update_syntax];

assume set_ext: forall x, forall y, (forall a, a in x <-> a in y) -> x = y;
assume set_regular: forall x, (exists a, a in x) -> (exists y, y in x /\ ~(exists a, a in x /\ a in y));
assume subset_primitive: \P: (_: setvar) -> (_: setvar) -> Prop => forall x, exists y, forall a, a in y <-> a in x /\ P x a;
assume pairset_primitive: forall x, forall y, exists z, x in z and y in z;
assume unionset_primitive: forall f, exists z, forall x, x in f -> (forall a, a in x -> a in z);
assume imageset_primitive: \P: (_: setvar) -> (_: setvar) -> setvar => forall x, exists y, forall a, a in x -> P x a in y;
-- assume inductiveset_primitive: exists x, emptyset in x and (forall a, a in x -> pairset a (singletonset a) in x);
assume powerset_primitive: forall x, exists y, forall z, (forall a, a in z -> a in x) -> z in y;

-- =====
-- Tests
-- =====

[context_fprint];

assume x: setvar;
assume y: setvar;
assume heq: x = y;
expr_fprint (expr_check { eq.e (\□: setvar => □ = x) x y heq (eq.i x) });
unassume;
unassume;
unassume;

assume x: setvar;
assume y: setvar;
assume z: setvar;
assume hxy: x = y;
assume hyz: y = z;
expr_fprint (expr_check { eq.e (\□: setvar => x = □) y z hyz hxy });
unassume;
unassume;
unassume;
unassume;
unassume;

assume lt: (a: setvar) -> (b: setvar) -> Prop;
declare_rule lt' <logic_expr 90> ::= <logic_expr 91> <op_less> <logic_expr 91>;
define_macro lt' (fun [l _ r] => `[App [App [Var Named lt] ,l] ,r]);
[update_syntax];

assume one: setvar;
assume zero: setvar;
assume zero_lt_one: zero < one;
assume something: setvar;
assume something_def: zero = something;

expr_fprint (expr_check { forall x, x = arbitrary });
expr_fprint (expr_check { eq.e (\x: setvar => x < one) zero something something_def zero_lt_one });

[context_fprint];
