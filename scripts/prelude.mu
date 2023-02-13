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
