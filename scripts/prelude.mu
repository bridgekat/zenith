// =====================================
// Enhanced syntax for the base language
// =====================================

// Lexical patterns
(define patterns `(

  // Blank, line comment and block comment
  (_ (_ 0) (star (char " \f\n\r\t\v")))
  (_ (_ 0) (concat (word "//") (star (except "\n\r"))))
  (_ (_ 0)
    (concat (word "/*")
            (star (concat (star (except "*"))
                          (plus (char "*"))
                          (except "/")))
            (star (except "*"))
            (plus (char "*"))
            (char "/")))

  // Identifiers
  (symbol' (symbol 0)
    (concat (alt (range 97 122) (range 65 90) (char "_'") (utf8seg))
            (star (alt (range 97 122) (range 65 90) (range 48 57) (char "_'") (utf8seg)))))

  // Non-negative integers
  (nat64' (nat64 0)
    (alt (plus (range 48 57))
        (concat (char "0")
                (char "xX")
                (plus (alt (range 48 57) (range 97 102) (range 65 70))))))

  // Strings
  (string' (string 0)
    (concat (char "\"")
            (star (alt (except "\\\"")
                      (concat (char "\\") (char "\\\"abfnrtv"))))
            (char "\"")))

  // Operators and keywords
  (_ (op_left_paren 0) (word "("))
  (_ (op_right_paren 0) (word ")"))
  (_ (op_left_bracket 0) (word "["))
  (_ (op_right_bracket 0) (word "]"))
  (_ (op_period 0) (word "."))
  (_ (op_quote 0) (word "`"))
  (_ (op_comma 0) (word ","))
  (_ (op_colon 0) (word ":"))
  (_ (op_semicolon 0) (word ";"))

  (_ (op_double_colon_equals 0) (word "::="))
  (_ (op_plus 0) (word "+"))
  (_ (op_minus 0) (word "-"))
  (_ (op_asterisk 0) (word "*"))
  (_ (op_slash 0) (word "/"))
  (_ (op_less_equals 0) (word "<="))
  (_ (op_less 0) (word "<"))
  (_ (op_greater_equals 0) (word ">="))
  (_ (op_greater 0) (word ">"))
  (_ (op_equals 0) (word "="))
  (_ (op_double_equals 0) (word "=="))
  (_ (op_bang_equals 0) (word "!="))
  (_ (op_bang 0) (word "!"))
  (_ (op_amp_amp 0) (word "&&"))
  (_ (op_bar_bar 0) (word "||"))
  (_ (op_left_arrow 0) (word "<-"))
  (_ (op_right_arrow 0) (word "->"))
  (_ (op_left_right_arrow 0) (word "<->"))
  (_ (op_double_right_arrow 0) (word "=>"))
  (_ (op_double_left_right_arrow 0) (word "<=>"))

  (_ (kw_let 0) (word "let"))
  (_ (kw_in 0) (word "in"))
  (_ (kw_fun 0) (word "fun"))
  (_ (kw_if 0) (word "if"))
  (_ (kw_then 0) (word "then"))
  (_ (kw_else 0) (word "else"))
  (_ (kw_match 0) (word "match"))
  (_ (kw_with 0) (word "with"))
  (_ (kw_begin 0) (word "begin"))

))

// Syntax rules
(define rules `(

  // Preserve default rules
  // See: https://github.com/digama0/mm0/blob/master/mm0-hs/mm1.md#s-expressions
  (id' (tree 0) ((symbol 0)))
  (id' (tree 0) ((nat64 0)))
  (id' (tree 0) ((string 0)))
  (nil' (list 0) ())
  (cons' (list 0) ((tree 0) (list 0)))
  (period' (list 0) ((tree 0) (op_period 0) (tree 0)))
  (quote' (tree 0) ((op_quote 0) (tree 0)))
  (unquote' (tree 0) ((op_comma 0) (tree 0)))
  (tree' (tree 0) ((op_left_paren 0) (list 0) (op_right_paren 0)))

  // Extended part
  // A more natural way (with less parentheses) to write BNF grammars
  (syncat_default' (syncat 0) ((op_less 0) (symbol 0) (op_greater 0)))
  (syncat_prec' (syncat 0) ((op_less 0) (symbol 0) (nat64 0) (op_greater 0)))
  (syncat_ignored' (syncat 0) ((syncat 0) (op_asterisk 0))) // For use with `add_rule_auto` only
  (nil' (syncats 0) ())
  (cons' (syncats 0) ((syncat 0) (syncats 0)))
  (pattern' (tree 0) ((op_left_bracket 0) (symbol 0) (syncat 0) (op_double_colon_equals 0) (tree 0) (op_right_bracket 0)))
  (rule' (tree 0) ((op_left_bracket 0) (symbol 0) (syncat 0) (op_double_colon_equals 0) (syncats 0) (op_right_bracket 0)))

  // A more natural way (with less parentheses) to write expressions
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
  (nil' (bindings 0) ())
  (period' (bindings 0) ((binding 0) (opt_semicolon 0) (bindings 0)))
  (let' (expr 0) ((kw_let 0) (bindings 0) (kw_in 0) (expr 0))) // Possibly ambiguous
  (fun' (expr 0) ((kw_fun 0) (expr 100) (op_double_right_arrow 0) (expr 0)))
  (if' (expr 0) ((kw_if 0) (expr 1) (kw_then 0) (expr 1) (kw_else 0) (expr 0)))
  (clause' (clause 0) ((expr 100) (op_double_right_arrow 0) (expr 0)))
  (nil' (clauses 0) ())
  (period' (clauses 0) ((clause 0) (opt_semicolon 0) (clauses 0)))
  (match' (expr 0) ((kw_match 0) (expr 1) (kw_with 0) (clauses 0))) // Possibly ambiguous
  (nil' (begin 0) ())
  (period' (begin 0) ((expr 0) (opt_semicolon 0) (begin 0)))
  (set' (expr 0) ((symbol 0) (op_equals 0) (expr 0)))
  (begin' (expr 0) ((kw_begin 0) (begin 0))) // Possibly ambiguous

  (id' (expr 100) ((tree 0)))
  (tree' (tree 0) ((op_left_bracket 0) (expr 0) (op_right_bracket 0)))
  (id' (_ 0) ((expr 0)))

))

// Helper macros
(define true (eq 1 1))
(define false (eq 1 2))

(define_macro syncat_default' (lambda (_ x _) `(,x 0)))
(define_macro syncat_prec' (lambda (_ l r _) `(,l ,r)))
(define_macro syncat_ignored' (lambda (x _) `(,x)))
(define_macro pattern' (lambda (_ m l _ r _) ``(,m ,l ,r)))
(define_macro rule' (lambda (_ m l _ r _) ``(,m ,l ,r)))

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

(define_macro binding' (lambda (sym _ val) `(,sym ,val)))
(define_macro let' (lambda (_ bindings _ body) `(letrec ,bindings ,body)))
(define_macro fun' (lambda (_ arg _ body) `(lambda ,arg ,body)))
(define_macro if' (lambda (_ c _ t _ f) `(cond ,c ,t ,f)))
(define_macro clause' (lambda (pat _ val) `(,pat ,val)))
(define_macro match' (lambda (_ e _ clauses) `(match ,e ,clauses)))
(define_macro set' (lambda (s _ e) `(set ,s ,e)))
(define_macro begin' (lambda (_ x) (cons `begin x)))

// Update syntax
(set_syntax patterns rules)
// Starting from this line, we can write everything in the enhanced syntax!

// =================
// Utility functions
// =================

(define reset_syntax [fun () => (set_syntax patterns rules)])
(define get_patterns [fun () => match (get_syntax) with (patterns rules) => patterns])
(define get_rules [fun () => match (get_syntax) with (patterns rules) => rules])

let sum = fun (l) =>
  match l with
  ()       => 0
  (x . xs) => x + (sum xs)
in (define sum sum)

let concat = fun (l r) =>
  match l with
  ()       => r
  (x . xs) => (cons x (concat xs r))
in (define concat concat)

(define add_pattern [fun (pattern) => match (get_syntax) with (patterns rules) => (set_syntax (concat patterns (list pattern)) rules)])
(define add_rule [fun (rule) => match (get_syntax) with (patterns rules) => (set_syntax patterns (concat rules (list rule)))])

// Helper function for the next one
let split_rule_rhs = fun (syncats n) =>
  match syncats with
  ()       => (list `() `() `())
  (x . xs) => [
    match (split_rule_rhs xs [n + 1]) with (rhs arg_list body) => [
      match x with
      (x)        => (list (cons x rhs) (cons `_ arg_list) body)
      (sym prec) => let var_sym = (string_symbol (string_concat "_" (print n)))
                    in (list (cons x rhs) (cons var_sym arg_list) (cons (list `unquote var_sym) body))
    ]
  ]
in (define split_rule_rhs split_rule_rhs)

// Automatically generates code that defines a "symbol-discarding" macro like the ones on lines 154~184
(define add_rule_auto [fun ((func_name lhs rhs)) =>
  let macro_name = (string_symbol (string_concat (print func_name) "'"))
  in match (split_rule_rhs rhs 0) with (rhs arg_list body) => `[begin
    [match (get_syntax) with (patterns rules) => (set_syntax patterns (concat rules (quote ((,macro_name ,lhs ,rhs)))))]
    (define_macro ,macro_name [fun ,arg_list => (quote ,(cons func_name body))])
  ]
])
(define_macro add_rule_auto' [fun (_ _ e _) => (add_rule_auto (eval e))])

(add_pattern `(_ (kw_add_rule_auto 0) (word "add_rule_auto")))
(add_rule `(add_rule_auto' (tree 0) ((op_left_paren 0) (kw_add_rule_auto 0) (tree 0) (op_right_paren 0))))

// Additional operators
(add_pattern   [_ <op_double_plus> ::= (word "++")])
(add_rule_auto [concat <expr 70> ::= <expr 70> <op_double_plus>* <expr 71>])
(add_pattern   [_ <op_period_double_plus> ::= (word ".++")])
(add_rule_auto [string_concat <expr 70> ::= <expr 70> <op_period_double_plus>* <expr 71>])
