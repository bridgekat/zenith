// Enhanced syntax!

(define patterns (quote (

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

  (symbol' (symbol 0)
    (concat (alt (range 97 122) (range 65 90) (char "_'") (utf8seg))
            (star (alt (range 97 122) (range 65 90) (range 48 57) (char "_'") (utf8seg)))))

  (nat64' (nat64 0)
    (alt (plus (range 48 57))
        (concat (char "0")
                (char "xX")
                (plus (alt (range 48 57) (range 97 102) (range 65 70))))))

  (string' (string 0)
    (concat (char "\"")
            (star (alt (except "\\\"")
                      (concat (char "\\") (char "\\\"abfnrtv"))))
            (char "\"")))

  (_ (op_left_paren 0) (word "("))
  (_ (op_right_paren 0) (word ")"))
  (_ (op_period 0) (word "."))
  (_ (op_left_bracket 0) (word "["))
  (_ (op_right_bracket 0) (word "]"))

  (_ (op_plus 0) (word "+"))
  (_ (op_minus 0) (word "-"))
  (_ (op_asterisk 0) (word "*"))
  (_ (op_slash 0) (word "/"))

  (_ (op_equals 0) (word "="))
  (_ (op_rarrow 0) (word "=>"))
  (_ (op_comma 0) (word ","))
  (_ (op_colon 0) (word ":"))
  (_ (op_semicolon 0) (word ";"))
  (_ (op_derivation 0) (word "::="))

  (_ (kw_let 0) (word "let"))
  (_ (kw_in 0) (word "in"))
  (_ (kw_fun 0) (word "fun"))
  (_ (kw_if 0) (word "if"))
  (_ (kw_then 0) (word "then"))
  (_ (kw_else 0) (word "else"))
  (_ (kw_match 0) (word "match"))
  (_ (kw_with 0) (word "with"))

)))

(define rules (quote (

  (id' (tree 0) ((symbol 0)))
  (id' (tree 0) ((nat64 0)))
  (id' (tree 0) ((string 0)))

  // See: https://github.com/digama0/mm0/blob/master/mm0-hs/mm1.md#s-expressions

  (nil' (list 0) ())
  (cons' (list 0) ((tree 0) (list 0)))
  (period' (list 0) ((tree 0) (op_period 0) (tree 0)))
  (tree' (tree 0) ((op_left_paren 0) (list 0) (op_right_paren 0)))
  (id' (_ 0) ((tree 0)))

/*
  (nil' (tree 100) ())
  (cons' (tree 75) ((tree 100) (tree 75)))
  (tree' (tree 100) ((op_left_paren 0) (tree 0) (op_right_paren 0)))
  (id' (_ 0) ((tree 100)))
*/

  (equals' (expr 5) ((expr 6) (op_equals 0) (expr 6)))
  (add' (expr 10) ((expr 10) (op_plus 0) (expr 11)))
  (sub' (expr 10) ((expr 10) (op_minus 0) (expr 11)))
  (mul' (expr 20) ((expr 20) (op_asterisk 0) (expr 21)))
  (div' (expr 20) ((expr 20) (op_slash 0) (expr 21)))
  (minus' (expr 21) ((op_minus 0) (expr 21)))

  (_ (opt_comma 0) ())
  (_ (opt_comma 0) ((op_comma 0)))

  (binding' (binding 0) ((symbol 0) (op_equals 0) (expr 0) (opt_comma 0)))
  (nil' (bindings 0) ())
  (cons' (bindings 0) ((binding 0) (bindings 0)))
  (let' (expr 0) ((kw_let 0) (bindings 0) (kw_in 0) (expr 0)))
  (fun' (expr 0) ((kw_fun 0) (expr 0) (op_rarrow 0) (expr 0)))
  (if' (expr 0) ((kw_if 0) (expr 0) (kw_then 0) (expr 0) (kw_else 0) (expr 0)))
  (clause' (clause 0) ((expr 0) (op_rarrow 0) (expr 0) (opt_comma 0)))
  (nil' (clauses 0) ())
  (cons' (clauses 0) ((clause 0) (clauses 0)))
  (match' (expr 0) ((kw_match 0) (expr 0) (kw_with 0) (clauses 0)))

  (id' (expr 100) ((tree 0)))
  (tree' (tree 0) ((op_left_bracket 0) (expr 0) (op_right_bracket 0)))

)))

(define_macro equals' (lambda (l _ r) (quote (eq (unquote l) (unquote r)))))
(define_macro add' (lambda (l _ r) (quote (add (unquote l) (unquote r)))))
(define_macro sub' (lambda (l _ r) (quote (sub (unquote l) (unquote r)))))
(define_macro mul' (lambda (l _ r) (quote (mul (unquote l) (unquote r)))))
(define_macro div' (lambda (l _ r) (quote (div (unquote l) (unquote r)))))
(define_macro minus' (lambda (_ x) (quote (minus (unquote x)))))

(define_macro binding' (lambda (sym _ val _) (quote ((unquote sym) (unquote val)))))
(define_macro let' (lambda (_ bindings _ body) (quote (letrec (unquote bindings) (unquote body)))))
(define_macro fun' (lambda (_ arg _ body) (quote (lambda (unquote arg) (unquote body)))))
(define_macro if' (lambda (_ c _ t _ f) (quote (cond (unquote c) (unquote t) (unquote f)))))
(define_macro clause' (lambda (pat _ val _) (quote ((unquote pat) (unquote val)))))
(define_macro match' (lambda (_ e _ clauses) (quote (match (unquote e) (unquote clauses)))))

(set_syntax patterns rules)
