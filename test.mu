// :load syntax.mu
[
let
  sum = fun (l) =>
    match l with
    ()       => 0
    (x . xs) => x + (sum xs)
in
  (define sum sum)
]
[
let
  concat = fun (l r) =>
    match l with
    ()       => r
    (x . xs) => (cons x (concat xs r))
in
  (define concat concat)
]
(define reset_syntax [fun () => (set_syntax patterns rules)])
(define get_patterns [fun () => match (get_syntax) with (patterns rules) => patterns])
(define get_rules [fun () => match (get_syntax) with (patterns rules) => rules])
(define add_pattern [fun (pattern) => match (get_syntax) with (patterns rules) => (set_syntax (concat patterns (list pattern)) rules)])
(define add_rule [fun (rule) => match (get_syntax) with (patterns rules) => (set_syntax patterns (concat rules (list rule)))])

// Testing continuation-passing style
(define add_ [fun (l r) => fun (k) => (k [l + r])])
(define sub_ [fun (l r) => fun (k) => (k [l - r])])
(define mul_ [fun (l r) => fun (k) => (k [l * r])])
(define div_ [fun (l r) => fun (k) => (k [l / r])])

(define return [fun (x) => fun (k) => (k x)])
(define bind [fun (m f) => fun (k) => (m [fun (x) => ((f x) k)])])

// Add ">>=" as keyword
(add_pattern `(_ (op_bind 0) (word ">>=")))
// Declare it as infix operator, precedence 0, right associative
(add_rule `(bind' (expr 0) ((expr 1) (op_bind 0) (expr 0))))
// Declare handler for the new syntax
(define_macro bind' [fun (l _ r) => `(bind ,l ,r)])

([(add_ 1 2) >>= fun (x) =>
  (mul_ x 4) >>= fun (y) =>
  (sub_ y 3)] id)
