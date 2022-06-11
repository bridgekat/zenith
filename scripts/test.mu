// Testing continuation-passing style
(define add_ [fun (l r) => fun (k) => (k [l + r])])
(define sub_ [fun (l r) => fun (k) => (k [l - r])])
(define mul_ [fun (l r) => fun (k) => (k [l * r])])
(define div_ [fun (l r) => fun (k) => (k [l / r])])

(define return [fun (x) => fun (k) => (k x)])
(define bind [fun (m f) => fun (k) => (m [fun (x) => ((f x) k)])])

(add_pattern   [_    <op_bind> ::= (word ">>=")])
(add_rule_auto [bind <expr 0>  ::= <expr 1> <op_bind>* <expr 0>])

([(add_ 1 2) >>= fun (x) =>
  (mul_ x 4) >>= fun (y) =>
  (sub_ y 3)] id)
