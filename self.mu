// Default syntax

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

  (symbol' (tree 0)
    (concat (alt (range 97 122) (range 65 90) (char "_'") (utf8seg))
            (star (alt (range 97 122) (range 65 90) (range 48 57) (char "_'") (utf8seg)))))

  (nat64' (tree 0)
    (alt (plus (range 48 57))
        (concat (char "0")
                (char "xX")
                (plus (alt (range 48 57) (range 97 102) (range 65 70))))))

  (string' (tree 0)
    (concat (char "\"")
            (star (alt (except "\\\"")
                       (concat (char "\\") (char "\\\"abfnrtv"))))
            (char "\"")))

  (_ (left_paren 0) (word "("))
  (_ (right_paren 0) (word ")"))
  (_ (period 0) (word "."))

)))

(define rules (quote (

  (nil' (list 0) ())
  (cons' (list 0) ((tree 0) (list 0)))
  (period' (list 0) ((tree 0) (period 0) (tree 0)))
  (tree' (tree 0) ((left_paren 0) (list 0) (right_paren 0)))
  (id' (_ 0) ((tree 0)))

)))

(set_syntax patterns rules)
