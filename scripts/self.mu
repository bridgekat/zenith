// ====================================
// Default syntax for the base language
// ====================================

(define patterns `(

  (_ (star (char " \f\n\r\t\v")))
  (_ (concat (word "//") (star (except "\n\r"))))
  (_ (concat (word "/*")
             (star (concat (star (except "*"))
                           (plus (char "*"))
                           (except "/")))
             (star (except "*"))
             (plus (char "*"))
             (char "/")))

  (symbol
    (concat (alt (range 97 122) (range 65 90) (char "_'") (utf8seg))
            (star (alt (range 97 122) (range 65 90) (range 48 57) (char "_'") (utf8seg)))))

  (nat64
    (alt (plus (range 48 57))
        (concat (char "0")
                (char "xX")
                (plus (alt (range 48 57) (range 97 102) (range 65 70))))))

  (string
    (concat (char "\"")
            (star (alt (except "\\\"")
                       (concat (char "\\") (char "\\\"abfnrtv"))))
            (char "\"")))

  (left_paren (word "("))
  (right_paren (word ")"))
  (period (word "."))
  (quote (word "`"))
  (comma (word ","))

))

(define rules `(

  (symbol' (tree 0) ((symbol 0)))
  (nat64' (tree 0) ((nat64 0)))
  (string' (tree 0) ((string 0)))
  (nil' (list 0) ())
  (cons' (list 0) ((tree 0) (list 0)))
  (period' (list 0) ((tree 0) (period 0) (tree 0)))
  (quote' (tree 0) ((quote 0) (tree 0)))
  (unquote' (tree 0) ((comma 0) (tree 0)))
  (tree' (tree 0) ((left_paren 0) (list 0) (right_paren 0)))
  (id' (_ 0) ((tree 0)))

))

(set_syntax patterns rules)
