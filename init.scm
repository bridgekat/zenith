{
(define (car (h . _)) h)
(define (cdr (_ . t)) t)
(define hd car)
(define tl cdr)

(define prop          '(Sort Prop))
(define type          '(Sort Type))
(define setvar        '(Var Free 0))
(define arbitrary     '(Var Free 1))
(define (equals x y)  '(App (App (Var Free 2) ,x) ,y))
(define true          '(Var Free 3))
(define false         '(Var Free 4))
(define (not x)       '(App (Var Free 5) ,x))
(define (and x y)     '(App (App (Var Free 6) ,x) ,y))
(define (or x y)      '(App (App (Var Free 7) ,x) ,y))
(define (implies x y) '(App (App (Var Free 8) ,x) ,y))
(define (iff x y)     '(App (App (Var Free 9) ,x) ,y))
(define (forall s r)  '(App (Var Free 10) @ Lam ,s (Var Free 0) ,r))
(define (exists s r)  '(App (Var Free 11) @ Lam ,s (Var Free 0) ,r))
(define (unique s r)  '(App (Var Free 12) @ Lam ,s (Var Free 0) ,r))

(define (fv id)       '(Var Free  ,id))
(define (bv id)       '(Var Bound ,id))
(define (mv id)       '(Var Meta  ,id))

(define expr @ list->Expr (forall "x" @ exists "y" @ equals (bv 1) (bv 0)))
expr
(Print expr)
(PrintFOL expr)
(Print @ CheckType expr)
// (Expr->list @ CheckType expr)
}


