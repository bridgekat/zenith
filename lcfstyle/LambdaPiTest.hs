import LambdaPi

-- Put them together...

convertAndCheck' :: Context -> Expr -> Theorem
convertAndCheck' ctx e = case e of
  (Var (Free x)) -> varMk ctx x
  (Var (Bound i)) -> error "Please use names for bound variables in the input expression"
  (Sort n) -> sortMk n
  (Pi x t e) -> piMk wft (convertAndCheck (ctxVar x wft) e) where wft = convertAndCheck ctx t
  (Lam x t e) -> piIntro (convertAndCheck (ctxVar x wft) e) where wft = convertAndCheck ctx t
  (App e1 e2) -> beta (piElim (convertAndCheck ctx e1) (convertAndCheck ctx e2))

convertAndCheck :: Context -> Expr -> Theorem
convertAndCheck ctx e = weaken (convertAndCheck' ctx e) ctx

var = Var . Free

id' = Lam "α" (Sort 0) (Lam "a" (var "α") (var "a"))
ex0 = convertAndCheck ctxEmpty id'
-- (λ α : Sort 0, (λ a : α, a)) : (Π α : Sort 0, (Π a : α, α))

ctx :: Context
ctx =
  ctxVar "False" . flip convertAndCheck (var "Bool") $
  ctxVar "Bool" . flip convertAndCheck (Sort 0) $
  ctxEmpty

ex1 = convertAndCheck ctx (App id' (var "Bool"))
-- ((λ α : Sort 0, (λ a : α, a)) Bool) ~> (λ a : Bool, a) : (Π a : Bool, Bool)
ex2 = convertAndCheck ctx (App (App id' (var "Bool")) (var "False"))
-- (((λ α : Sort 0, (λ a : α, a)) Bool) False) ~> False : Bool



