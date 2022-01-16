import Data.List
import LambdaPi


-- Convert to de Brujin indices.
convert :: [String] -> Expr -> Expr
convert stk e = case e of
  (Var (Free x)) -> case elemIndex x stk of
    Nothing  -> e
    (Just i) -> Var (Bound i)
  (Var (Bound i)) -> error "Please use names for bound variables in the input expression"
  (Sort n) -> e
  (Pi x t e1) -> Pi x (convert stk t) (convert (x : stk) e1)
  (Lam x t e1) -> Lam x (convert stk t) (convert (x : stk) e1)
  (App e1 e2) -> App (convert stk e1) (convert stk e2)
  (Let x e1 e2) -> Let x (convert stk e1) (convert (x : stk) e2)

-- Check the type of converted expressions. (Inefficient, but I don't care for now!)
checkType' :: Context -> Expr -> Theorem
checkType' ctx e = case e of
  (Var (Free x)) -> varMk ctx x
  (Var (Bound i)) -> undefined -- Unreachable
  (Sort n) -> sortMk n
  (Pi x t e) -> piMk wft (checkType (ctxVar x wft) (makeFree x e)) where wft = checkType ctx t
  (Lam x t e) -> piIntro (checkType (ctxVar x wft) (makeFree x e)) where wft = checkType ctx t
  (App e1 e2) -> piElim (checkType ctx e1) (checkType ctx e2)
  (Let x e1 e2) -> letMk x (makeFree x e2) (checkType ctx e1) (checkType ctx (makeReplace e1 e2))

checkType :: Context -> Expr -> Theorem
checkType ctx e = weaken (checkType' ctx e) ctx

-- Combining the above two
convertAndCheck :: Context -> Expr -> Theorem
convertAndCheck ctx = checkType ctx . convert []

var = Var . Free

id' = Lam "α" (Sort 0) (Lam "a" (var "α") (var "a"))
ex0 = convertAndCheck ctxEmpty id'
-- (λ α : Sort 0, (λ a : α, a)) : (Π α : Sort 0, (Π a : α, α))

ctx :: Context
ctx =
  ctxVar "False" . flip convertAndCheck (var "Bool") $
  ctxVar "Bool" . flip convertAndCheck (Sort 0) $
  ctxEmpty

e1 = convert [] $ App id' (var "Bool")
ex1 = checkType ctx e1
-- ((λ α : Sort 0, (λ a : α, a)) Bool) : (Π a : Bool, Bool)
ex1' = defeqCongrTerm ex1 (reduce (thmExpr ex1))
-- (λ a : Bool, a) : (Π a : Bool, Bool)
e2 = convert [] $ App (App id' (var "Bool")) (var "False")
ex2 = checkType ctx e2
-- (((λ α : Sort 0, (λ a : α, a)) Bool) False) : Bool
ex2' = defeqCongrTerm ex2 (reduce (thmExpr ex2))
-- False : Bool
e3 = convert [] $ Let "Bool1" (var "Bool") $ Let "False1" (var "False") $ App (App id' (var "Bool1")) (var "False1")
ex3 = checkType ctx e3
-- (let Bool1 := Bool in (let False1 := False in (((λ α : Sort 0, (λ a : α, a)) Bool1) False1))) : Bool
ex3' = defeqCongrTerm ex3 (reduce (thmExpr ex3))
-- False : Bool


