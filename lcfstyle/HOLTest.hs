import Prelude hiding (true, false, not, and, or)
import Data.Map (Map)
import qualified Data.Map as Map

import HOL


convertAndCheck' :: Context -> Expr -> Theorem
convertAndCheck' ctx e = case e of
  (Type _) -> error "Type expression should not appear here"
  (Var (Free x)) -> varMk ctx x
  (Var _) -> error "Please use names for variables in the input expression"
  (App e1 e2) -> appMk (convertAndCheck ctx e1) (convertAndCheck ctx e2)
  (Lam x t e) -> lamMk (convertAndCheck (ctxNewVar x t ctx) e)

convertAndCheck :: Context -> Expr -> Theorem
convertAndCheck ctx e = weaken (convertAndCheck' ctx e) ctx


var :: String -> Expr
var = Var . Free

ctx :: Context
ctx =
  ctxNewVar "+" (TFun TVar (TFun TVar TVar)) $
  ctxNewVar "<" (TFun TVar (TFun TVar TProp)) $
  ctxNewVar "3" TVar ctxEmpty

e1 = Lam "x" TVar (Lam "y" TVar (App (App (var "+") (var "x")) (var "y")))
-- (λ x : ι, (λ y : ι, ((+ x) y)))
wff1 = convertAndCheck ctx e1
-- (ι → (ι → ι))

e2 = Lam "x" TVar (Lam "y" TVar (App (App (var "<") (App (App (var "+") (var "x")) (var "y"))) (var "3")))
-- (λ x : ι, (λ y : ι, ((< ((+ x) y)) 3)))
wff2 = convertAndCheck ctx e2
-- (ι → (ι → *))

ctx' :: Context
ctx' =
  ctxNewVar "exists" (TFun (TFun TVar TProp) TProp) $
  ctxNewVar "forall" (TFun (TFun TVar TProp) TProp) $
  ctxNewVar "iff" (TFun TProp (TFun TProp TProp)) $
  ctxNewVar "implies" (TFun TProp (TFun TProp TProp)) $
  ctxNewVar "or" (TFun TProp (TFun TProp TProp)) $
  ctxNewVar "and" (TFun TProp (TFun TProp TProp)) $
  ctxNewVar "not" (TFun TProp TProp) $
  ctxNewVar "false" TProp $
  ctxNewVar "true" TProp $
  ctxNewVar "eq" (TFun TVar (TFun TVar TProp)) ctx

eq = App . (var "eq" `App`)
true = var "true"
false = var "false"
not = (var "not" `App`)
and = App . (var "and" `App`)
or = App . (var "or" `App`)
implies = App . (var "implies" `App`)
iff = App . (var "iff" `App`)
forall id = (var "forall" `App`) . Lam id TVar
exists id = (var "exists" `App`) . Lam id TVar

e3 = forall "x" (true `and` ((var "x" `eq` var "x") `implies` false))
wff3 = convertAndCheck ctx' e3

e4 = exists "x" (forall "y" (var "x" `App` var "y"))
wff4 = convertAndCheck ctx' e4 -- Should fail


