import Prelude hiding (true, false, not, and, or)
import Data.Map (Map)
import qualified Data.Map as Map

import HOL


convertAndCheck' :: Context -> Expr -> Theorem
convertAndCheck' ctx e = case e of
  (Var (Free x)) -> varMk ctx x
  (App e1 e2) -> appMk (convertAndCheck ctx e1) (convertAndCheck ctx e2)
  (Lam x t e) -> lamMk (convertAndCheck (ctxVar (x, t) ctx) e)
  (Eq e1 e2) -> eqMk (convertAndCheck ctx e1) (convertAndCheck ctx e2)
  (Iota x t e) -> iotaMk (convertAndCheck (ctxVar (x, t) ctx) e)

convertAndCheck :: Context -> Expr -> Theorem
convertAndCheck ctx e = weaken (convertAndCheck' ctx e) ctx


-- Encoding logical connectives & quantifiers

var :: String -> Expr
var = Var . Free

true :: Expr
true = Eq (Lam "x" TProp (var "x")) (Lam "x" TProp (var "x"))

false :: Expr
false = Eq (Lam "x" TProp true) (Lam "x" TProp (var "x"))

not :: Expr -> Expr
not a = Eq a false

and :: Expr -> Expr -> Expr
and a b = Eq
  (Lam "f" (TFun TProp (TFun TProp TProp)) (App (App (var "f") true) true))
  (Lam "f" (TFun TProp (TFun TProp TProp)) (App (App (var "f") a) b))

or :: Expr -> Expr -> Expr
or a b = not (and (not a) (not b))

implies :: Expr -> Expr -> Expr
implies a b = or (not a) b

iff :: Expr -> Expr -> Expr
iff a b = Eq a b

forall :: String -> Type -> Expr -> Expr
forall x t e = Eq (Lam x t e) (Lam x t true)

exists :: String -> Type -> Expr -> Expr
exists x t e = not (forall x t (not e))

-- A canonical "error" term for every type
bottom :: Type -> Expr
bottom t = Iota "x" t (not (Eq (var "x") (var "x")))

{-
-- If ... then ... else ...
ite :: String -> Type -> Expr -> Expr -> Expr -> Expr
ite x t e e1 e2 =
  | x `elem` freeVars e || x `elem` freeVars e1 || x `elem` freeVars e2 = error ("Variable " ++ x ++ " occurs free in e, e1 or e2")
  | otherwise = Iota x t (and (implies e (Eq (var x) e1)) (implies (not e) (Eq (var x) e2)))
-}


-- TODO: proof system (do we have natural deduction for this?)


-- TEMP CODE

ctx :: Context
ctx =
  ctxVar ("+", TFun TVar (TFun TVar TVar)) $
  ctxVar ("<", TFun TVar (TFun TVar TProp)) $
  ctxVar ("3", TVar) $
  ctxEmpty

e1 = Lam "x" TVar (Lam "y" TVar (App (App (var "+") (var "x")) (var "y")))
-- `e1` output: (λ x : ι, (λ y : ι, ((+ x) y)))
-- `thmType . convertAndCheck ctx $ e1` output: (ι → (ι → ι))

e2 = Lam "x" TVar (Lam "y" TVar (App (App (var "<") (App (App (var "+") (var "x")) (var "y"))) (var "3")))
-- `e2` output: (λ x : ι, (λ y : ι, ((< ((+ x) y)) 3)))
-- `thmType . convertAndCheck ctx $ e2` output: (ι → (ι → *))

e3 = forall "x" TVar (and true (implies (Eq (var "x") (var "x")) false))

e4 = exists "x" (TFun TVar TProp) (forall "y" TVar (App (var "x") (var "y")))






