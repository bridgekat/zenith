import Data.Map (Map)
import qualified Data.Map as Map

import HOL


checkType :: Context -> Expr -> Theorem
checkType ctx e = case e of
  (Var x) -> mkVar ctx x
  (App e1 e2) -> mkApp (checkType ctx e1) (checkType ctx e2)
  (Lam x t e) -> mkLam x t (checkType (Map.insert x t ctx) e)
  (Eq e1 e2) -> mkEq (checkType ctx e1) (checkType ctx e2)
  (Iota x t e) -> mkIota x t (checkType (Map.insert x t ctx) e)


-- TEMP CODE

{-
assume :: Context -> (String, Type) -> [Theorem] -> [Theorem]
assume curr next 
-}

ctx :: Context
ctx = Map.fromList
  [ ("+", TLam TVar (TLam TVar TVar)),
    ("<", TLam TVar (TLam TVar TProp)),
    ("3", TVar)
  ]

e1 = Lam "x" TVar (Lam "y" TVar (App (App (Var "+") (Var "x")) (Var "y")))
-- `e1` output: (λ x : ι, (λ y : ι, ((+ x) y)))
-- `thmType (checkType ctx e1)` output: (ι → (ι → ι))

e2 = Lam "x" TVar (Lam "y" TVar (App (App (Var "<") (App (App (Var "+") (Var "x")) (Var "y"))) (Var "3")))
-- `e2` output: (λ x : ι, (λ y : ι, ((< ((+ x) y)) 3)))
-- `thmType (checkType ctx e2)` output: (ι → (ι → *))


