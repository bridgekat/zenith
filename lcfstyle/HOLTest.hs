import Prelude hiding (true, false, not, and, or)
import Data.Map (Map)
import qualified Data.Map as Map

import HOL


checkType :: Context -> Expr -> Theorem
checkType ctx e = case e of
  (Var x) -> varMk ctx x
  (App e1 e2) -> appMk (checkType ctx e1) (checkType ctx e2)
  (Lam x t e) -> lamMk x t (checkType (Map.insert x t ctx) e)
  (Eq e1 e2) -> eqMk (checkType ctx e1) (checkType ctx e2)
  (Iota x t e) -> iotaMk x t (checkType (Map.insert x t ctx) e)


-- Encoding logical connectives & quantifiers

true :: Expr
true = Eq (Lam "x" TProp (Var "x")) (Lam "x" TProp (Var "x"))

false :: Expr
false = Eq (Lam "x" TProp true) (Lam "x" TProp (Var "x"))

not :: Expr -> Expr
not a = Eq a false

and :: Expr -> Expr -> Expr
and a b = Eq
  (Lam "f" (TLam TProp (TLam TProp TProp)) (App (App (Var "f") true) true))
  (Lam "f" (TLam TProp (TLam TProp TProp)) (App (App (Var "f") a) b))

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
bottom t = Iota "x" t (not (Eq (Var "x") (Var "x")))

-- If ... then ... else ...
ite :: String -> Type -> Expr -> Expr -> Expr -> Expr
ite x t e e1 e2
  | x `elem` freeVars e || x `elem` freeVars e1 || x `elem` freeVars e2 = error ("Variable " ++ x ++ " occurs free in e, e1 or e2")
  | otherwise = Iota x t (and (implies e (Eq (Var x) e1)) (implies (not e) (Eq (Var x) e2)))


-- TODO: proof system (do we have natural deduction for this?)




-- TEMP CODE

emptyctx :: Context
emptyctx = Map.empty

ctx :: Context
ctx = Map.fromList
  [ ("+", TLam TVar (TLam TVar TVar)),
    ("<", TLam TVar (TLam TVar TProp)),
    ("3", TVar)
  ]

e1 = Lam "x" TVar (Lam "y" TVar (App (App (Var "+") (Var "x")) (Var "y")))
-- `e1` output: (λ x : ι, (λ y : ι, ((+ x) y)))
-- `thmType . checkType ctx $ e1` output: (ι → (ι → ι))

e2 = Lam "x" TVar (Lam "y" TVar (App (App (Var "<") (App (App (Var "+") (Var "x")) (Var "y"))) (Var "3")))
-- `e2` output: (λ x : ι, (λ y : ι, ((< ((+ x) y)) 3)))
-- `thmType . checkType ctx $ e2` output: (ι → (ι → *))

e3 = forall "x" TVar (and true (implies (Eq (Var "x") (Var "x")) false))

e4 = exists "x" (TLam TVar TProp) (forall "y" TVar (App (Var "x") (Var "y")))


