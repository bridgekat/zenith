-- Simple type theory / higher-order logic for experimentation
-- This variant of HOL is largely based on William M. Farmer's *The Seven Virtues of Simple Type Theory*...

module HOL (Type(..), Expr(..), Context(..), Judgment(..),
            freeVars,
            weaken, varMk, appMk, lamMk, eqMk, iotaMk,
            Theorem, thmJudgment, thmContext, thmExpr, thmType) where

import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map


data Type =
    TVar
  | TProp
  | TLam Type Type
  deriving (Eq)

showT :: Type -> String
showT TVar = "ι"
showT TProp = "*"
showT (TLam t1 t2) = "(" ++ showT t1 ++ " → " ++ showT t2 ++ ")"

instance Show Type where
  show = showT

-- TODO: locally nameless variables
data Expr =
    Var String
  | App Expr Expr
  | Lam String Type Expr
  | Eq Expr Expr
  | Iota String Type Expr
  deriving (Eq)

showE :: Expr -> String
showE (Var x) = x
showE (App e1 e2) = "(" ++ showE e1 ++ " " ++ showE e2 ++ ")"
showE (Lam x t e) = "(λ " ++ x ++ " : " ++ showT t ++ ", " ++ showE e ++ ")"
showE (Eq e1 e2) = "(" ++ showE e1 ++ " = " ++ showE e2 ++ ")"
showE (Iota x t e) = "(I " ++ x ++ " : " ++ showT t ++ ", " ++ showE e ++ ")"

instance Show Expr where
  show = showE


{-
freeVars :: Expr -> Set String
freeVars (Var x) = Set.singleton x
freeVars (App e1 e2) = Set.union (freeVars e1) (freeVars e2)
freeVars (Lam x t e) = Set.delete x (freeVars e)
freeVars (Eq e1 e2) = Set.union (freeVars e1) (freeVars e2)
freeVars (Iota x t e) = Set.delete x (freeVars e)
-}

freeVars :: Expr -> [String]
freeVars (Var x) = [x]
freeVars (App e1 e2) = freeVars e1 ++ freeVars e2
freeVars (Lam x t e) = filter (/= x) (freeVars e)
freeVars (Eq e1 e2) = freeVars e1 ++ freeVars e2
freeVars (Iota x t e) = filter (/= x) (freeVars e)


-- Assuming structural rules: contraction and permutation; weakening is stated below
type Context = Map String Type

-- `context ⊢ expr : type`
type Judgment = (Context, Expr, Type)

newtype Theorem = Theorem Judgment

thmJudgment :: Theorem -> Judgment
thmJudgment (Theorem j) = j

thmContext :: Theorem -> Context
thmContext (Theorem (c, _, _)) = c

thmExpr :: Theorem -> Expr
thmExpr (Theorem (_, e, _)) = e

thmType :: Theorem -> Type
thmType (Theorem (_, _, t)) = t

weaken :: Theorem -> (String, Type) -> Theorem
weaken (Theorem (ctx, e, te)) (x, tx) = Theorem (Map.insert x tx ctx, e, te)


-- Formation rules

varMk :: Context -> String -> Theorem
varMk ctx s = case Map.lookup s ctx of
  Nothing  -> error ("Variable not in context: " ++ s)
  (Just t) -> Theorem (ctx, Var s, t)

appMk :: Theorem -> Theorem -> Theorem
appMk (Theorem (ctx1, e1, t1)) (Theorem (ctx2, e2, t2)) = case t1 of
  (TLam l r)
    | l == t2   -> Theorem (Map.union ctx1 ctx2, App e1 e2, r)
    | otherwise -> error ("Incompatible types in function application: " ++ show l ++ ", " ++ show t2)
  _ -> error ("Not a function type: " ++ show t1)

lamMk :: String -> Type -> Theorem -> Theorem
lamMk x tx (Theorem (ctx, e, te)) = Theorem (ctx', Lam x tx e, TLam tx te)
  where
    ctx' = case Map.lookup x ctx of
      (Just tx')
        | tx' == tx -> Map.delete x ctx
      _             -> ctx -- Weakening is assumed

eqMk :: Theorem -> Theorem -> Theorem
eqMk (Theorem (ctx1, e1, t1)) (Theorem (ctx2, e2, t2))
  | t1 == t2  = Theorem (Map.union ctx1 ctx2, Eq e1 e2, TProp)
  | otherwise = error ("Incompatible types in equality: " ++ show t1 ++ ", " ++ show t2)

iotaMk :: String -> Type -> Theorem -> Theorem
iotaMk x tx (Theorem (ctx, e, te))
  | te /= TProp = error ("Not a proposition type: " ++ show te)
  | otherwise   = Theorem (ctx', Iota x tx e, tx)
  where
    ctx' = case Map.lookup x ctx of
      (Just tx')
        | tx' == tx -> Map.delete x ctx
      _             -> ctx -- Weakening is assumed (though useless here)


-- TODO: inference rules

-- eqSubst :: Theorem -> Expr -> Theorem

