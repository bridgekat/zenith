-- ApiMu/HOL verifier v0.1 (Haskell version)
-- Licensed under Creative Commons CC0 (no copyright reserved, use at your will)

-- This variant of HOL is largely based on William M. Farmer's *The Seven Virtues of Simple Type Theory*...

module HOL (Type(..), Expr(..), Context(..), Judgment(..),
            weaken, mkVar, mkApp, mkLam, mkEq, mkIota,
            Theorem, thmJudgment, thmContext, thmExpr, thmType) where

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

-- Assuming structural rules: contraction and permutation
-- Weakening is stated below
type Context = Map String Type

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

mkVar :: Context -> String -> Theorem
mkVar ctx s = case Map.lookup s ctx of
  Nothing  -> error ("Variable not in context: " ++ s)
  (Just t) -> Theorem (ctx, Var s, t)

mkApp :: Theorem -> Theorem -> Theorem
mkApp (Theorem (ctx1, e1, t1)) (Theorem (ctx2, e2, t2)) = case t1 of
  (TLam l r)
    | l == t2   -> Theorem (Map.union ctx1 ctx2, App e1 e2, r)
    | otherwise -> error ("Incompatible types in function application: " ++ show l ++ ", " ++ show t2)
  _ -> error ("Not a function type: " ++ show t1)

mkLam :: String -> Type -> Theorem -> Theorem
mkLam x tx (Theorem (ctx, e, te)) = Theorem (ctx', Lam x tx e, TLam tx te)
  where
    ctx' = case Map.lookup x ctx of
      (Just tx')
        | tx' == tx -> Map.delete x ctx
      _             -> ctx -- Weakening is assumed

mkEq :: Theorem -> Theorem -> Theorem
mkEq (Theorem (ctx1, e1, t1)) (Theorem (ctx2, e2, t2))
  | t1 == t2  = Theorem (Map.union ctx1 ctx2, Eq e1 e2, TProp)
  | otherwise = error ("Incompatible types in equality: " ++ show t1 ++ ", " ++ show t2)

mkIota :: String -> Type -> Theorem -> Theorem
mkIota x tx (Theorem (ctx, e, te))
  | te /= TProp = error ("Not a proposition type: " ++ show te)
  | otherwise   = Theorem (ctx', Iota x tx e, tx)
  where
    ctx' = case Map.lookup x ctx of
      (Just tx')
        | tx' == tx -> Map.delete x ctx
      _             -> ctx -- Weakening is assumed (though useless here)

-- TODO: encoding logical connectives, quantifiers, & proof system



