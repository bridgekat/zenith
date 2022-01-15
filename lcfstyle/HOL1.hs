-- Simple type theory / higher-order logic for experimentation
-- This variant of HOL is largely based on Andres Löh, Conor McBride & Wouter Swierstra's
-- *A tutorial implementation of a dependently typed lambda calculus*...

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}

module HOL1 where

import Data.List
import Control.Monad


data Type =
    TVar String
  | TFun Type Type
  deriving (Eq)

showT :: Type -> String
showT (TVar id) = id
showT (TFun t1 t2) = "(" ++ showT t1 ++ " → " ++ showT t2 ++ ")"

instance Show Type where
  show = showT

-- Bound variables are represented using de Brujin indices
-- (0 = binds to the deepest binder, 1 = escapes one binder, and so on)
data VarName = Free String | Bound Int -- Free : Global String | Local Int | Quote Int ???
  deriving (Eq, Show)

-- "Inferable" and "checkable (against)" distinction (WHY???)
data IC = Inferable | Checkable

data Expr a where
  Ann :: Expr 'Checkable -> Type            -> Expr 'Inferable
  Var :: VarName                            -> Expr 'Inferable
  App :: Expr 'Inferable -> Expr 'Checkable -> Expr 'Inferable
  Inf :: Expr 'Inferable                    -> Expr 'Checkable
  Lam :: Expr 'Checkable                    -> Expr 'Checkable

-- Evaluation result
data Value =
    VLam (Value -> Value)
  | VNeutral Neutral

data Neutral =
    NFree String
  | NApp Neutral Value

vfree :: String -> Value
vfree n = VNeutral (NFree n)

vapp :: Value -> Value -> Value
vapp (VLam f) v = f v
vapp (VNeutral n) v = VNeutral (NApp n v)

eval :: Expr a -> [Value] -> Value
eval (Ann e _) stk = eval e stk
eval (Var (Free id)) stk = vfree id
eval (Var (Bound i)) stk = stk !! i
eval (App e1 e2) stk = vapp (eval e1 stk) (eval e2 stk)
eval (Inf i) stk = eval i stk
eval (Lam e) stk = VLam (\x -> eval e (x : stk))

{-
substI :: Int -> Expr 'Inferable -> Expr 'Inferable -> Expr 'Inferable
substI i r (Ann e t) = Ann (substC i r e) t
substI i r (Var (Bound j))
  | i == j    = r
  | otherwise = Var (Bound j)
substI i r (Var (Free y)) = Var (Free y)
substI i r (App e1 e2) = App (substI i r e1) (substC i r e2)

substC :: Int -> Expr 'Inferable -> Expr 'Checkable -> Expr 'Checkable
substC i r (Inf e) = Inf (substI i r e)
substC i r (Lam e) = Lam (substC (i + 1) r e)

class HasSubst a where
  subst :: Expr 'Inferable -> a -> a

instance HasSubst (Expr 'Inferable) where
  subst = substI 0

instance HasSubst (Expr 'Checkable) where
  subst = substC 0
-}

data Kind = Star
  deriving (Show)

data Info =
    HasKind Kind
  | HasType Type
  deriving (Show)

type Context = [(String, Info)]


throwError :: String -> Either String a
throwError = Left

checkKind :: Context -> Type -> Kind -> Either String ()
checkKind ctx (TVar x) Star =
  case lookup x ctx of
    (Just (HasKind Star)) -> Right ()
    (Just (HasType t))    -> throwError ("Expected type, term " ++ x ++ " has type " ++ show t)
    Nothing               -> throwError ("Unknown identifier: " ++ x)
checkKind ctx (TFun t1 t2) Star =
  do  checkKind ctx t1 Star;
      checkKind ctx t2 Star;

inferType :: [Type] -> Context -> Expr 'Inferable -> Either String Type
inferType stk ctx (Ann e t) =
  do  checkKind ctx t Star;
      checkType stk ctx e t;
      return t;
inferType stk ctx (Var (Free x)) =
  case lookup x ctx of
    (Just (HasType t)) -> return t
    (Just (HasKind t)) -> throwError ("Expected term, type " ++ x ++ " has kind " ++ show t)
    Nothing            -> throwError ("Unknown identifier: " ++ x)
inferType stk ctx (Var (Bound i)) =
  return (stk !! i)
inferType stk ctx (App e1 e2) =
  do  s <- inferType stk ctx e1;
      case s of
        (TFun t1 t2) -> do checkType stk ctx e2 t1; return t2;
        _            -> throwError "Type mismatch in function application: ..."

checkType :: [Type] -> Context -> Expr 'Checkable -> Type -> Either String ()
checkType stk ctx (Inf e) t =
  do  t' <- inferType stk ctx e;
      unless (t == t') $ throwError ("Type mismatch, expected " ++ show t ++ ", inferred " ++ show t')
checkType stk ctx (Lam e) (TFun t1 t2) =
  checkType (t1 : stk) ctx e t2
checkType stk ctx _ _ =
  throwError "Type mismatch in: ..."


