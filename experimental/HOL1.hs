-- Simple type theory / higher-order logic for experimentation
-- This variant of HOL is largely based on Andres Löh, Conor McBride & Wouter Swierstra's
-- *A tutorial implementation of a dependently typed lambda calculus*...

{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}

module HOL1 where

import Data.List
import Data.Char
import Control.Monad


data Info =
    HasKind Kind
  | HasType Type
  deriving (Eq)

type Context = [(String, Info)]

data Kind =
    Star
  deriving (Eq)

data Type =
    TVar String
  | TFun Type Type
  deriving (Eq)

showK :: Kind -> String
showK Star = "*"

showT :: Type -> String
showT (TVar id) = id
showT (TFun t1 t2) = "(" ++ showT t1 ++ " → " ++ showT t2 ++ ")"

instance Show Kind where
  show = showK

instance Show Type where
  show = showT

-- Bound variables are represented using de Brujin indices
-- (0 = binds to the deepest binder, 1 = escapes one binder, and so on)
data VarName = Free String | Bound Int
  deriving (Eq)

-- "Inferable" and "checkable" distinction (not necessary)
data IC = Inferable | Checkable

data Expr a where
  -- "Inferable": type can be determined by looking only at the subtree (bottom-up)
  Ann :: Expr 'Checkable -> Type            -> Expr 'Inferable
  Var :: VarName                            -> Expr 'Inferable
  App :: Expr 'Inferable -> Expr 'Checkable -> Expr 'Inferable
  -- "Checkable": given an expected type, we can determine whether it is possible to
  -- fill in the "blanks" and make the subtree this type (top-down)
  -- (All inferable expressions are also checkable, just infer and compare)
  Inf :: Expr 'Inferable                    -> Expr 'Checkable
  Lam :: Expr 'Checkable                    -> Expr 'Checkable

instance Eq (Expr a) where
  (==) (Ann x1 x2) (Ann y1 y2) = x1 == y1 && x2 == y2
  (==) (Var x1)    (Var y1)    = x1 == y1
  (==) (App x1 x2) (App y1 y2) = x1 == y1 && x2 == y2
  (==) (Inf x1)    (Inf y1)    = x1 == y1
  (==) (Lam x1)    (Lam y1)    = x1 == y1
  (==) _           _           = False

newName :: String -> [String] -> String
newName [x] used
  | [x] `notElem` used  = [x]
  | 'a' <= x && x < 'z' = [chr (ord x + 1)]
  | x == 'z'            = newName "a'" used
newName x used
  | x `notElem` used    = x
  | otherwise           = newName (x ++ "'") used

showName :: [String] -> VarName -> String
showName stk (Free s)  = s
showName stk (Bound i) = stk !! i

showE :: [String] -> [String] -> Expr a -> String
showE used stk e = case e of
  (Ann e1 t1)  -> "(" ++ showE used stk e1 ++ " : " ++ showT t1 ++ ")"
  (Var x)      -> showName stk x
  (App e1 e2)  -> "(" ++ showE used stk e1 ++ " " ++ showE used stk e2 ++ ")"
  (Inf e1)     -> showE used stk e1
  (Lam e1)     -> "(λ " ++ x' ++ ", " ++ showE (x' : used) (x' : stk) e1 ++ ")" where x' = newName "a" used

inContextShowE :: Context -> Expr a -> String
inContextShowE ls = showE (map fst . filter (\(_, i) -> case i of (HasType _) -> True; _ -> False) $ ls) []

instance Show (Expr a) where
  show = showE [] []

-- n = (number of binders on top of current node)
updateVars :: Int -> (Int -> VarName -> Expr 'Inferable) -> Expr a -> Expr a
updateVars n f e = case e of
  (Ann e1 t1)  -> Ann (updateVars n f e1) t1
  (Var x)      -> f n x
  (App e1 e2)  -> App (updateVars n f e1) (updateVars n f e2)
  (Inf e1)     -> Inf (updateVars n f e1)
  (Lam e1)     -> Lam (updateVars (n + 1) f e1)

-- Input expression can be a subexpression which is not well-formed by itself
makeReplace :: Expr 'Inferable -> Expr a -> Expr a
makeReplace t = updateVars 0 (\n x -> if x == Bound n then t else Var x)


-- Using the Either monad to represent failure
throwError :: String -> Either String a
throwError = Left

-- Check if a type can have a given kind
checkKind :: Context -> Type -> Kind -> Either String ()
checkKind ctx (TVar x) Star =
  case lookup x ctx of
    (Just (HasKind Star)) -> Right ()
    (Just (HasType t))    -> throwError ("Expected type, term " ++ x ++ " has type " ++ show t)
    Nothing               -> throwError ("Unknown identifier: " ++ x)
checkKind ctx (TFun t1 t2) Star =
  do  checkKind ctx t1 Star;
      checkKind ctx t2 Star;

-- Infer types by looking at the subtree
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
  do  t <- inferType stk ctx e1;
      case t of
        (TFun t1 t2) -> do checkType stk ctx e2 t1; return t2;
        _            -> throwError ("Expected function, given term has type " ++ show t)

-- Check if subtree can have a given type
checkType :: [Type] -> Context -> Expr 'Checkable -> Type -> Either String ()
checkType stk ctx (Inf e) t =
  do  t' <- inferType stk ctx e;
      unless (t == t') $ throwError ("Type mismatch, expected " ++ show t ++ ", inferred " ++ show t')
checkType stk ctx (Lam e) (TFun t1 t2) =
  checkType (t1 : stk) ctx e t2
checkType stk ctx (Lam e) t =
  throwError ("Expected term of type " ++ show t ++ ", given term has function type")

-- Evaluation result
-- "Higher-order abstract syntax": use metalanguage constructs (Haskell functions) for higher-order values (functions)
data Value =
    VLam (Value -> Value)
  | VNeutral Neutral

-- Fully-reduced non-function values
data Neutral =
    NFree String
  | NApp Neutral Value

eval :: [Value] -> Expr a -> Value
eval stk (Ann e _) = eval stk e
eval stk (Var (Free id)) = VNeutral (NFree id)
eval stk (Var (Bound i)) = stk !! i
eval stk (App e1 e2) =
  case eval stk e1 of
    (VLam f)     -> f v -- Let Haskell do the beta-reduction... (有必要吗？)
    (VNeutral f) -> VNeutral (NApp f v)
  where
    v = eval stk e2
eval stk (Inf i) = eval stk i
eval stk (Lam e) = VLam (\x -> eval (x : stk) e)

-- Convert Haskell functions back to expressions in the subject language
quote :: Int -> Value -> Expr 'Checkable
quote i (VLam f)     = Lam (quote (i + 1) (f (VNeutral (NFree ('$' : show i))))) -- Substitute in a temporary variable
quote i (VNeutral f) = Inf (quoteN i f)

quoteN :: Int -> Neutral -> Expr 'Inferable
quoteN i (NFree ('$' : s)) = Var (Bound (i - 1 - read s)) -- Temporary variable encountered, making into bound
quoteN i (NFree x)         = Var (Free x)
quoteN i (NApp n v)        = App (quoteN i n) (quote i v)


-- TEMP CODE

id' = Lam (Inf (Var . Bound $ 0))
const' = Lam (Lam (Inf (Var . Bound $ 1)))

tfree = TVar
free x = Inf (Var . Free $ x)

term1 = Ann id' (tfree "a" `TFun` tfree "a") `App` free "y"
term2 = Ann const' ((tfree "b" `TFun` tfree "b") `TFun` (tfree "a" `TFun` (tfree "b" `TFun` tfree "b"))) `App` id' `App` free "y"

env1 = [("y", HasType (tfree "a")), ("a", HasKind Star)]
env2 = ("b", HasKind Star) : env1

ex1 = quote 0 (eval [] term1)
ex2 = quote 0 (eval [] term2)
ex3 = inferType [] env1 term1
ex4 = inferType [] env2 term2


