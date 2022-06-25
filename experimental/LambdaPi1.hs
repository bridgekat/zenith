-- Dependent type theory for experimentation
-- This variant of DTT is largely based on Andres Löh, Conor McBride & Wouter Swierstra's
-- *A tutorial implementation of a dependently typed lambda calculus*...

{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}

module LambdaPi1 where

import Data.List
import Data.Char
import Control.Monad


type Context = [(String, Value)]

-- Bound variables are represented using de Brujin indices
-- (0 = binds to the deepest binder, 1 = escapes one binder, and so on)
data VarName = Free String | Bound Int
  deriving (Eq)

-- "Inferable" and "checkable" distinction (not necessary)
data IC = Inferable | Checkable

data Expr a where
  -- "Inferable": type can be determined by looking only at the subtree (bottom-up)
  Ann :: Expr 'Checkable -> Expr 'Checkable -> Expr 'Inferable
  Var :: VarName                            -> Expr 'Inferable
  Star ::                                      Expr 'Inferable
  Pi  :: Expr 'Checkable -> Expr 'Checkable -> Expr 'Inferable
  App :: Expr 'Inferable -> Expr 'Checkable -> Expr 'Inferable
  -- "Checkable": given an expected type, we can determine whether it is possible to
  -- fill in the "blanks" and make the subtree this type (top-down)
  -- (All inferable expressions are also checkable, just infer and compare)
  Inf :: Expr 'Inferable                    -> Expr 'Checkable
  Lam :: Expr 'Checkable                    -> Expr 'Checkable

instance Eq (Expr a) where
  (==) (Ann x1 x2) (Ann y1 y2) = x1 == y1 && x2 == y2
  (==) (Var x1)    (Var y1)    = x1 == y1
  (==) (Star)      (Star)      = True
  (==) (Pi x1 x2)  (Pi y1 y2)  = x1 == y1 && x2 == y2
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
  (Ann e1 e2)  -> "(" ++ showE used stk e1 ++ " : " ++ showE used stk e2 ++ ")"
  (Var x)      -> showName stk x
  (Star)       -> "*"
  (Pi e1 e2)   -> "(Π " ++ x' ++ " : " ++ showE used stk e1 ++ ", " ++ showE (x' : used) (x' : stk) e2 ++ ")" where x' = newName "a" used
  (App e1 e2)  -> "(" ++ showE used stk e1 ++ " " ++ showE used stk e2 ++ ")"
  (Inf e1)     -> showE used stk e1
  (Lam e1)     -> "(λ " ++ x' ++ ", " ++ showE (x' : used) (x' : stk) e1 ++ ")" where x' = newName "a" used

inContextShowE :: Context -> Expr a -> String
inContextShowE ls = showE (map fst ls) []

instance Show (Expr a) where
  show = showE [] []

-- n = (number of binders on top of current node)
updateVars :: Int -> (Int -> VarName -> Expr 'Inferable) -> Expr a -> Expr a
updateVars n f e = case e of
  (Ann e1 t1)  -> Ann (updateVars n f e1) t1
  (Var x)      -> f n x
  (Star)       -> Star
  (Pi e1 e2)   -> Pi (updateVars n f e1) (updateVars (n + 1) f e2)
  (App e1 e2)  -> App (updateVars n f e1) (updateVars n f e2)
  (Inf e1)     -> Inf (updateVars n f e1)
  (Lam e1)     -> Lam (updateVars (n + 1) f e1)

-- Input expression can be a subexpression which is not well-formed by itself
makeReplace :: Expr 'Inferable -> Expr a -> Expr a
makeReplace t = updateVars 0 (\n x -> if x == Bound n then t else Var x)


-- Using the Either monad to represent failure
throwError :: String -> Either String a
throwError = Left

-- Infer types by looking at the subtree (storing inferred types in their normal form)
inferType :: [Value] -> Context -> Expr 'Inferable -> Either String Value
inferType stk ctx (Ann e1 e2) =
  do  checkType stk ctx e2 VStar;
      checkType stk ctx e1 e2';
      return e2';
  where e2' = eval [] e2
inferType stk ctx (Var (Free x)) =
  case lookup x ctx of
    (Just t) -> return t
    Nothing  -> throwError ("Unknown identifier: " ++ x)
inferType stk ctx (Var (Bound i)) =
  return (stk !! i)
inferType stk ctx (Star) =
  return VStar
inferType stk ctx (Pi e1 e2) =
  do  checkType stk ctx e1 VStar;
      checkType (e1' : stk) ctx e2 VStar;
      return VStar;
  where e1' = eval [] e1;
inferType stk ctx (App e1 e2) =
  do  t <- inferType stk ctx e1;
      case t of
        (VPi t1 t2) -> do checkType stk ctx e2 t1; return (t2 (eval [] e2))
        _           -> throwError ("Expected function, given term has type " ++ show (quote 0 t))

-- Check if subtree can have a given type (storing expected type in its normal form)
checkType :: [Value] -> Context -> Expr 'Checkable -> Value -> Either String ()
checkType stk ctx (Inf e) t =
  do  t' <- inferType stk ctx e;
      unless (quote 0 t == quote 0 t') $ throwError ("Type mismatch, expected " ++ show (quote 0 t) ++ ", inferred " ++ show (quote 0 t'))
checkType stk ctx (Lam e) (VPi t1' t2') =
  do  checkType (undefined : stk) ((x', t1') : ctx) (makeReplace (Var (Free x')) e) (t2' (VNeutral (NFree x')))
  where x' = "$" ++ show (length stk) -- Make a temporary variable
checkType stk ctx (Lam e) t =
  throwError ("Expected term of type " ++ show (quote 0 t) ++ ", given term has function type")

-- Evaluation result (normal form)
-- "Higher-order abstract syntax": use metalanguage constructs (Haskell functions) for higher-order values (functions)
data Value =
    VPi Value (Value -> Value)
  | VLam (Value -> Value)
  | VStar
  | VNeutral Neutral

data Neutral =
    NFree String
  | NApp Neutral Value

eval :: [Value] -> Expr a -> Value
eval stk (Ann e _) = eval stk e
eval stk (Var (Free id)) = VNeutral (NFree id)
eval stk (Var (Bound i)) = stk !! i
eval stk (Star) = VStar
eval stk (Pi e1 e2) = VPi (eval stk e1) (\x -> eval (x : stk) e2)
eval stk (App e1 e2) =
  case eval stk e1 of
    (VLam f)     -> f v -- Let Haskell do the beta-reduction...
    (VNeutral f) -> VNeutral (NApp f v)
    _            -> error "Illegal function application during evaluation"
  where
    v = eval stk e2
eval stk (Inf i) = eval stk i
eval stk (Lam e) = VLam (\x -> eval (x : stk) e)

-- Convert Haskell functions back to expressions in the subject language
quote :: Int -> Value -> Expr 'Checkable
quote i (VPi v f)    = Inf (Pi (quote i v) (quote (i + 1) (f (VNeutral (NFree ('$' : show i))))))
quote i (VLam f)     = Lam (quote (i + 1) (f (VNeutral (NFree ('$' : show i))))) -- Substitute in a temporary variable
quote i (VStar)      = Inf (Star)
quote i (VNeutral f) = Inf (quoteN i f)

quoteN :: Int -> Neutral -> Expr 'Inferable
quoteN i (NFree ('$' : s)) = Var (Bound (i - 1 - read s)) -- Temporary variable encountered, making into bound
quoteN i (NFree x)         = Var (Free x)
quoteN i (NApp n v)        = App (quoteN i n) (quote i v)


-- TEMP CODE

id' = Ann (Lam (Lam (Inf . Var . Bound $ 0))) (Inf $ Pi (Inf Star) (Inf $ Pi (Inf . Var . Bound $ 0) (Inf . Var . Bound $ 1)))
ctx = [("False", eval [] (Var . Free $ "Bool")), ("Bool", eval [] Star)]

Right ex1' = inferType [] ctx (App id' (Inf . Var . Free $ "Bool"))
ex1 = quote 0 ex1'
Right ex2' = inferType [] ctx (App (App id' (Inf . Var . Free $ "Bool")) (Inf . Var . Free $ "False"))
ex2 = quote 0 ex2'


