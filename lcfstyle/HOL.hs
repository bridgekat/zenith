-- Simple type theory / higher-order logic for experimentation
-- This variant of HOL ~~is~~ was largely based on William M. Farmer's *The Seven Virtues of Simple Type Theory*...

{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module HOL where

import Data.List


-- The context is stored as a stack (a list whose first element denotes the topmost layer).
-- On each layer there is a list:
--   The first element is what was "assumed" at the beginning of the current scope.
--   The later elements are what were "defined" inside the current scope.
-- We don't have contraction or permutation rules, but currently they are not needed; weakening is stated below.
newtype Context = Context { ctxStack :: [[(String, Expr)]] }
  deriving (Eq)

instance Show Context where
  show ctx@(Context a) =
    foldr (\defs acc -> acc ++ foldl (\acc (id, c) -> acc ++ id ++ " : " ++ show c ++ "\n  | ") "" defs ++ "\n") "" a

ctxEmpty :: Context
ctxEmpty = Context []

ctxNewVar :: String -> Type -> Context -> Context
ctxNewVar id t ctx@(Context a)
  | id `notElem` ctxAllNames ctx = Context ([(id, Type t)] : a)
  | otherwise = error ("ctxNewVar: name " ++ id ++ "already taken")

ctxAssumption :: String -> Theorem -> Context
ctxAssumption id (Theorem (ctx@(Context a), HasType p TProp))
  | id `notElem` ctxAllNames ctx = Context ([(id, p)] : a)
  | otherwise     = error ("ctxAssumption: name " ++ id ++ "already taken")
ctxAssumption _ _ = error "ctxAssumption"

-- Add definition entry (hidden)
ctxAddDef :: String -> Type -> Context -> Context
ctxAddDef id t ctx@(Context (l : ls))
  | id `notElem` ctxAllNames ctx = Context (((id, Type t) : l) : ls)
  | otherwise   = error ("ctxAddDef: name " ++ id ++ "already taken")
ctxAddDef _ _ _ = error "ctxAddDef"

-- Returns True if the first context is an extension of the second one (used in the weakening rule)
isExtensionOf :: Context -> Context -> Bool
isExtensionOf (Context a') (Context a) =
  length a' >= length a && and (zipWith isPrefixOf (reverse a) (reverse a'))

-- Get all names
ctxAllNames :: Context -> [String]
ctxAllNames (Context a) = concatMap (map fst) a

-- Look up by name
ctxLookup :: String -> Context -> Maybe Expr
ctxLookup s (Context a) = ctxLookup' a
  where
    ctxLookup' [] = Nothing
    ctxLookup' (l : ls) = case lookup s l of
      Just res -> Just res
      Nothing  -> ctxLookup' ls

-- Bound variables are represented using de Bruijn indices
-- (0 = binds to the deepest binder, 1 = escapes one binder, and so on)
data VarName = Free String | Bound Int
  deriving (Eq)

data Type =
    TVar
  | TProp
  | TFun Type Type
  deriving (Eq)

showT :: Type -> String
showT TVar = "ι"
showT TProp = "*"
showT (TFun t1 t2) = "(" ++ showT t1 ++ " → " ++ showT t2 ++ ")"

instance Show Type where
  show = showT

data Expr =
    Type Type
  | Var VarName
  | App Expr Expr
  | Lam String Type Expr

-- Ignore the names of bound variables when comparing
instance Eq Expr where
  (==) (Type x1)      (Type y1)      = x1 == y1
  (==) (Var x1)       (Var y1)       = x1 == y1
  (==) (App x1 x2)    (App y1 y2)    = x1 == y1 && x2 == y2
  (==) (Lam _ x1 x2)  (Lam _ y1 y2)  = x1 == y1 && x2 == y2
  (==) _              _              = False

newName :: String -> [String] -> String
newName x used
  | x `notElem` used = x
  | otherwise        = newName (x ++ "'") used

showName :: [String] -> VarName -> String
showName stk (Free s)  = s
showName stk (Bound i) = stk !! i

showE :: [String] -> [String] -> Expr -> String
showE used stk e = case e of
  (Type t)     -> show t
  (Var x)      -> showName stk x
  (App e1 e2)  -> "(" ++ showE used stk e1 ++ " " ++ showE used stk e2 ++ ")"
  (Lam x t e)  -> "(λ " ++ x' ++ " : " ++ showT t ++ ", " ++ showE (x' : used) (x' : stk) e ++ ")" where x' = newName x used

inContextShowE :: Context -> Expr -> String
inContextShowE ctx = showE (ctxAllNames ctx) []

instance Show Expr where
  show = inContextShowE ctxEmpty

-- n = (number of binders on top of current node)
updateVars :: Int -> (Int -> VarName -> Expr) -> Expr -> Expr
updateVars n f e = case e of
  (Type t)     -> Type t
  (Var x)      -> f n x
  (App e1 e2)  -> App (updateVars n f e1) (updateVars n f e2)
  (Lam x t e)  -> Lam x t (updateVars (n + 1) f e)

-- Replace occurrences of a free variable by a given term
-- Pre: t is a well-formed term
replaceVar :: String -> Expr -> Expr -> Expr
replaceVar id t = updateVars 0 (\_ x -> if x == Free id then t else Var x)

-- Note that the resulting expression is not well-formed until one additional layer of binder is added
makeBound :: String -> Expr -> Expr
makeBound id = updateVars 0 (\n x -> if x == Free id then Var (Bound n) else Var x)

-- Input expression can be a subexpression which is not well-formed by itself
makeFree :: String -> Expr -> Expr
makeFree id = updateVars 0 (\n x -> if x == Bound n then Var (Free id) else Var x)

-- Input expression can be a subexpression which is not well-formed by itself
makeReplace :: Expr -> Expr -> Expr
makeReplace t = updateVars 0 (\n x -> if x == Bound n then t else Var x)

-- Kinds of judgments
data Judgment = HasType Expr Type | Provable Expr
  deriving (Eq)

inContextShowJ :: Context -> Judgment -> String
inContextShowJ ctx j = case j of
  (HasType e t) -> inContextShowE ctx e ++ " : " ++ show t
  (Provable e)  -> "Provable : " ++ inContextShowE ctx e

-- Main theorem type
newtype Theorem = Theorem (Context, Judgment)

thmContext :: Theorem -> Context
thmContext (Theorem (c, _)) = c

thmJudgment :: Theorem -> Judgment
thmJudgment (Theorem (_, j)) = j

instance Show Theorem where
  show (Theorem (c, j)) = "\n" ++ show c ++ "\n|- " ++ inContextShowJ c j ++ "\n"

-- Structural rules

weaken :: Theorem -> Context -> Theorem
weaken (Theorem (ctx, j)) ctx'
  | ctx' `isExtensionOf` ctx = Theorem (ctx', j)
  | otherwise                = error "weaken: the second context is not an extension of the first one"

-- Formation rules

varMk :: Context -> String -> Theorem
varMk ctx id = case ctxLookup id ctx of
  Just (Type t) -> Theorem (ctx, HasType (Var (Free id)) t)
  _ -> error "varMk"

appMk :: Theorem -> Theorem -> Theorem
appMk (Theorem (ctx, HasType e1 (TFun l r))) (Theorem (ctx', HasType e2 l'))
  | ctx == ctx' && l == l' =
    Theorem (ctx, HasType (App e1 e2) r)
appMk _ _ = error "appMk"

lamMk :: Theorem -> Theorem
lamMk (Theorem (ctx,  HasType e te)) =
       Theorem (ctx', HasType (Lam x tx e') (TFun tx te))
  where (ctx', x, tx, e') = ctxPop ctx e
lamMk _ = error "lamMk"

-- Definition generalization rules (executed in context-changing rules)

ctxPop :: Context -> Expr -> (Context, String, Type, Expr)
ctxPop (Context (((name, hyp) : defs) : l' : ls)) e =
  case hyp of
    -- Add the definitions in the topmost layer into the second-to-top layer,
    -- adding abstraction over the hypothesized variable.
    (Type t) -> (Context ((l' ++ newdefs) : ls), name, t, modify e)
      where
        newdefs = map (\(name, Type t') -> (name, Type (TFun t t'))) defs
        ids = map fst defs -- The names of definitions in the last layer (excluding the hypothesized one)
        modify =
          updateVars 0 (\n x -> case x of
            (Free id)
              | id `elem` ids -> App (Var x) (Var (Bound n))
              | id == name    -> Var (Bound n)
            _                 -> Var x)
    -- Add the definitions in the topmost layer into the second-to-top layer,
    -- prepending the assumption to every theorem (not implemented here).
    _ -> (Context ((l' ++ defs) : ls), name, TVar, e)
ctxPop _ _ = error "ctxPop"
