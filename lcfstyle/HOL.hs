-- Simple type theory / higher-order logic for experimentation
-- This variant of HOL is largely based on William M. Farmer's *The Seven Virtues of Simple Type Theory*...

-- {-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module HOL where

import Data.List


-- Contraction and permutation should be allowed, but currently they are not needed; weakening is stated below.
-- If there are naming clashes, later names will override
-- (TODO: hide this constructor when exporting)
newtype Context = Context [(String, Type)]
  deriving (Eq)

instance Show Context where
  show (Context ls) = foldl (\acc (id, t) -> id ++ " : " ++ show t ++ "\n" ++ acc) "" ls

ctxList :: Context -> [(String, Type)]
ctxList (Context ls) = ls

ctxEmpty :: Context
ctxEmpty = Context []

ctxVar :: (String, Type) -> Context -> Context
ctxVar (id, t) (Context ctx) = Context ((id, t) : ctx)

-- Bound variables are represented using de Brujin indices
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
    Var VarName
  | App Expr Expr
  | Lam String Type Expr
  | Eq Expr Expr
  | Iota String Type Expr

-- Ignore the names of bound variables when comparing
instance Eq Expr where
  (==) (Var x1)       (Var y1)       = x1 == y1
  (==) (App x1 x2)    (App y1 y2)    = x1 == y1 && x2 == y2
  (==) (Lam _ x1 x2)  (Lam _ y1 y2)  = x1 == y1 && x2 == y2
  (==) (Eq x1 x2)     (Eq y1 y2)     = x1 == y1 && x2 == y2
  (==) (Iota _ x1 x2) (Iota _ y1 y2) = x1 == y1 && x2 == y2
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
  (Var x)      -> showName stk x
  (App e1 e2)  -> "(" ++ showE used stk e1 ++ " " ++ showE used stk e2 ++ ")"
  (Lam x t e)  -> "(λ " ++ x' ++ " : " ++ showT t ++ ", " ++ showE (x' : used) (x' : stk) e ++ ")" where x' = newName x used
  (Eq e1 e2)   -> "(" ++ showE used stk e1 ++ " = " ++ showE used stk e2 ++ ")"
  (Iota x t e) -> "(I " ++ x' ++ " : " ++ showT t ++ ", " ++ showE (x' : used) (x' : stk) e ++ ")" where x' = newName x used

inContextShowE :: Context -> Expr -> String
inContextShowE (Context ls) = showE (map fst ls) []

instance Show Expr where
  show = showE [] []

-- n = (number of binders on top of current node)
updateVars :: Int -> (Int -> VarName -> Expr) -> Expr -> Expr
updateVars n f e = case e of
  (Var x)      -> f n x
  (App e1 e2)  -> App (updateVars n f e1) (updateVars n f e2)
  (Lam x t e)  -> Lam x t (updateVars (n + 1) f e)
  (Eq e1 e2)   -> Eq (updateVars n f e1) (updateVars n f e2)
  (Iota x t e) -> Iota x t (updateVars (n + 1) f e)

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


-- `Context ⊢ (Expr : Type)`
type Judgment = (Context, Expr, Type)

-- (TODO: hide this constructor when exporting)
newtype Theorem = Theorem Judgment

thmJudgment :: Theorem -> Judgment
thmJudgment (Theorem j) = j

thmContext :: Theorem -> Context
thmContext (Theorem (c, _, _)) = c

thmExpr :: Theorem -> Expr
thmExpr (Theorem (_, e, _)) = e

thmType :: Theorem -> Type
thmType (Theorem (_, _, t)) = t

instance Show Theorem where
  show (Theorem (c, e, t)) = "\n" ++ show c ++ "\n|- " ++ show e ++ " : " ++ show t ++ "\n"


weaken :: Theorem -> Context -> Theorem
weaken (Theorem (ctx, e, t)) ctx' =
  case ctxList ctx `isSuffixOf` ctxList ctx' of
    True -> Theorem (ctx', e, t)

-- Formation rules

varMk :: Context -> String -> Theorem
varMk (Context ls) s = case lookup s ls of
  (Just t) -> Theorem (Context ls, Var (Free s), t)

appMk :: Theorem -> Theorem -> Theorem
appMk (Theorem (ctx, e1, TFun l r)) (Theorem (ctx', e2, l'))
  | ctx == ctx' && l == l' =
    Theorem (ctx, App e1 e2, r)

lamMk :: Theorem -> Theorem
lamMk (Theorem (Context ((x, tx) : ls), e, te)) =
  Theorem (Context ls, Lam x tx (makeBound x e), TFun tx te)

eqMk :: Theorem -> Theorem -> Theorem
eqMk (Theorem (ctx, e1, t1)) (Theorem (ctx', e2, t2))
  | ctx == ctx' && t1 == t2 =
    Theorem (ctx, Eq e1 e2, TProp)

iotaMk :: Theorem -> Theorem
iotaMk (Theorem (Context ((x, tx) : ls), e, te)) =
  Theorem (Context ls, Iota x tx (makeBound x e), tx)

-- TODO: inference rules

-- eqSubst :: Theorem -> Expr -> Theorem

