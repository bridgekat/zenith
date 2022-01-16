-- Dependent type theory for experimentation

{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module LambdaPi where

import Data.List
import Data.Char
import Control.Monad


-- Contraction and permutation should be allowed, but currently they are not needed; weakening is stated below.
-- If there are naming clashes, later names will override
-- (TODO: hide this constructor when exporting)
newtype Context = Context [(String, Expr)]
  deriving (Eq)

instance Show Context where
  show (Context ls) = foldl (\acc (s, t) -> s ++ " : " ++ show t ++ "\n" ++ acc) "" ls

ctxList :: Context -> [(String, Expr)]
ctxList (Context ls) = ls

ctxEmpty :: Context
ctxEmpty = Context []

ctxVar :: String -> Theorem -> Context
ctxVar s (Theorem (Context ls, t, Sort _)) = Context ((s, t) : ls)
ctxVar _ _ = error "Illegal application of ctxVar"

-- Bound variables are represented using de Brujin indices
-- (0 = binds to the deepest binder, 1 = escapes one binder, and so on)
data VarName = Free String | Bound Int
  deriving (Eq)

data Expr =
    Var VarName
  | Sort Int
  | Pi String Expr Expr | Lam String Expr Expr | App Expr Expr
  -- | Eq Expr Expr | EqIntro Expr | EqElim ...
  -- | Unit | UnitIntro
  -- | Empty | EmptyElim ...
  -- | Sigma String Expr Expr | SigmaIntro ... | SigmaElim ...
  -- | Sum Expr Expr | SumInl Expr | SumInr Expr | SumElim ...

instance Eq Expr where
  (==) (Var x1)      (Var y1)      = x1 == y1
  (==) (Sort x1)     (Sort y1)     = x1 == y1
  (==) (Pi _ x1 x2)  (Pi _ y1 y2)  = x1 == y1 && x2 == y2
  (==) (Lam _ x1 x2) (Lam _ y1 y2) = x1 == y1 && x2 == y2
  (==) (App x1 x2)   (App y1 y2)   = x1 == y1 && x2 == y2
  (==) _             _             = False

newName :: String -> [String] -> String
newName x used
  | x `notElem` used    = x
  | otherwise           = newName (x ++ "'") used

showName :: [String] -> VarName -> String
showName stk (Free s)  = s
showName stk (Bound i) = stk !! i

showE :: [String] -> [String] -> Expr -> String
showE used stk e = case e of
  (Var x)       -> showName stk x
  (Sort n)      -> "Sort " ++ show n
  (Pi x e1 e2)  -> "(Π " ++ x' ++ " : " ++ showE used stk e1 ++ ", " ++ showE (x' : used) (x' : stk) e2 ++ ")" where x' = newName x used
  (Lam x e1 e2) -> "(λ " ++ x' ++ " : " ++ showE used stk e1 ++ ", " ++ showE (x' : used) (x' : stk) e2 ++ ")" where x' = newName x used
  (App e1 e2)   -> "(" ++ showE used stk e1 ++ " " ++ showE used stk e2 ++ ")"

inContextShowE :: Context -> Expr -> String
inContextShowE (Context ls) = showE (map fst ls) []

instance Show Expr where
  show = showE [] []

-- n = (number of binders on top of current node)
updateVars :: Int -> (Int -> VarName -> Expr) -> Expr -> Expr
updateVars n f e = case e of
  (Var x)       -> f n x
  (Sort n)      -> Sort n
  (Pi x e1 e2)  -> Pi x (updateVars n f e1) (updateVars (n + 1) f e2)
  (Lam x e1 e2) -> Lam x (updateVars n f e1) (updateVars (n + 1) f e2)
  (App e1 e2)   -> App (updateVars n f e1) (updateVars n f e2)

-- Replace occurrences of a free variable by a given term
-- Pre: t is a well-formed term
replaceVar :: String -> Expr -> Expr -> Expr
replaceVar s t = updateVars 0 (\_ x -> if x == Free s then t else Var x)

-- Note that the resulting expression is not well-formed until one additional layer of binder is added
makeBound :: String -> Expr -> Expr
makeBound s = updateVars 0 (\n x -> if x == Free s then Var (Bound n) else Var x)

-- Input expression can be a subexpression which is not well-formed by itself
makeFree :: String -> Expr -> Expr
makeFree s = updateVars 0 (\n x -> if x == Bound n then Var (Free s) else Var x)

-- Input expression can be a subexpression which is not well-formed by itself
makeReplace :: Expr -> Expr -> Expr
makeReplace t = updateVars 0 (\n x -> if x == Bound n then t else Var x)


-- `Context ⊢ (Expr : Type)` where the second expression is in its normal form
type Judgment = (Context, Expr, Expr)

-- (TODO: hide this constructor when exporting)
newtype Theorem = Theorem Judgment

thmJudgment :: Theorem -> Judgment
thmJudgment (Theorem j) = j

thmContext :: Theorem -> Context
thmContext (Theorem (c, _, _)) = c

thmExpr :: Theorem -> Expr
thmExpr (Theorem (_, e, _)) = e

thmType :: Theorem -> Expr
thmType (Theorem (_, _, t)) = t

instance Show Theorem where
  show (Theorem (c, e, t)) = "\n" ++ show c ++ "\n|- " ++ show e ++ " : " ++ show t ++ "\n"


weaken :: Theorem -> Context -> Theorem
weaken (Theorem (ctx, e, t)) ctx' =
  if ctxList ctx `isSuffixOf` ctxList ctx' then
    Theorem (ctx', e, t)
  else
    error "Illegal application of weakening"

-- Formation rules

varMk :: Context -> String -> Theorem
varMk (Context ls) s = case lookup s ls of
  (Just t) -> Theorem (Context ls, Var (Free s), t)
  Nothing  -> error ("Unknown identifier: " ++ s)

sortMk :: Int -> Theorem
sortMk n = Theorem (ctxEmpty, Sort n, Sort (n + 1))

{-
Π-formation:
If   `Γ          ⊢ (α               : Sort m)`
     `Γ, (x : α) ⊢ (β(x)            : Sort n)`
Then `Γ          ⊢ (Π (x : α), β(x) : Sort (max m n))`
-}

piMk :: Theorem -> Theorem -> Theorem
piMk (Theorem (Context ls,              α,                      Sort m))
     (Theorem (Context ((x, α') : ls'), β,                      Sort n))
     | ls == ls' && α == α' =
      Theorem (Context ls,              Pi x α (makeBound x β), Sort (max m n))
piMk _ _ = error "Illegal application of piMk"

-- Introduction rules

{-
Π-introduction:
If   `Γ, (x : α) ⊢ (b(x) : β(x))`
Then `Γ          ⊢ (λ (x : α), b(x) : Π (x : α), β(x))`
-}

piIntro :: Theorem -> Theorem
piIntro (Theorem (Context ((x, α) : ls), b,                       β)) =
         Theorem (Context ls,            Lam x α (makeBound x b), Pi x α (makeBound x β))
piIntro _ = error "Illegal application of piIntro"

-- Elimination rules

{-
Π-elimination:
If   `Γ          ⊢ (f : Π (x : α), β(x))`
     `Γ          ⊢ (a : α)`
Then `Γ          ⊢ (f a : β(a))`
-}

piElim :: Theorem -> Theorem -> Theorem
piElim (Theorem (ctx,  f, Pi x α β))
       (Theorem (ctx', a, α'))
       | ctx == ctx' && α == α' =
        Theorem (ctx, App f a, makeReplace a β)
piElim _ _ = error "Illegal application of piElim"

-- Computation (reduction) rules

{-
Π-computation (β-reduction):
If   `Γ          ⊢ ((λ (x : α), t(x)) a : β)`
Then `Γ          ⊢ (t(a) : β)`
-}

beta :: Theorem -> Theorem
beta (Theorem (ctx, App (Lam x α t) a, β)) =
      Theorem (ctx, makeReplace a t, β)
beta t = t


