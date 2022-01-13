-- ApiMu/FOL verifier v0.1 (Haskell version)
-- Licensed under Creative Commons CC0 (no copyright reserved, use at your will)

-- This variant of FOL & ND is largely based on Dirk van Dalen's *Logic and Structure*...
-- Additional features are described in `notes/design.md`.

module FOL where

import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map, union, unions)
import qualified Data.Map as Map


-- Bound variables are represented using de Brujin indices
-- (0 = binds to the deepest binder, 1 = escapes one binder, and so on)
data VarName = Free String | Bound Int
  deriving (Eq)

data Expr =
    Var VarName
  | Func VarName [Expr]
  | Pred VarName [Expr]
  | Equals Expr Expr
  | Top
  | Bottom
  | Not Expr
  | And Expr Expr
  | Or Expr Expr
  | Implies Expr Expr
  | Iff Expr Expr
  | Forall String Expr
  | Exists String Expr
  | Unique String Expr
-- | ForallFunc String Int Expr
-- | ForallPred String Int Expr
  deriving (Eq)

newName :: String -> Set String -> String
newName x used
  | Set.notMember x used = x
  | otherwise            = newName (x ++ "'") used

showName :: [String] -> VarName -> String
showName st (Free s)  = s
showName st (Bound i) = st !! i

showE :: Set String -> [String] -> Expr -> String
showE used st e = case e of
  (Var x) -> showName st x
  (Func x as) -> "(" ++ showName st x ++ concatMap ((" " ++) . showE used st) as ++ ")"
  (Pred x as) -> "(" ++ showName st x ++ concatMap ((" " ++) . showE used st) as ++ ")"
  (Equals t1 t2) -> "(" ++ showE used st t1 ++ " = " ++ showE used st t2 ++ ")"
  Top -> "true"
  Bottom -> "false"
  (Not e) -> "not " ++ showE used st e
  (And e1 e2) -> "(" ++ showE used st e1 ++ " and " ++ showE used st e2 ++ ")"
  (Or e1 e2) -> "(" ++ showE used st e1 ++ " or " ++ showE used st e2 ++ ")"
  (Implies e1 e2) -> "(" ++ showE used st e1 ++ " implies " ++ showE used st e2 ++ ")"
  (Iff e1 e2) -> "(" ++ showE used st e1 ++ " iff " ++ showE used st e2 ++ ")"
  (Forall x e) -> "(forall " ++ x' ++ ", " ++ showE (Set.insert x' used) (x' : st) e ++ ")" where x' = newName x used
  (Exists x e) -> "(exists " ++ x' ++ ", " ++ showE (Set.insert x' used) (x' : st) e ++ ")" where x' = newName x used
  (Unique x e) -> "(unique " ++ x' ++ ", " ++ showE (Set.insert x' used) (x' : st) e ++ ")" where x' = newName x used
-- (ForallFunc x k e) -> "(forallfunc " ++ x ++ "/" ++ show k ++ ", " ++ showE (x : st) e ++ ")"
-- (ForallPred x k e) -> "(forallpred " ++ x ++ "/" ++ show k ++ ", " ++ showE (x : st) e ++ ")"

inContextShowE :: Context -> Expr -> String
inContextShowE (Context map) = showE (Map.keysSet map) []

instance Show Expr where
  show = showE Set.empty []

-- n = (number of binders on top of current node)
updateVars :: Int -> (Int -> VarName -> Expr) -> Expr -> Expr
updateVars n f e = case e of
  (Var x) -> f n x
  (Func x es) -> Func x (map (updateVars n f) es)
  (Pred x es) -> Pred x (map (updateVars n f) es)
  (Equals e1 e2) -> Equals (updateVars n f e1) (updateVars n f e2)
  Top -> e
  Bottom -> e
  (Not e1) -> Not (updateVars n f e1)
  (And e1 e2) -> And (updateVars n f e1) (updateVars n f e2)
  (Or e1 e2) -> Or (updateVars n f e1) (updateVars n f e2)
  (Implies e1 e2) -> Implies (updateVars n f e1) (updateVars n f e2)
  (Iff e1 e2) -> Iff (updateVars n f e1) (updateVars n f e2)
  (Forall x e1) -> Forall x (updateVars (n + 1) f e1)
  (Exists x e1) -> Exists x (updateVars (n + 1) f e1)
  (Unique x e1) -> Unique x (updateVars (n + 1) f e1)

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


data Type =
    TVar
  | TFunc Int
  | TPred Int
  | TProp Expr
  deriving (Eq, Show)

-- Assuming structural rules: contraction and permutation; weakening is stated below
-- If there are naming clashes, later names will override
-- (TODO: hide this constructor when exporting)
newtype Context = Context (Map String Type)
  deriving (Eq, Show)

ctxMap :: Context -> Map String Type
ctxMap (Context map) = map

ctxEmpty :: Context
ctxEmpty = Context Map.empty

ctxVar :: String -> Context -> Context
ctxVar id (Context ctx) = Context (Map.insert id TVar ctx)

ctxFunc :: String -> Int -> Context -> Context
ctxFunc id arity (Context ctx) = Context (Map.insert id (TFunc arity) ctx)

ctxPred :: String -> Int -> Context -> Context
ctxPred id arity (Context ctx) = Context (Map.insert id (TPred arity) ctx)

ctxAssumption :: String -> Theorem -> Context -> Context
ctxAssumption id (Theorem (Context ctx', IsFormula p)) (Context ctx)
  | ctx == ctx' = Context (Map.insert id (TProp p) ctx)


data Judgment =
    IsTerm Expr
  | IsFormula Expr
  | IsSchema Expr
  | Provable Expr
  deriving (Eq, Show)

-- (TODO: hide this constructor when exporting)
newtype Theorem = Theorem (Context, Judgment)

thmContext :: Theorem -> Context
thmContext (Theorem (c, _)) = c

thmJudgment :: Theorem -> Judgment
thmJudgment (Theorem (_, j)) = j


weaken :: Theorem -> Context -> Theorem
weaken (Theorem (ctx, j)) ctx' =
  case isSubset of
    True -> Theorem (ctx', j)
  where
    isSubset = Map.foldlWithKey (\acc k v -> acc && Map.lookup k (ctxMap ctx') == Just v) True (ctxMap ctx)

-- Formation rules (as in `notes/design.md`)

varMk :: Context -> String -> Theorem
varMk ctx id = case Map.lookup id (ctxMap ctx) of
  (Just t)
    | t == TVar -> Theorem (ctx, IsTerm (Var (Free id)))

funcMk :: Context -> String -> [Theorem] -> Theorem
funcMk ctx id js = case Map.lookup id (ctxMap ctx) of
  (Just t)
    | t == TFunc (length as) && all (== ctx) ctxs ->
        Theorem (ctx, IsTerm (Func (Free id) as))
    where
      (ctxs, as) = unzip . map (\x -> let Theorem (c, IsTerm t) = x in (c, t)) $ js

predMk :: Context -> String -> [Theorem] -> Theorem
predMk ctx id js = case Map.lookup id (ctxMap ctx) of
  (Just t)
    | t == TPred (length as) && all (== ctx) ctxs ->
        Theorem (ctx, IsFormula (Pred (Free id) as))
    where
      (ctxs, as) = unzip . map (\x -> let Theorem (c, IsTerm t) = x in (c, t)) $ js

eqMk :: Theorem -> Theorem -> Theorem
eqMk (Theorem (ctx, IsTerm t1)) (Theorem (ctx', IsTerm t2))
  | ctx == ctx' = Theorem (ctx, IsFormula (Equals t1 t2))

topMk :: Theorem
topMk = Theorem (ctxEmpty, IsFormula Top)

bottomMk :: Theorem
bottomMk = Theorem (ctxEmpty, IsFormula Bottom)

notMk :: Theorem -> Theorem
notMk (Theorem (ctx, IsFormula e)) =
  Theorem (ctx, IsFormula (Not e))

andMk :: Theorem -> Theorem -> Theorem
andMk (Theorem (ctx, IsFormula e1)) (Theorem (ctx', IsFormula e2))
  | ctx == ctx' = Theorem (ctx, IsFormula (And e1 e2))

orMk :: Theorem -> Theorem -> Theorem
orMk (Theorem (ctx, IsFormula e1)) (Theorem (ctx', IsFormula e2))
  | ctx == ctx' = Theorem (ctx, IsFormula (Or e1 e2))

impliesMk :: Theorem -> Theorem -> Theorem
impliesMk (Theorem (ctx, IsFormula e1)) (Theorem (ctx', IsFormula e2))
  | ctx == ctx' = Theorem (ctx, IsFormula (Implies e1 e2))

iffMk :: Theorem -> Theorem -> Theorem
iffMk (Theorem (ctx, IsFormula e1)) (Theorem (ctx', IsFormula e2))
  | ctx == ctx' = Theorem (ctx, IsFormula (Iff e1 e2))

forallMk :: String -> Theorem -> Theorem
forallMk id (Theorem (Context map, IsFormula e)) =
  case Map.lookup id map of
    Just TVar -> Theorem (Context (Map.delete id map), IsFormula (Forall id (makeBound id e)))

existsMk :: String -> Theorem -> Theorem
existsMk id (Theorem (Context map, IsFormula e)) =
  case Map.lookup id map of
    Just TVar -> Theorem (Context (Map.delete id map), IsFormula (Exists id (makeBound id e)))

uniqueMk :: String -> Theorem -> Theorem
uniqueMk id (Theorem (Context map, IsFormula e)) =
  case Map.lookup id map of
    Just TVar -> Theorem (Context (Map.delete id map), IsFormula (Unique id (makeBound id e)))

{-
schemaMk :: Theorem -> Theorem
schemaMk (Theorem (ctx, IsFormula e)) =
  Theorem (ctx, IsSchema e)

forallfuncMk :: String -> Theorem -> Theorem
forallfuncMk id (Theorem (Context map, IsSchema e)) =
  case Map.lookup id map of
    Just (TFunc k) -> Theorem (Context (Map.delete id map), IsSchema (ForallFunc id k undefined))

forallpredMk :: String -> Theorem -> Theorem
forallpredMk id (Theorem (Context map, IsSchema e)) =
  case Map.lookup id map of
    Just (TPred k) -> Theorem (Context (Map.delete id map), IsSchema (ForallPred id k undefined))
-}


-- Inference rules
-- Pre & post: `Provable ctx p` => `IsFormula ctx p`

assumption :: Context -> String -> Theorem
assumption ctx id =
  case Map.lookup id (ctxMap ctx) of
    Just (TProp p) -> Theorem (ctx, Provable p)

andIntro :: Theorem -> Theorem -> Theorem
andIntro (Theorem (ctx,  Provable p))
         (Theorem (ctx', Provable q))
         | ctx == ctx' =
          Theorem (ctx,  Provable (And p q)) 

andLeft :: Theorem -> Theorem
andLeft (Theorem (ctx, Provable (And p q))) =
         Theorem (ctx, Provable p) 

andRight :: Theorem -> Theorem
andRight (Theorem (ctx, Provable (And p q))) =
          Theorem (ctx, Provable q)

orInl :: Theorem -> Theorem -> Theorem
orInl (Theorem (ctx,  Provable p))
      (Theorem (ctx', IsFormula q))
      | ctx == ctx' =
       Theorem (ctx,  Provable (Or p q))

orInr :: Theorem -> Theorem -> Theorem
orInr (Theorem (ctx,  IsFormula p))
      (Theorem (ctx', Provable q))
      | ctx == ctx' =
       Theorem (ctx,  Provable (Or p q))

orElim :: Theorem -> Theorem -> Theorem -> Theorem
orElim (Theorem (ctx,   Provable (Or p q)))
       (Theorem (ctx',  Provable (Implies p' r)))
       (Theorem (ctx'', Provable (Implies q' r')))
       | ctx == ctx' && ctx == ctx'' && p == p' && q == q' && r == r' =
        Theorem (ctx,   Provable r)

impliesIntro :: Theorem -> String -> Theorem
impliesIntro (Theorem (Context map, Provable q)) id =
  case p' of
    (Just (TProp p)) -> Theorem (Context map', Provable (Implies p q))
    _                -> Theorem (Context map, Provable q)
  where
    p' = Map.lookup id map
    map' = Map.delete id map

impliesElim :: Theorem -> Theorem -> Theorem
impliesElim (Theorem (ctx,  Provable (Implies p q)))
            (Theorem (ctx', Provable p'))
            | ctx == ctx' && p == p' =
             Theorem (ctx,  Provable q)

-- ...

forallIntro :: Theorem -> String -> Theorem
forallIntro (Theorem (Context map, Provable p)) id =
  case t' of
    (Just TVar) -> Theorem (Context map', Provable (Forall id (makeBound id p)))
    _           -> Theorem (Context map, Provable p)
  where
    t' = Map.lookup id map
    map' = Map.delete id map

forallElim :: Theorem -> Theorem -> Theorem
forallElim (Theorem (ctx,  Provable (Forall x q)))
           (Theorem (ctx', IsTerm t))
           | ctx == ctx' =
            Theorem (ctx,  Provable (makeReplace t q))


