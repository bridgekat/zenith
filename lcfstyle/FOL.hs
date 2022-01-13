-- ApiMu/FOL verifier v0.1 (Haskell version)
-- Licensed under Creative Commons CC0 (no copyright reserved, use at your will)

-- This variant of FOL & ND is largely based on Dirk van Dalen's *Logic and Structure*...
-- Additional features are described in `notes/design.md`.

module FOL where

import Data.Map (Map, union, unions)
import qualified Data.Map as Map


-- TODO: locally nameless variables
data Term =
    Var String
  | Func String [Term]
  deriving (Eq)

showT :: Term -> String
showT (Var x) = x
showT (Func x as) = "(" ++ x ++ concatMap ((" " ++) . showT) as ++ ")"

instance Show Term where
  show = showT

data Formula =
    Pred String [Term]
  | Equals Term Term
  | Top
  | Bottom
  | Not Formula
  | And Formula Formula
  | Or Formula Formula
  | Implies Formula Formula
  | Iff Formula Formula
  | Forall String Formula
  | Exists String Formula
  | Unique String Formula
-- | ForallFunc String Int Formula
-- | ForallPred String Int Formula
  deriving (Eq)

showF :: Formula -> String
showF (Pred x as) = "(" ++ x ++ concatMap ((" " ++) . showT) as ++ ")"
showF (Equals t1 t2) = "(" ++ showT t1 ++ " = " ++ showT t2 ++ ")"
showF Top = "true"
showF Bottom = "false"
showF (Not e) = "not " ++ showF e
showF (And e1 e2) = "(" ++ showF e1 ++ " and " ++ showF e2 ++ ")"
showF (Or e1 e2) = "(" ++ showF e1 ++ " or " ++ showF e2 ++ ")"
showF (Implies e1 e2) = "(" ++ showF e1 ++ " implies " ++ showF e2 ++ ")"
showF (Iff e1 e2) = "(" ++ showF e1 ++ " iff " ++ showF e2 ++ ")"
showF (Forall x e) = "(forall " ++ x ++ ", " ++ showF e ++ ")"
showF (Exists x e) = "(exists " ++ x ++ ", " ++ showF e ++ ")"
showF (Unique x e) = "(unique " ++ x ++ ", " ++ showF e ++ ")"
-- showF (ForallFunc x k e) = "(forallfunc " ++ x ++ "/" ++ show k ++ ", " ++ showF e ++ ")"
-- showF (ForallPred x k e) = "(forallpred " ++ x ++ "/" ++ show k ++ ", " ++ showF e ++ ")"

instance Show Formula where
  show = showF

{-
replaceVarT :: Term -> String -> Term -> Term
replaceVarT a x t = case a of
  (Var x')
    | x == x'   -> t
    | otherwise -> a

-}


data Type =
    TVar
  | TFunc Int
  | TPred Int
  | TProp Formula
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
    IsTerm Term
  | IsFormula Formula
  | IsSchema Formula
  | Provable Formula
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
    | t == TVar -> Theorem (ctx, IsTerm (Var id))

funcMk :: Context -> String -> [Theorem] -> Theorem
funcMk ctx id js = case Map.lookup id (ctxMap ctx) of
  (Just t)
    | t == TFunc (length as) && all (== ctx) ctxs ->
        Theorem (ctx, IsTerm (Func id as))
    where
      (ctxs, as) = unzip . map (\x -> let Theorem (c, IsTerm t) = x in (c, t)) $ js

predMk :: Context -> String -> [Theorem] -> Theorem
predMk ctx id js = case Map.lookup id (ctxMap ctx) of
  (Just t)
    | t == TPred (length as) && all (== ctx) ctxs ->
        Theorem (ctx, IsFormula (Pred id as))
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
    Just TVar -> Theorem (Context (Map.delete id map), IsFormula (Forall id e))

existsMk :: String -> Theorem -> Theorem
existsMk id (Theorem (Context map, IsFormula e)) =
  case Map.lookup id map of
    Just TVar -> Theorem (Context (Map.delete id map), IsFormula (Exists id e))

uniqueMk :: String -> Theorem -> Theorem
uniqueMk id (Theorem (Context map, IsFormula e)) =
  case Map.lookup id map of
    Just TVar -> Theorem (Context (Map.delete id map), IsFormula (Unique id e))

{-
schemaMk :: Theorem -> Theorem
schemaMk (Theorem (ctx, IsFormula e)) =
  Theorem (ctx, IsSchema e)

forallfuncMk :: String -> Theorem -> Theorem
forallfuncMk id (Theorem (Context map, IsSchema e)) =
  case Map.lookup id map of
    Just (TFunc k) -> Theorem (Context (Map.delete id map), IsSchema (ForallFunc id k e))

forallpredMk :: String -> Theorem -> Theorem
forallpredMk id (Theorem (Context map, IsSchema e)) =
  case Map.lookup id map of
    Just (TPred k) -> Theorem (Context (Map.delete id map), IsSchema (ForallPred id k e))
-}


-- Inference rules
-- Pre & post: `Provable ctx p` => `IsFormula ctx p`

assumption :: Context -> String -> Theorem -> Theorem
assumption ctx id (Theorem (ctx', IsFormula p))
  | ctx == ctx' && Map.lookup id (ctxMap ctx) == Just (TProp p) =
      Theorem (ctx, Provable p)

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
    (Just TVar) -> Theorem (Context map', Provable (Forall id p))
    _           -> Theorem (Context map, Provable p)
  where
    t' = Map.lookup id map
    map' = Map.delete id map

forallElim :: Theorem -> Theorem -> Theorem
forallElim (Theorem (ctx,  Provable (Forall x q)))
           (Theorem (ctx', IsTerm t))
           | ctx == ctx' =
            Theorem (ctx,  Provable undefined {- ... -})


