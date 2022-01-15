-- ApiMu/FOL verifier v0.1 (Haskell version)
-- Licensed under Creative Commons CC0 (no copyright reserved, use at your will)

-- This variant of FOL & ND is largely based on Dirk van Dalen's *Logic and Structure*...
-- To keep in line with the proof language, some context-changing rules are now represented in terms of
-- `impliesIntro` and `forallIntro`; Additional features are described in `notes/design.md`.

-- {-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module FOL where

import Data.List


-- Bound variables are represented using de Brujin indices
-- (0 = binds to the deepest binder, 1 = escapes one binder, and so on)
data VarName = Free String | Bound Int
  deriving (Eq)

data Expr =
    Var VarName
  | Func VarName [Expr]
  | Pred VarName [Expr]
  | Eq Expr Expr --
  | Top    -- To avoid naming clashes I did not use `True` here
  | Bottom -- Also here
  | Not Expr
  | And Expr Expr
  | Or Expr Expr
  | Implies Expr Expr
  | Iff Expr Expr
  | Forall String Expr
  | Exists String Expr
  | Unique String Expr --
-- | ForallFunc String Int Expr
-- | ForallPred String Int Expr

-- Ignore the names of bound variables when comparing
instance Eq Expr where
  (==) (Var x1)        (Var y1)        = x1 == y1
  (==) (Func x1 x2)    (Func y1 y2)    = x1 == y1 && x2 == y2
  (==) (Pred x1 x2)    (Pred y1 y2)    = x1 == y1 && x2 == y2
  (==) (Eq x1 x2)      (Eq y1 y2)      = x1 == y1 && x2 == y2
  (==) Top             Top             = True
  (==) Bottom          Bottom          = True
  (==) (Not x1)        (Not y1)        = x1 == y1
  (==) (And x1 x2)     (And y1 y2)     = x1 == y1 && x2 == y2
  (==) (Or x1 x2)      (Or y1 y2)      = x1 == y1 && x2 == y2
  (==) (Implies x1 x2) (Implies y1 y2) = x1 == y1 && x2 == y2
  (==) (Iff x1 x2)     (Iff y1 y2)     = x1 == y1 && x2 == y2
  (==) (Forall _ x1)   (Forall _ y1)   = x1 == y1
  (==) (Exists _ x1)   (Exists _ y1)   = x1 == y1
  (==) (Unique _ x1)   (Unique _ y1)   = x1 == y1
  (==) _               _               = False

newName :: String -> [String] -> String
newName x used
  | x `notElem` used = x
  | otherwise        = newName (x ++ "'") used

showName :: [String] -> VarName -> String
showName stk (Free s)  = s
showName stk (Bound i) = stk !! i

showE :: [String] -> [String] -> Expr -> String
showE used stk e = case e of
  (Var x) -> showName stk x
  (Func x as) -> "(" ++ showName stk x ++ concatMap ((" " ++) . showE used stk) as ++ ")"
  (Pred x as) -> "(" ++ showName stk x ++ concatMap ((" " ++) . showE used stk) as ++ ")"
  (Eq t1 t2) -> "(" ++ showE used stk t1 ++ " = " ++ showE used stk t2 ++ ")"
  Top -> "true"
  Bottom -> "false"
  (Not e) -> "not " ++ showE used stk e
  (And e1 e2) -> "(" ++ showE used stk e1 ++ " and " ++ showE used stk e2 ++ ")"
  (Or e1 e2) -> "(" ++ showE used stk e1 ++ " or " ++ showE used stk e2 ++ ")"
  (Implies e1 e2) -> "(" ++ showE used stk e1 ++ " implies " ++ showE used stk e2 ++ ")"
  (Iff e1 e2) -> "(" ++ showE used stk e1 ++ " iff " ++ showE used stk e2 ++ ")"
  (Forall x e) -> "(forall " ++ x' ++ ", " ++ showE (x' : used) (x' : stk) e ++ ")" where x' = newName x used
  (Exists x e) -> "(exists " ++ x' ++ ", " ++ showE (x' : used) (x' : stk) e ++ ")" where x' = newName x used
  (Unique x e) -> "(unique " ++ x' ++ ", " ++ showE (x' : used) (x' : stk) e ++ ")" where x' = newName x used
-- (ForallFunc x k e) -> "(forallfunc " ++ x ++ "/" ++ show k ++ ", " ++ showE (x : stk) e ++ ")"
-- (ForallPred x k e) -> "(forallpred " ++ x ++ "/" ++ show k ++ ", " ++ showE (x : stk) e ++ ")"

inContextShowE :: Context -> Expr -> String
inContextShowE (Context ls) = showE (map fst ls) []

instance Show Expr where
  show = showE [] []

-- n = (number of binders on top of current node)
updateVars :: Int -> (Int -> VarName -> Expr) -> Expr -> Expr
updateVars n f e = case e of
  (Var x) -> f n x
  (Func x es) -> Func x (map (updateVars n f) es)
  (Pred x es) -> Pred x (map (updateVars n f) es)
  (Eq e1 e2) -> Eq (updateVars n f e1) (updateVars n f e2)
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
  | THyp Expr
  deriving (Eq, Show)

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

ctxVar :: String -> Context -> Context
ctxVar id (Context ctx) = Context ((id, TVar) : ctx)

ctxFunc :: String -> Int -> Context -> Context
ctxFunc id arity (Context ctx) = Context ((id, TFunc arity) : ctx)

ctxPred :: String -> Int -> Context -> Context
ctxPred id arity (Context ctx) = Context ((id, TPred arity) : ctx)

ctxAssumption :: String -> Theorem -> Context
ctxAssumption id (Theorem (Context ctx, IsFormula p)) = Context ((id, THyp p) : ctx)


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

instance Show Theorem where
  show (Theorem (c, j)) = "\n" ++ show c ++ "\n|- " ++ show j ++ "\n"


weaken :: Theorem -> Context -> Theorem
weaken (Theorem (ctx, j)) ctx' =
  case ctxList ctx `isSuffixOf` ctxList ctx' of
    True -> Theorem (ctx', j)

-- Formation rules (as in `notes/design.md`)

varMk :: Context -> String -> Theorem
varMk ctx id = case lookup id (ctxList ctx) of
  (Just t)
    | t == TVar -> Theorem (ctx, IsTerm (Var (Free id)))

funcMk :: Context -> String -> [Theorem] -> Theorem
funcMk ctx id js = case lookup id (ctxList ctx) of
  (Just t)
    | t == TFunc (length as) && all (== ctx) ctxs ->
        Theorem (ctx, IsTerm (Func (Free id) as))
    where
      (ctxs, as) = unzip . map (\x -> let Theorem (c, IsTerm t) = x in (c, t)) $ js

predMk :: Context -> String -> [Theorem] -> Theorem
predMk ctx id js = case lookup id (ctxList ctx) of
  (Just t)
    | t == TPred (length as) && all (== ctx) ctxs ->
        Theorem (ctx, IsFormula (Pred (Free id) as))
    where
      (ctxs, as) = unzip . map (\x -> let Theorem (c, IsTerm t) = x in (c, t)) $ js

eqMk :: Theorem -> Theorem -> Theorem
eqMk (Theorem (ctx, IsTerm t1)) (Theorem (ctx', IsTerm t2))
  | ctx == ctx' = Theorem (ctx, IsFormula (Eq t1 t2))

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

forallMk :: Theorem -> Theorem
forallMk (Theorem (Context ((id, TVar) : ls), IsFormula e)) =
  Theorem (Context ls, IsFormula (Forall id (makeBound id e)))

existsMk :: Theorem -> Theorem
existsMk (Theorem (Context ((id, TVar) : ls), IsFormula e)) =
  Theorem (Context ls, IsFormula (Exists id (makeBound id e)))

uniqueMk :: Theorem -> Theorem
uniqueMk (Theorem (Context ((id, TVar) : ls), IsFormula e)) =
  Theorem (Context ls, IsFormula (Unique id (makeBound id e)))


-- Introduction & elimination rules
-- Pre & post: `Provable ctx p` => `IsFormula ctx p`

assumption :: Context -> String -> Theorem
assumption ctx id =
  case lookup id (ctxList ctx) of
    Just (THyp p) -> Theorem (ctx, Provable p)

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

orLeft :: Theorem -> Theorem -> Theorem
orLeft (Theorem (ctx,  Provable p))
       (Theorem (ctx', IsFormula q))
       | ctx == ctx' =
        Theorem (ctx,  Provable (Or p q))

orRight :: Theorem -> Theorem -> Theorem
orRight (Theorem (ctx,  IsFormula p))
        (Theorem (ctx', Provable q))
        | ctx == ctx' =
         Theorem (ctx,  Provable (Or p q))

orElim :: Theorem -> Theorem -> Theorem -> Theorem
orElim (Theorem (ctx,   Provable (Or p q)))
       (Theorem (ctx',  Provable (p' `Implies` r)))
       (Theorem (ctx'', Provable (q' `Implies` r')))
       | ctx == ctx' && ctx == ctx'' && p == p' && q == q' && r == r' =
        Theorem (ctx,   Provable r)

-- (Context-changing rule)
impliesIntro :: Theorem -> Theorem
impliesIntro (Theorem (Context ((_, THyp p) : ls), Provable q)) =
              Theorem (Context ls, Provable (p `Implies` q))

impliesElim :: Theorem -> Theorem -> Theorem
impliesElim (Theorem (ctx,  Provable (p `Implies` q)))
            (Theorem (ctx', Provable p'))
            | ctx == ctx' && p == p' =
             Theorem (ctx,  Provable q)

notIntro :: Theorem -> Theorem
notIntro (Theorem (ctx, Provable (p `Implies` Bottom))) =
          Theorem (ctx, Provable (Not p))

notElim :: Theorem -> Theorem -> Theorem
notElim (Theorem (ctx,  Provable (Not p)))
        (Theorem (ctx', Provable p'))
        | ctx == ctx' && p == p' =
         Theorem (ctx,  Provable Bottom)

iffIntro :: Theorem -> Theorem -> Theorem
iffIntro (Theorem (ctx,  Provable (p `Implies` q)))
         (Theorem (ctx', Provable (q' `Implies` p')))
         | ctx == ctx' && p == p' && q == q' =
          Theorem (ctx,  Provable (p `Iff` q))

iffLeft :: Theorem -> Theorem -> Theorem
iffLeft (Theorem (ctx,  Provable (p `Iff` q)))
        (Theorem (ctx', Provable p'))
        | ctx == ctx' && p == p' =
         Theorem (ctx,  Provable q)

iffRight :: Theorem -> Theorem -> Theorem
iffRight (Theorem (ctx,  Provable (p `Iff` q)))
         (Theorem (ctx', Provable q'))
         | ctx == ctx' && q == q' =
          Theorem (ctx,  Provable p)

trueIntro :: Theorem
trueIntro = Theorem (ctxEmpty, Provable Top)

falseElim :: Theorem -> Theorem -> Theorem
falseElim (Theorem (ctx,  Provable Bottom))
          (Theorem (ctx', IsFormula p))
          | ctx == ctx' =
           Theorem (ctx,  Provable p)

raa :: Theorem -> Theorem
raa (Theorem (ctx, Provable (Not p `Implies` Bottom))) =
     Theorem (ctx, Provable p)

-- (Context-changing rule)
forallIntro :: Theorem -> Theorem
forallIntro (Theorem (Context ((id, TVar) : ls), Provable p)) =
             Theorem (Context ls, Provable (Forall id (makeBound id p)))

forallElim :: Theorem -> Theorem -> Theorem
forallElim (Theorem (ctx,  Provable (Forall x q)))
           (Theorem (ctx', IsTerm t))
           | ctx == ctx' =
            Theorem (ctx,  Provable (makeReplace t q))

existsIntro :: Theorem -> Theorem -> Theorem -> Theorem
existsIntro (Theorem (ctx,   Provable pt))
            (Theorem (ctx',  IsFormula (Exists x p)))
            (Theorem (ctx'', IsTerm t))
            | ctx == ctx' && pt == makeReplace t p =
             Theorem (ctx,   Provable (Exists x p))

existsElim :: Theorem -> Theorem -> Theorem -> Theorem
existsElim (Theorem (ctx,   Provable (Exists x p)))
           (Theorem (ctx',  Provable (Forall y (p' `Implies` q))))
           (Theorem (ctx'', IsFormula q'))
           | ctx == ctx' && ctx == ctx'' && p == p' && q == q' =
            Theorem (ctx,   Provable q)


-- Derivation trees (aka. proof terms)
data Proof =
    Assumption String
  | AndI Proof Proof
  | AndL Proof
  | AndR Proof
  | OrL Proof Expr
  | OrR Expr Proof
  | OrE Proof Proof Proof
  | ImpliesI Proof
  | ImpliesE Proof
-- ...

checkProof :: Context -> Proof -> Theorem
checkProof ctx p = case p of
  (Assumption s) -> assumption ctx s
  (AndI p' q') -> andIntro (checkProof ctx p') (checkProof ctx q')
-- ...


