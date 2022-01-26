-- ApiMu/FOL verifier v0.1 (Haskell version)
-- Licensed under Creative Commons CC0 (no copyright reserved, use at your will)

-- This variant of FOL & ND is largely based on Dirk van Dalen's *Logic and Structure*...
-- To keep in line with the proof language, some context-changing rules are now represented in terms of
-- `impliesIntro` and `forallIntro`; additional features are described in `notes/design.md`.

-- This is a VERY INEFFICIENT implementation that serves mainly as a specification:
-- EVERY theorem has a context attached to it, so if there are many definitions, the program will
-- take up a lot of time and memory.

-- {-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
{-# LANGUAGE PatternSynonyms #-}

module FOLPlus
  ( Theorem, Context, Judgment(..), Sort(..), Type(..), VarName(..), Expr(..),
    ctxStack, ctxEmpty, ctxVar, ctxFunc, ctxAssumption, isExtensionOf, ctxAllNames, ctxLookup,
    thmContext, thmJudgment,
    weaken, varMk, eqMk, topMk, bottomMk, notMk, andMk, orMk, impliesMk, iffMk,
    forallMk, existsMk, uniqueMk, forallFuncMk, lamMk,
    assumption, andIntro, andLeft, andRight, orLeft, orRight, orElim, impliesIntro, impliesElim,
    notIntro, notElim, iffIntro, iffLeft, iffRight, trueIntro, falseElim, raa, eqIntro, eqElim,
    forallIntro, forallElim, existsIntro, existsElim, uniqueIntro, uniqueLeft, uniqueRight,
    forallFuncIntro, forallFuncElim, funcDef, funcDDef, funcIDef ) where

import Data.List
import Data.Maybe


-- Context entry
data CInfo = CVar Type | CHyp Expr
  deriving (Eq, Show)

-- The context is stored as a stack (a list whose first element denotes the topmost layer).
-- On each layer there is a list:
--   The first element is what was "assumed" at the beginning of the current scope.
--   The later elements are what were "defined" inside the current scope.
-- We don't have contraction or permutation rules, but currently they are not needed; weakening is stated below.
newtype Context = Context { ctxStack :: [[(String, CInfo)]] }
  deriving (Eq)

instance Show Context where
  show ctx@(Context a) =
    foldr (\defs acc -> acc ++ foldl (\acc (id, c) -> acc ++ id ++ " : " ++ show c ++ "\n  | ") "" defs ++ "\n") "" a

ctxEmpty :: Context
ctxEmpty = Context [[("initial", CVar TTerm)]]

ctxVar :: String -> Context -> Context
ctxVar id ctx@(Context a)
  | id `notElem` ctxAllNames ctx = Context ([(id, CVar TTerm)] : a)
  | otherwise = error ("ctxVar: name " ++ id ++ "already taken")

ctxFunc :: String -> Int -> Sort -> Context -> Context
ctxFunc id arity sort ctx@(Context a)
  | id `notElem` ctxAllNames ctx && arity >= 0 = Context ([(id, CVar $ TFunc arity sort)] : a)
  | arity >= 0 = error ("ctxFunc: name " ++ id ++ "already taken")
  | otherwise  = error "ctxFunc: Negative arity"

ctxAssumption :: String -> Theorem -> Context
ctxAssumption id (Theorem (ctx@(Context a), HasType p TFormula))
  | id `notElem` ctxAllNames ctx = Context ([(id, CHyp p)] : a)
  | otherwise     = error ("ctxAssumption: name " ++ id ++ "already taken")
ctxAssumption _ _ = error "ctxAssumption: not a formula"

-- Add definition entry (hidden)
ctxAddDef :: String -> Type -> Context -> Context
ctxAddDef id t ctx@(Context (l : ls))
  | id `notElem` ctxAllNames ctx = Context (((id, CVar t) : l) : ls)
  | otherwise                    = error ("ctxAddDef: name " ++ id ++ "already taken")

-- Returns True if the first context is an extension of the second one (used in the weakening rule)
isExtensionOf :: Context -> Context -> Bool
isExtensionOf (Context a') (Context a) =
  length a' >= length a && and (zipWith isPrefixOf (reverse a) (reverse a'))

-- Get all names
ctxAllNames :: Context -> [String]
ctxAllNames (Context a) = concatMap (map fst) a

-- Look up by name
ctxLookup :: String -> Context -> Maybe CInfo
ctxLookup s (Context a) = ctxLookup' a
  where
    ctxLookup' [] = Nothing
    ctxLookup' (l : ls) = case lookup s l of
      Just res -> Just res
      Nothing  -> ctxLookup' ls

-- Bound variables are represented using de Brujin indices:
--   (0 = binds to the deepest binder, 1 = escapes one binder, and so on)
data VarName = Free String | Bound Int
  deriving (Eq)

-- Possible "types" of expressions (ι means Var, * means Prop):
--   Terms:      TFunc 0 SVar  (ι)
--   Functions:  TFunc k SVar  (ι → ... → ι → ι)
--   Formulas:   TFunc 0 SProp (*)
--   Predicates: TFunc k SProp (ι → ... → ι → *)
-- Schemas have "second-order parameters":
--   TSchema k1 s1 (TFunc k2 s2) means ((ι → ... → ι → s1) → ι → ... → ι → s2), etc.
-- (This is similar to Metamath definition checkers, according to Mario Carneiro!)
data Sort = SVar | SProp
  deriving (Eq, Show)
data Type = TFunc Int Sort | TSchema Int Sort Type
  deriving (Eq, Show)

pattern TTerm :: Type
pattern TTerm = TFunc 0 SVar

pattern TFormula :: Type
pattern TFormula = TFunc 0 SProp

-- Main expression type
data Expr =
  -- Variables / functions / predicates / schema instantiations (4 in 1)
  -- Always fully applied.
    Var VarName [Expr]
  -- Equality rules are expressible using axiom schemas, but `unique` binder / definite description rules are not.
  -- So I make equality a primitive notion here.
  | Eq Expr Expr
  | Top    -- To avoid naming clashes I did not use `True` here
  | Bottom -- Also here
  | Not Expr
  | And Expr Expr
  | Or Expr Expr
  | Implies Expr Expr
  | Iff Expr Expr
  | Forall String Expr
  | Exists String Expr
  | Unique String Expr
  -- These must be at the beginning (the outermost layers) of an expression
  | ForallFunc String Int Sort Expr
  | Lam String Expr

-- Ignore the literal names of bound variables when comparing (alpha-equivalence)
instance Eq Expr where
  (==) (Var x1 x2)             (Var y1 y2)             = x1 == y1 && x2 == y2
  (==) (Eq x1 x2)              (Eq y1 y2)              = x1 == y1 && x2 == y2
  (==) Top                     Top                     = True
  (==) Bottom                  Bottom                  = True
  (==) (Not x1)                (Not y1)                = x1 == y1
  (==) (And x1 x2)             (And y1 y2)             = x1 == y1 && x2 == y2
  (==) (Or x1 x2)              (Or y1 y2)              = x1 == y1 && x2 == y2
  (==) (Implies x1 x2)         (Implies y1 y2)         = x1 == y1 && x2 == y2
  (==) (Iff x1 x2)             (Iff y1 y2)             = x1 == y1 && x2 == y2
  (==) (Forall _ x1)           (Forall _ y1)           = x1 == y1
  (==) (Exists _ x1)           (Exists _ y1)           = x1 == y1
  (==) (Unique _ x1)           (Unique _ y1)           = x1 == y1
  (==) (ForallFunc _ x1 x2 x3) (ForallFunc _ y1 y2 y3) = x1 == y1 && x2 == y2 && x3 == y3
  (==) (Lam _ x1)              (Lam _ y1)              = x1 == y1
  (==) _                       _                       = False

-- For display
newName :: String -> [String] -> String
newName x used
  | x `notElem` used = x
  | otherwise        = newName (x ++ "'") used

showName :: [String] -> VarName -> String
showName stk (Free s)  = s
showName stk (Bound i) = stk !! i

showE :: [String] -> [String] -> Expr -> String
showE used stk e' = case e' of
  (Var x []) -> showName stk x
  (Var x as) -> "(" ++ showName stk x ++ concatMap ((" " ++) . showE used stk) as ++ ")"
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
  (ForallFunc x k SVar  e) -> "(forallfunc " ++ x' ++ "/" ++ show k ++ ", " ++ showE (x' : used) (x' : stk) e ++ ")" where x' = newName x used
  (ForallFunc x k SProp e) -> "(forallpred " ++ x' ++ "/" ++ show k ++ ", " ++ showE (x' : used) (x' : stk) e ++ ")" where x' = newName x used
  (Lam x e) -> case stk of
    [] -> "(" ++ str ++ ")" -- Outermost layer
    _  -> str               -- Otherwise
    where
      x' = newName x used
      str = case e of
        (Lam _ _) -> x' ++  " "  ++ showE (x' : used) (x' : stk) e -- Intermediate layers
        _         -> x' ++ " | " ++ showE (x' : used) (x' : stk) e -- Innermost layer

inContextShowE :: Context -> Expr -> String
inContextShowE ctx = showE (ctxAllNames ctx) []

instance Show Expr where
  show = showE [] []

-- n = (number of binders on top of current node)
updateVars :: Int -> (Int -> VarName -> [Expr] -> Expr) -> Expr -> Expr
updateVars n f e' = case e' of
  (Var x es) -> f n x args where args = map (updateVars n f) es
  (Eq e1 e2) -> Eq (updateVars n f e1) (updateVars n f e2)
  Top -> e'
  Bottom -> e'
  (Not e1) -> Not (updateVars n f e1)
  (And e1 e2) -> And (updateVars n f e1) (updateVars n f e2)
  (Or e1 e2) -> Or (updateVars n f e1) (updateVars n f e2)
  (Implies e1 e2) -> Implies (updateVars n f e1) (updateVars n f e2)
  (Iff e1 e2) -> Iff (updateVars n f e1) (updateVars n f e2)
  (Forall x e1) -> Forall x (updateVars (n + 1) f e1)
  (Exists x e1) -> Exists x (updateVars (n + 1) f e1)
  (Unique x e1) -> Unique x (updateVars (n + 1) f e1)
  (ForallFunc x k s e1) -> ForallFunc x k s (updateVars (n + 1) f e1)
  (Lam x e1) -> Lam x (updateVars (n + 1) f e1)

-- Prepare to bind a free variable
-- Note that the resulting expression is not well-formed until one additional layer of binder is added (there are "binding overflows by exactly one")
makeBound :: String -> Expr -> Expr
makeBound id = updateVars 0 (\n x args -> if x == Free id then Var (Bound n) args else Var x args)

-- makeFree + replaceVar in one go
-- Input expression can be a subexpression which is not well-formed by itself (there can be "binding overflows by exactly one")
makeReplace :: Expr -> Expr -> Expr
makeReplace t = updateVars 0 (\n x args -> if x == Bound n then t else Var x args)

-- Prepare to insert k binders around a subexpression
-- Input expression can be a subexpression which is not well-formed by itself
makeGap :: Int -> Expr -> Expr
makeGap k = updateVars 0 (\n x args -> case x of Bound m | m >= n -> Var (Bound (m + k)) args; _ -> Var x args)

-- Skip through lambda binders
getBody :: Expr -> (Int, Expr)
getBody (Lam _ e) = (n + 1, body) where (n, body) = getBody e
getBody body      = (0,     body)

-- Substitute in k overflow variables simultaneously, with t's possibly containing bound variables...
makeReplace' :: Int -> [Expr] -> Expr -> Expr
makeReplace' k ts
  | k == length ts = updateVars 0 (\n x args -> case x of Bound m | m >= n -> makeGap n (ts' !! (m - n)); _ -> Var x args)
  | otherwise      = error "makeReplace': arity do not match"
  where ts' = reverse ts -- Leftmost arguments are used to substitute highest lambdas

-- Substitute in a lambda function.
-- The 2nd argument is a lambda function/predicate with exactly k lambda binders (will be checked)
-- In the 3rd argument, all applications of the "overflow-bound" function/predicate must have k arguments (will be checked)
-- To ensure that the resulting expression is well-formed, functions must be replaced by functions and
-- predicates must be replaced by predicates (i.e. types must match)
makeReplaceLam :: Int -> Expr -> Expr -> Expr
makeReplaceLam k lam
  | k == k'   = updateVars 0 (\n f args -> if f == Bound n then makeReplace' k args body else Var f args)
  | otherwise = error "makeReplaceLam: arity do not match"
  where (k', body) = getBody lam

-- Kinds of judgments
data Judgment = HasType Expr Type | Provable Expr
  deriving (Eq)

inContextShowJ :: Context -> Judgment -> String
inContextShowJ ctx j = case j of
  (HasType e t) -> "HasType " ++ inContextShowE ctx e ++ " " ++ show t
  (Provable e)  -> "Provable " ++ inContextShowE ctx e

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

-- Formation rules (as in `notes/design.md`)

varMk :: Context -> String -> [Theorem] -> Theorem
varMk ctx id js =
  case ctxLookup id ctx of
    Just (CVar t) -> Theorem (ctx, HasType (Var (Free id) as) (check t js))
    _             -> error "varMk: variable not found in context"
  where
    as = map (\(Theorem (_, HasType t _)) -> t) js

    -- Try applying arguments one by one
    check :: Type -> [Theorem] -> Type
    check t [] = t
    check (TFunc k s) (Theorem (ctx', HasType _ TTerm) : js')
      | ctx == ctx' && k > 0 =
        check (TFunc (k - 1) s) js'
    check (TSchema k s t) (Theorem (ctx', HasType _ (TFunc k' s')) : js')
      | ctx == ctx' && k == k' && s == s' =
        check t js'
    check _ _ = error "varMk: argument type mismatch"

eqMk :: Theorem -> Theorem -> Theorem
eqMk (Theorem (ctx,  HasType t1 TTerm))
     (Theorem (ctx', HasType t2 TTerm))
     | ctx == ctx' =
      Theorem (ctx,  HasType (t1 `Eq` t2) TFormula)

topMk :: Context -> Theorem
topMk ctx = Theorem (ctx, HasType Top TFormula)

bottomMk :: Context -> Theorem
bottomMk ctx = Theorem (ctx, HasType Bottom TFormula)

notMk :: Theorem -> Theorem
notMk (Theorem (ctx, HasType e TFormula)) =
       Theorem (ctx, HasType (Not e) TFormula)

andMk :: Theorem -> Theorem -> Theorem
andMk (Theorem (ctx,  HasType e1 TFormula))
      (Theorem (ctx', HasType e2 TFormula))
      | ctx == ctx' =
       Theorem (ctx,  HasType (e1 `And` e2) TFormula)

orMk :: Theorem -> Theorem -> Theorem
orMk (Theorem (ctx,  HasType e1 TFormula))
     (Theorem (ctx', HasType e2 TFormula))
     | ctx == ctx' =
      Theorem (ctx,  HasType (e1 `Or` e2) TFormula)

impliesMk :: Theorem -> Theorem -> Theorem
impliesMk (Theorem (ctx,  HasType e1 TFormula))
          (Theorem (ctx', HasType e2 TFormula))
          | ctx == ctx' =
           Theorem (ctx,  HasType (e1 `Implies` e2) TFormula)

iffMk :: Theorem -> Theorem -> Theorem
iffMk (Theorem (ctx,  HasType e1 TFormula))
      (Theorem (ctx', HasType e2 TFormula))
      | ctx == ctx' =
       Theorem (ctx,  HasType (e1 `Iff` e2) TFormula)

-- (Context-changing rule)
forallMk :: Theorem -> Theorem
forallMk (Theorem (ctx,  HasType e TFormula)) =
          Theorem (ctx', HasType (Forall s' e') TFormula)
  where (ctx', s', 0, SVar, e') = ctxGenPop ctx e

-- (Context-changing rule)
existsMk :: Theorem -> Theorem
existsMk (Theorem (ctx,  HasType e TFormula)) =
          Theorem (ctx', HasType (Exists s' e') TFormula)
  where (ctx', s', 0, SVar, e') = ctxGenPop ctx e

-- (Context-changing rule)
uniqueMk :: Theorem -> Theorem
uniqueMk (Theorem (ctx,  HasType e TFormula)) =
          Theorem (ctx', HasType (Unique s' e') TFormula)
  where (ctx', s', 0, SVar, e') = ctxGenPop ctx e

-- (Context-changing rule)
forallFuncMk :: Theorem -> Theorem
forallFuncMk (Theorem (ctx,  HasType e TFormula)) =
              Theorem (ctx', HasType (ForallFunc str' k' s' e') TFormula)
  where (ctx', str', k', s', e') = ctxGenPop ctx e

-- (Context-changing rule)
lamMk :: Theorem -> Theorem
lamMk (Theorem (ctx,  HasType e (TFunc k sort))) =
       Theorem (ctx', HasType (Lam s' e') (TFunc (k + 1) sort))
  where (ctx', s', 0, SVar, e') = ctxGenPop ctx e

-- Introduction & elimination rules
-- Pre & post: `Provable ctx p` => `IsPred 0 ctx p`

assumption :: Context -> String -> Theorem
assumption ctx id =
  case ctxLookup id ctx of
    Just (CHyp p) -> Theorem (ctx, Provable p)

andIntro :: Theorem -> Theorem -> Theorem
andIntro (Theorem (ctx,  Provable p))
         (Theorem (ctx', Provable q))
         | ctx == ctx' =
          Theorem (ctx,  Provable (p `And` q))

andLeft :: Theorem -> Theorem
andLeft (Theorem (ctx, Provable (p `And` q))) =
         Theorem (ctx, Provable p)

andRight :: Theorem -> Theorem
andRight (Theorem (ctx, Provable (p `And` q))) =
          Theorem (ctx, Provable q)

orLeft :: Theorem -> Theorem -> Theorem
orLeft (Theorem (ctx,  Provable p))
       (Theorem (ctx', HasType q TFormula))
       | ctx == ctx' =
        Theorem (ctx,  Provable (p `Or` q))

orRight :: Theorem -> Theorem -> Theorem
orRight (Theorem (ctx,  HasType p TFormula))
        (Theorem (ctx', Provable q))
        | ctx == ctx' =
         Theorem (ctx,  Provable (p `Or` q))

orElim :: Theorem -> Theorem -> Theorem -> Theorem
orElim (Theorem (ctx,   Provable (p `Or` q)))
       (Theorem (ctx',  Provable (p' `Implies` r)))
       (Theorem (ctx'', Provable (q' `Implies` r')))
       | ctx == ctx' && ctx == ctx'' && p == p' && q == q' && r == r' =
        Theorem (ctx,   Provable r)

-- (Context-changing rule)
impliesIntro :: Theorem -> Theorem
impliesIntro (Theorem (ctx,  Provable q)) =
              Theorem (ctx', Provable (p' `Implies` q))
  where (ctx', p') = ctxAssumePop ctx

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

trueIntro :: Context -> Theorem
trueIntro ctx = Theorem (ctx, Provable Top)

falseElim :: Theorem -> Theorem -> Theorem
falseElim (Theorem (ctx,  Provable Bottom))
          (Theorem (ctx', HasType p TFormula))
          | ctx == ctx' =
           Theorem (ctx,  Provable p)

raa :: Theorem -> Theorem
raa (Theorem (ctx, Provable (Not p `Implies` Bottom))) =
     Theorem (ctx, Provable p)

eqIntro :: Theorem -> Theorem
eqIntro (Theorem (ctx, HasType t TTerm)) =
         Theorem (ctx, Provable (t `Eq` t))

eqElim :: Theorem -> Theorem -> Theorem -> Theorem
eqElim (Theorem (ctx,   HasType (Lam x px) (TFunc 1 SProp)))
       (Theorem (ctx',  Provable (a `Eq` b)))
       (Theorem (ctx'', Provable pa))
       | ctx == ctx' && pa == makeReplace a px =
        Theorem (ctx,   Provable (makeReplace b px))

-- (Context-changing rule)
forallIntro :: Theorem -> Theorem
forallIntro (Theorem (ctx,  Provable p)) =
             Theorem (ctx', Provable (Forall s' p'))
  where (ctx', s', 0, SVar, p') = ctxGenPop ctx p

forallElim :: Theorem -> Theorem -> Theorem
forallElim (Theorem (ctx,  Provable (Forall x q)))
           (Theorem (ctx', HasType t TTerm))
           | ctx == ctx' =
            Theorem (ctx,  Provable (makeReplace t q))

existsIntro :: Theorem -> Theorem -> Theorem -> Theorem
existsIntro (Theorem (ctx',  HasType (Exists x p) TFormula))
            (Theorem (ctx'', HasType t TTerm))
            (Theorem (ctx,   Provable pt))
            | ctx == ctx' && pt == makeReplace t p =
             Theorem (ctx,   Provable (Exists x p))

existsElim :: Theorem -> Theorem -> Theorem -> Theorem
existsElim (Theorem (ctx,   Provable (Exists x p)))
           (Theorem (ctx',  Provable (Forall y (p' `Implies` q))))
           (Theorem (ctx'', HasType q' TFormula))
           | ctx == ctx' && ctx == ctx'' && p == p' && q == q' =
            Theorem (ctx,   Provable q)

uniqueIntro :: Theorem -> Theorem -> Theorem
uniqueIntro (Theorem (ctx,  Provable (Exists x' px')))
            (Theorem (ctx', Provable (Forall x (px `Implies` Forall y (py `Implies` (Var (Bound 1) [] `Eq` Var (Bound 0) []))))))
            | ctx == ctx' && px' == px && px' == py =
             Theorem (ctx,  Provable (Unique x' px'))

uniqueLeft :: Theorem -> Theorem
uniqueLeft (Theorem (ctx, Provable (Unique x px))) =
            Theorem (ctx, Provable (Exists x px))

uniqueRight :: Theorem -> Theorem
uniqueRight (Theorem (ctx, Provable (Unique x px))) =
             Theorem (ctx, Provable (Forall x (px `Implies` Forall x' (px `Implies` (Var (Bound 1) [] `Eq` Var (Bound 0) [])))))
  where x' = newName x (x : ctxAllNames ctx)

-- (Context-changing rule)
forallFuncIntro :: Theorem -> Theorem
forallFuncIntro (Theorem (ctx,  Provable p)) =
                 Theorem (ctx', Provable (ForallFunc str' k' s' p'))
  where (ctx', str', k', s', p') = ctxGenPop ctx p

forallFuncElim :: Theorem -> Theorem -> Theorem
forallFuncElim (Theorem (ctx,  Provable (ForallFunc f k s q)))
               (Theorem (ctx', HasType t (TFunc k' s')))
               | ctx == ctx' && k == k' && s == s' =
                Theorem (ctx,  Provable (makeReplaceLam k t q))

-- Definition rules

-- Function/predicate definition
funcDef :: String -> Sort -> Theorem -> Theorem
funcDef id SVar (Theorem (ctx,  HasType t TTerm)) = 
                 Theorem (ctx', Provable (Var (Free id) [] `Eq` t))
  where ctx' = ctxAddDef id TTerm ctx

funcDef id SProp (Theorem (ctx,  HasType phi TFormula)) =
                  Theorem (ctx', Provable (Var (Free id) [] `Iff` phi))
  where ctx' = ctxAddDef id TFormula ctx

-- Function definition by definite description
funcDDef :: String -> Theorem -> Theorem
funcDDef id (Theorem (ctx,  Provable (Unique x p))) =
             Theorem (ctx', Provable (Forall x (p `Iff` (Var (Bound 0) [] `Eq` Var (Free id) []))))
  where ctx' = ctxAddDef id TTerm ctx

-- Function definition by indefinite description
funcIDef :: String -> Theorem -> Theorem
funcIDef id (Theorem (ctx,  Provable (Exists _ p))) =
             Theorem (ctx', Provable (makeReplace (Var (Free id) []) p))
  where ctx' = ctxAddDef id TTerm ctx

-- Definition generalization rules (executed in context-changing rules)

-- (Hidden)
ctxAssumePop :: Context -> (Context, Expr)
ctxAssumePop (Context (((_, CHyp hyp) : defs) : l' : ls)) =
             (Context ((l' ++ defs) : ls), hyp)

-- (Hidden)
ctxGenPop :: Context -> Expr -> (Context, String, Int, Sort, Expr)
ctxGenPop (Context (((name, CVar (TFunc k s)) : defs) : l' : ls)) e =
          (Context ((l' ++ newdefs) : ls), name, k, s, modify e)
  where
    -- The names of definitions in the last layer (excluding the hypothesized one)
    ids = map fst defs
    -- Add the definitions in the topmost layer into the second-to-top layer,
    -- adding abstraction over the hypothesized variable.
    newdefs =
      map (\(name, CVar t) -> case t of
        (TFunc k' s') ->
          if (k, s) == (0, SVar)
          then (name, CVar $ TFunc (k' + 1) s')
          else (name, CVar $ TSchema k s t)
        (TSchema {}) ->
          (name, CVar $ TSchema k s t))
      defs
    -- Modify the expression to reflect changes in definitions,
    -- and prepare to bind the hypothesized variable.
    modify =
      updateVars 0 (\n x args -> case x of
        (Free id)
          | id `elem` ids -> Var (Free id) (Var (Bound n) [] : args)
          | id == name    -> Var (Bound n) args
        _                 -> Var x args)

