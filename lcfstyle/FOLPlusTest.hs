{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

import Prelude hiding (pred)
import Data.Map (Map)
import qualified Data.Map as Map

import FOLPlus


convertAndCheck' :: Context -> Expr -> Theorem
convertAndCheck' ctx e = case e of
  (Var (Free x)) -> varMk ctx x
  (Var (Bound i)) -> error "Please use names for bound variables in the input expression"
  (Func (Free f) ts) -> funcMk ctx f (map (convertAndCheck ctx) ts)
  (Func (Bound i) ts) -> error "Please use names for bound variables in the input expression"
  (Pred (Free p) ts) -> predMk ctx p (map (convertAndCheck ctx) ts)
  (Pred (Bound i) ts) -> error "Please use names for bound variables in the input expression"
  (Eq t1 t2) -> eqMk (convertAndCheck ctx t1) (convertAndCheck ctx t2)
  Top -> topMk
  Bottom -> bottomMk
  (Not e) -> notMk (convertAndCheck ctx e)
  (And e1 e2) -> andMk (convertAndCheck ctx e1) (convertAndCheck ctx e2)
  (Or e1 e2) -> orMk (convertAndCheck ctx e1) (convertAndCheck ctx e2)
  (Implies e1 e2) -> impliesMk (convertAndCheck ctx e1) (convertAndCheck ctx e2)
  (Iff e1 e2) -> iffMk (convertAndCheck ctx e1) (convertAndCheck ctx e2)
  (Forall x e) -> forallMk (convertAndCheck (ctxVar x ctx) e)
  (Exists x e) -> existsMk (convertAndCheck (ctxVar x ctx) e)
  (Unique x e) -> uniqueMk (convertAndCheck (ctxVar x ctx) e)
  (ForallFunc f k e) -> forallFuncMk (convertAndCheck (ctxFunc f k ctx) e)
  (ForallPred p k e) -> forallPredMk (convertAndCheck (ctxPred p k ctx) e)
  (Lam x e) -> lamMk (convertAndCheck (ctxVar x ctx) e)

-- Convert to de Brujin indices and check types.
convertAndCheck :: Context -> Expr -> Theorem
convertAndCheck ctx e = weaken (convertAndCheck' ctx e) ctx

-- Derivation trees (aka. proof terms)
data Proof =
    Assumption String
  | Lemma Decl
  | AndI Proof Proof | AndL Proof | AndR Proof
  | OrL Proof Expr | OrR Expr Proof | OrE Proof Proof Proof
  | ImpliesE Proof Proof
  | NotI Proof | NotE Proof Proof
  | IffI Proof Proof | IffL Proof Proof | IffR Proof Proof
  | TrueI
  | FalseE Proof Expr | RAA Proof
  | EqI Expr | EqE Proof Expr Proof
  | ForallE Proof Expr
  | ExistsI Expr Proof | ExistsE Proof Proof
  | UniqueI Proof Proof | UniqueL Proof | UniqueR Proof
  | ForallFuncE Proof Expr
  | ForallPredE Proof Expr

-- Declarations
data Decl =
    Block [Decl]
  | Theorem String Expr Proof
  | FuncDef String Expr
  | PredDef String Expr
  | FuncDDef String Expr Proof
  | FuncIDef String Expr Proof

checkProof :: Context -> Proof -> [Theorem]
checkProof ctx thm p = case p of
  (Assumption s) -> assumption ctx s
  (AndI p' q') -> andIntro (checkProof ctx p') (checkProof ctx q')
-- ...



-- TEMP CODE

var = Var . Free
func = Func . Free
pred = Pred . Free

{-
ctx' :: Context
ctx' = ctxPred "<" 2 $ ctxFunc "+" 2 $ ctxVar "0" ctxEmpty

e1 = Forall "e" (pred "<" [var "0", var "e"] `Implies` Exists "N" (Forall "n" (pred "<" [var "N", var "n"] `Implies` Bottom)))
wff1 = convertAndCheck ctx' e1


ctx :: Context
ctx = ctxAssumption "h" wff1

thm1 = assumption ctx "h"

t1 = func "+" [func "+" [var "0", var "0"], var "0"]
wft1 = convertAndCheck ctx t1

-- `thmJudgment (forallElim thm1 wft1)` outputs:
-- Provable ((< 0 (+ (+ 0 0) 0)) implies (exists N, (forall n, ((< N n) implies false))))
-}

ctx' :: Context
ctx' = ctxPred "L" 2 $ ctxPred "B" 3 $ ctxVar "Q" ctxEmpty

e1 = Forall "x" (Forall "y" (pred "L" [var "x", var "y"] `Implies` Forall "z" (Not (Eq (var "z") (var "y")) `Implies` Not (pred "L" [var "x", var "z"]))))
wff1 = convertAndCheck ctx' e1
e2 = Forall "x" (Forall "y" (Forall "z" (pred "B" [var "x", var "y", var "z"] `Implies` (pred "L" [var "x", var "z"] `Implies` pred "L" [var "x", var "y"]))))
wff2 = convertAndCheck ctx' e2
e3 = Exists "x" (Not (Eq (var "x") (var "Q")) `And` Forall "y" (pred "B" [var "y", var "x", var "Q"]))
wff3 = convertAndCheck ctx' e3
e4 = Not (Exists "x" (pred "L" [var "x", var "Q"]))
wff4 = convertAndCheck ctx' e4

ctx :: Context
ctx =
  ctxAssumption "h3" . flip convertAndCheck e3 $
  ctxAssumption "h2" . flip convertAndCheck e2 $
  ctxAssumption "h1" . flip convertAndCheck e1 $
  ctxVar "Q" $
  ctxPred "B" 3 $
  ctxPred "L" 2 $
  ctxEmpty

h1 = assumption ctx "h1"
h2 = assumption ctx "h2"
h3 = assumption ctx "h3"

ctx1 =
  ctxAssumption "hc" . flip convertAndCheck
    (Not (Eq (var "c") (var "Q")) `And` Forall "x" (pred "B" [var "x", var "c", var "Q"])) $
  ctxVar "c" $
  ctx
hc = assumption ctx1 "hc"
hc1 = andLeft hc
hc2 = andRight hc

ctx2 =
  ctxAssumption "hex" . flip convertAndCheck
    (Exists "x" (pred "L" [var "x", var "Q"])) $
  ctx1
hex = assumption ctx2 "hex"

ctx3 =
  ctxAssumption "hx" . flip convertAndCheck
    (pred "L" [var "x", var "Q"]) $
  ctxVar "x" $
  ctx2
hx = assumption ctx3 "hx"

t1 =
  impliesElim
    (forallElim
      (forallElim
        (weaken h1 ctx3)
        (convertAndCheck ctx3 (var "x")))
      (convertAndCheck ctx3 (var "Q")))
    (weaken hx ctx3)

t2 =
  impliesElim
    (forallElim
      (weaken t1 ctx3)
      (convertAndCheck ctx3 (var "c")))
    (weaken hc1 ctx3)

t3 =
  forallElim
    (weaken hc2 ctx3)
    (convertAndCheck ctx3 (var "x"))

t4 =
  impliesElim
    (impliesElim
      (forallElim
        (forallElim
          (forallElim
            (weaken h2 ctx3)
            (convertAndCheck ctx3 (var "x")))
          (convertAndCheck ctx3 (var "c")))
        (convertAndCheck ctx3 (var "Q")))
      (weaken t3 ctx3))
    (weaken hx ctx3)

t5 = notElim t2 t4

[t1', t2', t3', t4', t5'] = map (forallIntro . impliesIntro) [t1, t2, t3, t4, t5]

t6' = existsElim (weaken hex ctx2) t5' (convertAndCheck ctx2 Bottom)

[t1'', t2'', t3'', t4'', t5'', t6''] = map impliesIntro [t1', t2', t3', t4', t5', t6']

t7'' = notIntro t6''

[t1''', t2''', t3''', t4''', t5''', t6''', t7'''] = map (forallIntro . impliesIntro) [t1'', t2'', t3'', t4'', t5'', t6'', t7'']

t8''' = existsElim (weaken h3 ctx) t7''' (convertAndCheck ctx (Not (Exists "x" (pred "L" [var "x", var "Q"]))))


