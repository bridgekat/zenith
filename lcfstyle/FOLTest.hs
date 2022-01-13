import Prelude hiding (pred)
import Data.Map (Map)
import qualified Data.Map as Map

import FOL


convertAndCheck' :: Context -> Expr -> Theorem
convertAndCheck' ctx e = case e of
  (Var (Free x)) -> varMk ctx x
  (Func (Free f) ts) -> funcMk ctx f (map (convertAndCheck ctx) ts)
  (Pred (Free p) ts) -> predMk ctx p (map (convertAndCheck ctx) ts)
  (Equals t1 t2) -> eqMk (convertAndCheck ctx t1) (convertAndCheck ctx t1)
  Top -> topMk
  Bottom -> bottomMk
  (Not e) -> notMk (convertAndCheck ctx e)
  (And e1 e2) -> andMk (convertAndCheck ctx e1) (convertAndCheck ctx e2)
  (Or e1 e2) -> orMk (convertAndCheck ctx e1) (convertAndCheck ctx e2)
  (Implies e1 e2) -> impliesMk (convertAndCheck ctx e1) (convertAndCheck ctx e2)
  (Iff e1 e2) -> iffMk (convertAndCheck ctx e1) (convertAndCheck ctx e2)
  (Forall x e) -> forallMk x (convertAndCheck (ctxVar x ctx) e)
  (Exists x e) -> existsMk x (convertAndCheck (ctxVar x ctx) e)
  (Unique x e) -> uniqueMk x (convertAndCheck (ctxVar x ctx) e)

convertAndCheck :: Context -> Expr -> Theorem
convertAndCheck ctx e = weaken (convertAndCheck' ctx e) ctx


-- TEMP CODE

var = Var . Free
func = Func . Free
pred = Pred . Free

ctx1 :: Context
ctx1 = ctxPred "<" 2 $ ctxFunc "+" 2 $ ctxVar "0" ctxEmpty

e1 = Forall "e" (pred "<" [var "0", var "e"] `Implies` Exists "N" (Forall "n" (pred "<" [var "N", var "n"] `Implies` Bottom)))
wff1 = convertAndCheck ctx1 e1


ctx1' :: Context
ctx1' = ctxAssumption "h" wff1 ctx1

thm1p = assumption ctx1' "h"

t1 = func "+" [func "+" [var "0", var "0"], var "0"]
wft1 = convertAndCheck ctx1' t1

-- `thmJudgment (forallElim thm1p wft1)` outputs:
-- Provable ((< 0 (+ (+ 0 0) 0)) implies (exists N, (forall n, ((< N n) implies false))))


ctx2 :: Context
ctx2 = ctxPred "L" 2 $ ctxPred "B" 3 $ ctxVar "Q" ctxEmpty

e2 = Forall "x" (Forall "y" (pred "L" [var "x", var "y"] `Implies` Forall "z" (Not (Equals (var "z") (var "y")) `Implies` Not (pred "L" [var "x", var "z"]))))
wff2 = convertAndCheck ctx2 e2
e3 = Forall "x" (Forall "y" (Forall "z" (pred "B" [var "x", var "y", var "z"] `Implies` (pred "L" [var "x", var "z"] `Implies` pred "L" [var "x", var "y"]))))
wff3 = convertAndCheck ctx2 e3
e4 = Exists "x" (Forall "y" (pred "B" [var "y", var "x", var "Q"]))
wff4 = convertAndCheck ctx2 e4
e5 = Not (Exists "x" (pred "L" [var "x", var "Q"]))
wff5 = convertAndCheck ctx2 e5



