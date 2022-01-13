import Data.Map (Map)
import qualified Data.Map as Map

import FOL


checkIsTerm' :: Context -> Term -> Theorem
checkIsTerm' ctx e = case e of
  (Var x)     -> varMk ctx x
  (Func f ts) -> funcMk ctx f (map (checkIsTerm ctx) ts)

checkIsTerm :: Context -> Term -> Theorem
checkIsTerm ctx e = weaken (checkIsTerm' ctx e) ctx

checkIsFormula' :: Context -> Formula -> Theorem
checkIsFormula' ctx e = case e of
  (Pred p ts)     -> predMk ctx p (map (checkIsTerm ctx) ts)
  (Equals t1 t2)  -> eqMk (checkIsTerm ctx t1) (checkIsTerm ctx t1)
  Top             -> topMk
  Bottom          -> bottomMk
  (Not e)         -> notMk (checkIsFormula ctx e)
  (And e1 e2)     -> andMk (checkIsFormula ctx e1) (checkIsFormula ctx e2)
  (Or e1 e2)      -> orMk (checkIsFormula ctx e1) (checkIsFormula ctx e2)
  (Implies e1 e2) -> impliesMk (checkIsFormula ctx e1) (checkIsFormula ctx e2)
  (Iff e1 e2)     -> iffMk (checkIsFormula ctx e1) (checkIsFormula ctx e2)
  (Forall x e)    -> forallMk x (checkIsFormula (ctxVar x ctx) e)
  (Exists x e)    -> existsMk x (checkIsFormula (ctxVar x ctx) e)
  (Unique x e)    -> uniqueMk x (checkIsFormula (ctxVar x ctx) e)

checkIsFormula :: Context -> Formula -> Theorem
checkIsFormula ctx e = weaken (checkIsFormula' ctx e) ctx


-- TEMP CODE

ctx1 :: Context
ctx1 = ctxPred "<" 2 $ ctxFunc "+" 2 $ ctxVar "0" ctxEmpty

e1 = Forall "e" (Pred "<" [Var "0", Var "e"] `Implies` Exists "N" (Forall "n" (Pred "<" [Var "N", Var "n"] `Implies` Bottom)))

ctx2 :: Context
ctx2 = ctxPred "L" 2 $ ctxPred "B" 3 $ ctxVar "Q" ctxEmpty

e2 = Forall "x" (Forall "y" (Pred "L" [Var "x", Var "y"] `Implies` Forall "z" (Not (Equals (Var "z") (Var "y")) `Implies` Not (Pred "L" [Var "x", Var "z"]))))
e3 = Forall "x" (Forall "y" (Forall "z" (Pred "B" [Var "x", Var "y", Var "z"] `Implies` (Pred "L" [Var "x", Var "z"] `Implies` Pred "L" [Var "x", Var "y"]))))
e4 = Exists "x" (Forall "y" (Pred "B" [Var "y", Var "x", Var "Q"]))
e5 = Not (Exists "x" (Pred "L" [Var "x", Var "Q"]))

