-- ApiMu/FOL verifier v0.1 (Haskell version)
-- Licensed under Creative Commons CC0 (no copyright reserved, use at your will)

{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE TupleSections #-}

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe

import FOLPlus

pattern TTerm :: Type
pattern TTerm = TFunc 0 SVar

pattern TFormula :: Type
pattern TFormula = TFunc 0 SProp


-- Convert to de Brujin indices and check types.
convertAndCheck :: Context -> Expr -> Theorem
convertAndCheck ctx e' = case e' of
  (Var (Free x) ts) -> varMk ctx x (map (convertAndCheck ctx) ts)
  (Var _ ts) -> error "Please use names for variables in the input expression"
  (Eq t1 t2) -> eqMk (convertAndCheck ctx t1) (convertAndCheck ctx t2)
  Top -> topMk ctx
  Bottom -> bottomMk ctx
  (Not e) -> notMk (convertAndCheck ctx e)
  (And e1 e2) -> andMk (convertAndCheck ctx e1) (convertAndCheck ctx e2)
  (Or e1 e2) -> orMk (convertAndCheck ctx e1) (convertAndCheck ctx e2)
  (Implies e1 e2) -> impliesMk (convertAndCheck ctx e1) (convertAndCheck ctx e2)
  (Iff e1 e2) -> iffMk (convertAndCheck ctx e1) (convertAndCheck ctx e2)
  (Forall x e) -> forallMk (convertAndCheck (ctxVar x ctx) e)
  (Exists x e) -> existsMk (convertAndCheck (ctxVar x ctx) e)
  (Unique x e) -> uniqueMk (convertAndCheck (ctxVar x ctx) e)
  (ForallFunc f k s e) -> forallFuncMk (convertAndCheck (ctxFunc f k s ctx) e)
  (Lam x e) -> lamMk (convertAndCheck (ctxVar x ctx) e)

-- Derivation trees (aka. proof terms)
data Proof =
    As String
  | Decl Decl
  | AndI Proof Proof        | AndL Proof              | AndR Proof
  | OrL Proof Expr          | OrR Expr Proof          | OrE Proof Proof Proof
  | ImpliesE Proof Proof
  | NotI Proof              | NotE Proof Proof
  | IffI Proof Proof        | IffL Proof Proof        | IffR Proof Proof
  | TrueI                   | FalseE Proof Expr       | RAA Proof
  | EqI Expr                | EqE Expr Proof Proof
  | ForallE Proof Expr
  | ExistsI Expr Expr Proof | ExistsE Proof Proof Expr
  | UniqueI Proof Proof     | UniqueL Proof           | UniqueR Proof
  | ForallFuncE Proof Expr

-- Declarations
data Decl =
    Block [Decl]
  | Assertion String (Maybe Expr) Proof
  | Any String Decl
  | AnyFunc String Int Sort Decl
  | Assume String Expr Decl
  | FuncDef String Expr
  | PredDef String Expr
  | FuncDDef String Expr Proof -- Definite description
  | FuncIDef String Expr Proof -- Indefinite description

-- `StatefulVal s` is a "state monad" (i.e. an expression/procedure that reads & modifies a state when being evaluated).
newtype StatefulVal s a = StatefulVal { eval :: s -> (a, s) }

instance Functor (StatefulVal s) where
  -- Allows normal functions to act on a `StatefulVal`. Can be implemented using the Applicative instance.
  fmap :: (a -> b) -> StatefulVal s a -> StatefulVal s b
  fmap f x = pure f <*> x

instance Applicative (StatefulVal s) where
  -- Allows normal values to be converted into `StatefulVal`s.
  pure :: a -> StatefulVal s a
  pure f = StatefulVal (\s -> (f, s))
  -- Allows a `StatefulVal` (which evaluates to a function) to act on another `StatefulVal`. We evaluate the LHS first.
  (<*>) :: StatefulVal s (a -> b) -> StatefulVal s a -> StatefulVal s b
  (<*>) f x = StatefulVal (\s -> let (f', s') = eval f s in let (x', s'') = eval x s' in (f' x', s''))

instance Monad (StatefulVal s) where
  -- Allows chaining of dependent `StatefulVal`s.
  (>>=) :: StatefulVal s a -> (a -> StatefulVal s b) -> StatefulVal s b
  (>>=) f g = StatefulVal (\s -> let (x, s') = eval f s in eval (g x) s')

-- Theorem pool (stack of Maps)
type TheoremPool = [Map String Theorem]
type WithState = StatefulVal TheoremPool

-- Look up by name
lookupPool :: String -> WithState (Maybe Theorem)
lookupPool id = StatefulVal $ \ls ->
  (foldl
    (\acc curr ->
      case acc of
        (Just thm) -> Just thm
        Nothing -> case Map.lookup id curr of
          (Just thm) -> Just thm
          Nothing -> Nothing)
    Nothing ls,
  ls)

-- Add theorem to the topmost pool and return it (for convenience).
addTheorem :: String -> Theorem -> WithState Theorem
addTheorem id thm = StatefulVal (\(top : ps) -> (thm, Map.insert id thm top : ps))

push :: WithState ()
push = StatefulVal (\ls -> ((), Map.empty : ls))

-- Apply a given introduction rule to each theorem, and then pop.
-- Pre: all theorems in the form of (Provable ctx, p) in the top layer must have the same context
introPop :: (Theorem -> Theorem) -> WithState ()
introPop intro = StatefulVal $ \(top : second : ls) -> ((),
  let
    second' = Map.foldlWithKey'
      (\acc id thm ->
        case thmJudgment thm of
          Provable p -> Map.insert id (intro thm) acc
          _          -> acc)
      second top
  in
    second' : ls)

-- If it is an assertion, apply a given introduction rule and return
introReturn :: (Theorem -> Theorem) -> Maybe Theorem -> WithState (Maybe Theorem)
introReturn intro thm' = return $ do
  thm <- thm';
  case thmJudgment thm of
    Provable p -> return (intro thm)
    _          -> Nothing

-- Check if a (non-context-changing) proof is well-formed; returns its judgment.
checkProof :: Context -> Proof -> WithState Theorem
checkProof ctx e = case e of
  (As id) -> do
    res <- lookupPool id;
    case res of
      (Just thm) -> return (weaken thm ctx);
      Nothing    -> return (assumption ctx id);
  (Decl decl) -> do res <- checkDecl ctx decl; return (fromJust res);
  (AndI p q) -> andIntro <$> checkProof ctx p <*> checkProof ctx q
  (AndL p) -> andLeft <$> checkProof ctx p
  (AndR p) -> andRight <$> checkProof ctx p
  (OrL p q) -> orLeft <$> checkProof ctx p <*> pure (convertAndCheck ctx q)
  (OrR p q) -> orRight <$> pure (convertAndCheck ctx p) <*> checkProof ctx q
  (OrE pq ps qs) -> orElim <$> checkProof ctx pq <*> checkProof ctx ps <*> checkProof ctx qs
  (ImpliesE pq p) -> impliesElim <$> checkProof ctx pq <*> checkProof ctx p
  (NotI p) -> notIntro <$> checkProof ctx p
  (NotE np p) -> notElim <$> checkProof ctx np <*> checkProof ctx p
  (IffI pq qp) -> iffIntro <$> checkProof ctx pq <*> checkProof ctx qp
  (IffL pq p) -> iffLeft <$> checkProof ctx pq <*> checkProof ctx p
  (IffR pq q) -> iffRight <$> checkProof ctx pq <*> checkProof ctx q
  (TrueI) -> pure (trueIntro ctx)
  (FalseE f p) -> falseElim <$> checkProof ctx f <*> pure (convertAndCheck ctx p)
  (RAA npf) -> raa <$> checkProof ctx npf
  (EqI t) -> eqIntro <$> pure (convertAndCheck ctx t)
  (EqE p ab pa) -> eqElim <$> pure (convertAndCheck ctx p) <*> checkProof ctx ab <*> checkProof ctx pa
  (ForallE px t) -> forallElim <$> checkProof ctx px <*> pure (convertAndCheck ctx t)
  (ExistsI p t pt) -> existsIntro <$> pure (convertAndCheck ctx p) <*> pure (convertAndCheck ctx t) <*> checkProof ctx pt
  (ExistsE epx pxq q) -> existsElim <$> checkProof ctx epx <*> checkProof ctx pxq <*> pure (convertAndCheck ctx q)
  (UniqueI ex one) -> uniqueIntro <$> checkProof ctx ex <*> checkProof ctx one
  (UniqueL uni) -> uniqueLeft <$> checkProof ctx uni
  (UniqueR uni) -> uniqueRight <$> checkProof ctx uni
  (ForallFuncE pf f) -> forallFuncElim <$> checkProof ctx pf <*> pure (convertAndCheck ctx f)

-- Check if a declaration is well-formed; returns the checked judgment of the last declaration (if applicable).
checkDecl :: Context -> Decl -> WithState (Maybe Theorem)
checkDecl ctx e = case e of
  -- Check block
  (Block []) -> return Nothing
  (Block [d]) -> checkDecl ctx d
  (Block (d : ds)) -> do checkDecl ctx d; checkDecl ctx (Block ds);
  -- Check assertion
  (Assertion id e pf) -> do
    thm <- checkProof ctx pf;
    case thmJudgment thm of
      (Provable e') ->
        case e of
          -- No indication
          Nothing -> do
            res <- addTheorem id thm;
            return (Just res);
          -- Check if proof and indicated statement match
          Just e''
            | thmJudgment (convertAndCheck ctx e'') == HasType e' TFormula -> do
                res <- addTheorem id thm;
                return (Just res);
            | otherwise -> error "Statement and proof does not match"
      -- The judgment of `thm` is not in the form of (Provable _)
      _ -> error "Not a proof"
  -- `any` section
  (Any x d) -> do
    push;
    thm' <- checkDecl (ctxVar x ctx) d;
    introPop forallIntro;
    introReturn forallIntro thm';
  -- `anyfunc` or `anyfunc` section
  (AnyFunc x k s d) -> do
    push;
    thm' <- checkDecl (ctxFunc x k s ctx) d;
    introPop forallFuncIntro;
    introReturn forallFuncIntro thm';
  -- `assume` section
  (Assume x e d) -> do
    push;
    thm' <- checkDecl (ctxAssumption x (convertAndCheck ctx e)) d;
    introPop impliesIntro;
    introReturn impliesIntro thm';
  -- Function definition
  (FuncDef s e) -> undefined
  -- Predicate definition
  (PredDef s e) -> undefined
  -- Function definition by definite description
  (FuncDDef s e pf) -> undefined
  -- Function definition by indefinit description
  (FuncIDef s e pf) -> undefined

-- TEMP CODE

var :: String -> Expr
var s = Var (Free s) []
func :: String -> [Expr] -> Expr
func = Var . Free

pool :: TheoremPool
pool = [Map.empty]

decls :: Decl
decls =
  AnyFunc "L" 2 SProp (AnyFunc "B" 3 SProp (Any "Q" (
    Assume "h1" (Forall "x" (Forall "y" (func "L" [var "x", var "y"] `Implies` Forall "z" (Not (Eq (var "z") (var "y")) `Implies` Not (func "L" [var "x", var "z"]))))) (
      Assume "h2" (Forall "x" (Forall "y" (Forall "z" (func "B" [var "x", var "y", var "z"] `Implies` (func "L" [var "x", var "z"] `Implies` func "L" [var "x", var "y"]))))) (
        Assume "h3" (Exists "x" (Not (Eq (var "x") (var "Q")) `And` Forall "y" (func "B" [var "y", var "x", var "Q"]))) (Block [
          Any "c" (Assume "hc" (Not (Eq (var "c") (var "Q")) `And` Forall "x" (func "B" [var "x", var "c", var "Q"])) (Block [
            Assertion "hc1" Nothing (AndL (As "hc")),
            Assertion "hc2" Nothing (AndR (As "hc")),
            Assume "hex" (Exists "x" (func "L" [var "x", var "Q"])) (Block [
              Any "x" (Assume "hx" (func "L" [var "x", var "Q"]) (Block [
                Assertion "t1" Nothing (ImpliesE (ForallE (ForallE (As "h1") (var "x")) (var "Q")) (As "hx")),
                Assertion "t2" Nothing (ImpliesE (ForallE (As "t1") (var "c")) (As "hc1")),
                Assertion "t3" Nothing (ForallE (As "hc2") (var "x")),
                Assertion "t4" Nothing (ImpliesE (ImpliesE (ForallE (ForallE (ForallE (As "h2") (var "x")) (var "c")) (var "Q")) (As "t3")) (As "hx")),
                Assertion "t5" Nothing (NotE (As "t2") (As "t4"))
              ])),
              Assertion "t6" Nothing (ExistsE (As "hex") (As "t5") Bottom)
            ]),
            Assertion "t7" Nothing (NotI (As "t6"))
          ])),
          Assertion "t8" (Just (Not (Exists "x" (func "L" [var "x", var "Q"]))))
            (ExistsE (As "h3") (As "t7") (Not (Exists "x" (func "L" [var "x", var "Q"]))))
        ])
      )
    )
  )))

res :: TheoremPool
res = snd $ eval (checkDecl ctxEmpty decls) pool

decls1 :: Decl
decls1 =
  Block [
    -- eq.symm, in natural style
    Any "x" (Any "y" (Assume "h" (var "x" `Eq` var "y") (Block [
      Assertion "t1" (Just $ var "x" `Eq` var "x") (EqI (var "x")),
      Assertion "eq.symm" (Just $ var "y" `Eq` var "x") (EqE (Lam "#" (var "#" `Eq` var "x")) (As "h") (As "t1"))
    ]))),
    -- eq.trans, in proof term style
    Assertion "eq.trans" (Just $ Forall "a" $ Forall "b" $ Forall "c" $ (var "a" `Eq` var "b") `Implies` ((var "b" `Eq` var "c") `Implies` (var "a" `Eq` var "c")))
      (Decl $ Any "x" $ Any "y" $ Any "z" $ Assume "h1" (var "x" `Eq` var "y") $ Assume "h2" (var "y" `Eq` var "z") (
        Assertion "" (Just $ var "x" `Eq` var "z") (EqE (Lam "#" (var "x" `Eq` var "#")) (As "h2") (As "h1"))
      ))
  ]

res1 :: TheoremPool
res1 = snd $ eval (checkDecl ctxEmpty decls1) pool

