{-# LANGUAGE BangPatterns, DeriveDataTypeable #-}
{-# OPTIONS_GHC -Wwarn #-}
-- adapted from picologic (c) 2014-2020, Stephen Diehl
module Control.Monad.Logic.Moded.Solver
  ( Expr (..),
    Ident (..),
    Solutions (..),
    Ctx,
    variables,
    eval,
    cnf,
    nnf,
    simp,
    isConst,
    propConst,
    subst,
    partEval,

    solveProp,
    solveCNF,
    solveOneCNF,
    clausesExpr,
    addVarsToSolutions,
  )
where

import Data.Data ( Data, Typeable )
import Data.List ( (\\), group, sort )
import qualified Data.Map as M
import Data.Maybe ( fromMaybe, mapMaybe )
import qualified Data.Set as S
import Control.Monad.Writer ()

import Picosat ( Solution(..), solve, solveAll )

newtype Ident = Ident String
  deriving (Eq, Ord, Show, Data, Typeable)

newtype Solutions = Solutions [[Expr]]

type Ctx = M.Map Ident Bool

data Expr
  = -- | Variable
    Var Ident
  | -- | Logical negation
    Neg Expr
  | -- | Logical conjunction
    Conj Expr Expr
  | -- | Logical disjunction
    Disj Expr Expr
  | -- | Logical biconditional
    Iff Expr Expr
  | -- | Material implication
    Implies Expr Expr
  | -- | Constant true
    Top
  | -- | Constant false
    Bottom
  deriving (Eq, Ord, Data, Typeable)

instance Show Expr where
  show ex = case ex of
    Var (Ident n) -> n
    Neg expr      -> "~"++ show expr
    Conj e1 e2    -> "("++ show e1 ++" & "++ show e2 ++")"
    Disj e1 e2    -> "("++ show e1 ++" | "++ show e2 ++")"
    Implies e1 e2 -> "("++ show e1 ++" -> "++ show e2 ++")"
    Iff e1 e2     -> "("++ show e1 ++" <-> "++ show e2 ++")"
    Top           -> "1"
    Bottom        -> "0"

-- | Evaluate expression.
eval :: Ctx -> Expr -> Bool
eval vs (Var v) = fromMaybe False (M.lookup v vs)
eval vs (Neg expr) = not $ eval vs expr
eval vs (Conj e1 e2) = eval vs e1 && eval vs e2
eval vs (Disj e1 e2) = eval vs e1 || eval vs e2
eval vs (Implies e1 e2) = not (eval vs e1) || eval vs e2
eval vs (Iff e1 e2) = eval vs e1 == eval vs e2
eval vs (Top) = True
eval vs (Bottom) = False

-- | Variables in expression
variables :: Expr -> [Ident]
variables expr = map head . group . sort $ go expr []
  where
    go (Var v) !vs = v : vs
    go (Neg e) !vs = go e vs
    go (Conj e1 e2) !vs = go e1 vs ++ go e2 vs
    go (Disj e1 e2) !vs = go e1 vs ++ go e2 vs
    go (Iff e1 e2) !vs = go e1 vs ++ go e2 vs
    go (Implies e1 e2) !vs = go e1 vs ++ go e2 vs
    go (Top) !vs = vs
    go (Bottom) !vs = vs

-- | Negation normal form.
-- (May result in exponential growth)
nnf :: Expr -> Expr
nnf = transformDown nnf1 . propConst

nnf1 :: Expr -> Expr
nnf1 ex = case ex of
  Neg (Neg e) -> nnf1 e
  Neg (Conj e1 e2) -> Neg e1 `Disj` Neg e2
  Neg (Disj e1 e2) -> Neg e1 `Conj` Neg e2
  Implies e1 e2 -> Neg e1 `Disj` e2
  Neg (Implies e1 e2) -> e1 `Conj` Neg e2
  Iff e1 e2 ->
    let a = e1 `Disj` Neg e2
        b = Neg e1 `Disj` e2
     in a `Conj` b
  Neg (Iff e1 e2) ->
    let a = e1 `Disj` e2
        b = Neg e1 `Disj` Neg e2
     in a `Conj` b
  e -> e

-- | Conjunctive normal form.
-- (May result in exponential growth)
cnf :: Expr -> Expr
cnf = simp . cnf' . nnf
  where
    cnf' :: Expr -> Expr
    cnf' (Conj e1 e2) = cnf' e1 `Conj` cnf' e2
    cnf' (Disj e1 e2) = cnf' e1 `dist` cnf' e2
    cnf' e = e

    dist :: Expr -> Expr -> Expr
    dist (Conj e11 e12) e2 = (e11 `dist` e2) `Conj` (e12 `dist` e2)
    dist e1 (Conj e21 e22) = (e1 `dist` e21) `Conj` (e1 `dist` e22)
    dist e1 e2 = e1 `Disj` e2

-- | Remove tautologies.
simp :: Expr -> Expr
simp = transformUp (propConst1 . simp1)

simp1 :: Expr -> Expr
simp1 ex = case ex of
  Disj e1 (Neg e2) | e1 == e2 -> Top
  Disj (Neg e1) e2 | e1 == e2 -> Top
  Conj e1 e2 | e1 == e2 -> e1
  e -> e

-- | Test if expression is constant.
isConst :: Expr -> Bool
isConst Top = True
isConst Bottom = True
isConst e = False

-- | Transform expression up from the bottom.
transformUp :: (Expr -> Expr) -> Expr -> Expr
-- TODO: This could probably be done with Data.Data, but it's outside my capabilities for now.
transformUp f ex = case ex of
  Neg e -> f $ Neg (transformUp f e)
  Conj e1 e2 -> f $ Conj (transformUp f e1) (transformUp f e2)
  Disj e1 e2 -> f $ Disj (transformUp f e1) (transformUp f e2)
  Iff e1 e2 -> f $ Iff (transformUp f e1) (transformUp f e2)
  Implies e1 e2 -> f $ Implies (transformUp f e1) (transformUp f e2)
  e -> f e

-- | Transform expression down from the top.
transformDown :: (Expr -> Expr) -> Expr -> Expr
-- TODO: This could probably be done with Data.Data, but it's outside my capabilities for now.
transformDown f ex = case f ex of
  Neg e -> Neg (transformDown f e)
  Conj e1 e2 -> Conj (transformDown f e1) (transformDown f e2)
  Disj e1 e2 -> Disj (transformDown f e1) (transformDown f e2)
  Iff e1 e2 -> Iff (transformDown f e1) (transformDown f e2)
  Implies e1 e2 -> Implies (transformDown f e1) (transformDown f e2)
  e -> e

-- | Convert expression to list of all subexpressions.
toList :: Expr -> [Expr]
-- TODO: This could probably be done with Data.Data, but it's outside my capabilities for now.
toList ex =
  ex : case ex of
    Var ident -> []
    Neg e -> toList e
    Conj e1 e2 -> toList e1 ++ toList e2
    Disj e1 e2 -> toList e1 ++ toList e2
    Iff e1 e2 -> toList e1 ++ toList e2
    Implies e1 e2 -> toList e1 ++ toList e2
    Top -> []
    Bottom -> []

-- | Propagate constants (to simplify expression).
propConst :: Expr -> Expr
propConst = transformUp propConst1

propConst1 :: Expr -> Expr
propConst1 ex = case ex of
  Neg (Neg e) -> e
  Neg Top -> Bottom
  Neg Bottom -> Top
  Conj Top e2 -> e2
  Conj Bottom e2 -> Bottom
  Conj e1 Top -> e1
  Conj e1 Bottom -> Bottom
  Disj Top e2 -> Top
  Disj Bottom e2 -> e2
  Disj e1 Top -> Top
  Disj e1 Bottom -> e1
  Iff Top Bottom -> Bottom
  Iff Bottom Top -> Bottom
  Iff Bottom Bottom -> Top
  Iff Top e2 -> e2
  Iff Bottom e2 -> Neg e2
  Iff e1 Top -> e1
  Iff e1 Bottom -> Neg e1
  Implies Top e2 -> e2
  Implies Bottom e2 -> Top
  Implies e1 Top -> Top
  Implies e1 Bottom -> Neg e1
  e -> e

-- | Substitute expressions for variables. This doesn't resolve any potential variable name conflicts.
subst :: M.Map Ident Expr -> Expr -> Expr
subst vs = transformUp (propConst1 . subst1 vs)
  where
    subst1 vs ex = case ex of
      Var ident -> M.findWithDefault ex ident vs
      e -> e

-- | Partially evaluate expression.
partEval :: Ctx -> Expr -> Expr
partEval vs = subst (M.map constants vs)
  where
    constants True = Top
    constants False = Bottom


-- | Yield the solutions for an expression using the PicoSAT solver.
solveProp :: Expr -> IO Solutions
solveProp p = solveCNF $ cnf p

-- | Yield the solutions for an expression using the PicoSAT
-- solver. The Expression must be in CNF form already.
solveCNF :: Expr -> IO Solutions
solveCNF p = if isConst p
             then
               return $ if eval M.empty p
                        then Solutions [[]]
                        else Solutions []
             else do
                 solutions <- solveAll ds
                 return $ Solutions $ mapMaybe (backSubst vs') solutions
  where
    cs = clausesFromCNF p
    ds = cnfToDimacs vs cs
    vs  = M.fromList $ zip vars [1..]
    vs' = M.fromList $ zip [1..] vars
    vars = variables p

-- | Yield one single solution for an expression using the PicoSAT
-- solver. The Expression must be in CNF form already.
solveOneCNF :: Expr -> IO (Maybe [Expr])
solveOneCNF p = if isConst p
                then
                  return $ if eval M.empty p
                           then Just []
                           else Nothing
                else do
                  solution <- solve ds
                  return $ backSubst vs' solution
  where
    cs = clausesFromCNF p
    ds = cnfToDimacs vs cs
    vs  = M.fromList $ zip vars [1..]
    vs' = M.fromList $ zip [1..] vars
    vars = variables p

clausesFromCNF :: Expr -> [[Expr]]
clausesFromCNF p = [ [ case lit of
                       v@(Var name) -> v
                       v@(Neg (Var name)) -> v
                       x -> error $ "input not in CNF: \n" ++ show p
                     | lit <- ors [clause] ]
                   | clause <- ands [p]]

ands :: [Expr] -> [Expr]
ands [] = []
ands (Conj a b : xs) = ands [a] ++ ands [b] ++ ands xs
ands (x:xs) = x : ands xs

ors :: [Expr] -> [Expr]
ors [] = []
ors (Disj a b : xs) = ors [a] ++ ors [b] ++ ors xs
ors (x:xs) = x : ors xs

cnfToDimacs :: M.Map Ident Int -> [[Expr]] -> [[Int]]
cnfToDimacs vs = map (map encode)
  where encode (Var ident)       = vs M.! ident
        encode (Neg (Var ident)) = negate $ vs M.! ident


-- | Yield the integer clauses given to the SAT solver.
clausesExpr :: Expr -> [[Int]]
clausesExpr p = ds
  where
    cs = clausesFromCNF p
    vs  = M.fromList $ zip vars [1..]
    vars = variables p
    ds = cnfToDimacs vs cs

backSubst :: M.Map Int Ident -> Solution -> Maybe [Expr]
backSubst env (Solution xs) = Just $ fmap go xs
  where
    go x | x >= 0 = Var (env M.! x)
    go x | x < 0 = Neg (Var (env M.! abs x))
backSubst _ Unsatisfiable = Nothing
backSubst _ Unknown = Nothing

addVarsToSolutions :: [Ident] -> Solutions -> Solutions
addVarsToSolutions vars (Solutions sols) = Solutions $ concatMap addVarsToSolution sols
  where
    addVarsToSolution sol = map (sol ++) $ sequence  [ [Var v, Neg(Var v)] | v <- newVars $ head sols ]
    newVars sol = vars \\ concatMap variables sol
