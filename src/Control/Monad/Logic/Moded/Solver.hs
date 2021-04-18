{-# LANGUAGE BangPatterns, DeriveDataTypeable #-}
{-# OPTIONS_GHC -Wwarn #-}
-- adapted from picologic (c) 2014-2020, Stephen Diehl
module Control.Monad.Logic.Moded.Solver
  ( Expr (..)
  , Solutions (..)
  , Ctx
  , Tseitin(..)
  , partEval
  , solveProp
  ) where

import Prelude hiding (and, or)
import Data.Data ( Data, Typeable )
import Data.List ( (\\), group, sort )
import qualified Data.Map as M
import Data.Maybe ( fromMaybe, mapMaybe )
import Control.Monad.State.Strict
import Control.Monad.Writer.Strict

import Picosat ( Solution(..), solve, solveAll )

newtype Solutions v = Solutions [[Expr v]]

type Ctx v = M.Map v Bool

data Expr v
  = -- | Variable
    Var v
  | -- | Logical negation
    Neg (Expr v)
  | -- | Logical conjunction
    Conj (Expr v) (Expr v)
  | -- | Logical disjunction
    Disj (Expr v) (Expr v)
  | -- | Logical biconditional
    Iff (Expr v) (Expr v)
  | -- | Material implication
    Implies (Expr v) (Expr v)
  | -- | Constant true
    Top
  | -- | Constant false
    Bottom
  deriving (Eq, Ord, Data, Typeable)

type TS v a = StateT Int (Writer [Expr v]) a

instance Show v => Show (Expr v) where
  show ex = case ex of
    Var v         -> show v
    Neg expr      -> "~"++ show expr
    Conj e1 e2    -> "("++ show e1 ++" & "++ show e2 ++")"
    Disj e1 e2    -> "("++ show e1 ++" | "++ show e2 ++")"
    Implies e1 e2 -> "("++ show e1 ++" -> "++ show e2 ++")"
    Iff e1 e2     -> "("++ show e1 ++" <-> "++ show e2 ++")"
    Top           -> "1"
    Bottom        -> "0"

-- | Evaluate expression.
eval :: Ord v => Ctx v -> Expr v -> Bool
eval vs (Var v) = fromMaybe False (M.lookup v vs)
eval vs (Neg expr) = not $ eval vs expr
eval vs (Conj e1 e2) = eval vs e1 && eval vs e2
eval vs (Disj e1 e2) = eval vs e1 || eval vs e2
eval vs (Implies e1 e2) = not (eval vs e1) || eval vs e2
eval vs (Iff e1 e2) = eval vs e1 == eval vs e2
eval vs (Top) = True
eval vs (Bottom) = False

-- | Variables in expression
variables :: Ord v => Expr v -> [v]
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
nnf :: Expr v -> Expr v
nnf = transformDown nnf1 . propConst

nnf1 :: Expr v -> Expr v
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
cnf :: Eq v => Expr v -> Expr v
cnf = simp . cnf' . nnf
  where
    cnf' :: Expr v -> Expr v
    cnf' (Conj e1 e2) = cnf' e1 `Conj` cnf' e2
    cnf' (Disj e1 e2) = cnf' e1 `dist` cnf' e2
    cnf' e = e

    dist :: Expr v -> Expr v -> Expr v
    dist (Conj e11 e12) e2 = (e11 `dist` e2) `Conj` (e12 `dist` e2)
    dist e1 (Conj e21 e22) = (e1 `dist` e21) `Conj` (e1 `dist` e22)
    dist e1 e2 = e1 `Disj` e2

-- | Remove tautologies.
simp :: Eq v => Expr v -> Expr v
simp = transformUp (propConst1 . simp1)

simp1 :: Eq v => Expr v -> Expr v
simp1 ex = case ex of
  Disj e1 (Neg e2) | e1 == e2 -> Top
  Disj (Neg e1) e2 | e1 == e2 -> Top
  Conj e1 e2 | e1 == e2 -> e1
  e -> e

-- | Test if expression is constant.
isConst :: Expr v -> Bool
isConst Top = True
isConst Bottom = True
isConst e = False

-- | Transform expression up from the bottom.
transformUp :: (Expr v -> Expr v) -> Expr v -> Expr v
-- TODO: This could probably be done with Data.Data, but it's outside my capabilities for now.
transformUp f ex = case ex of
  Neg e -> f $ Neg (transformUp f e)
  Conj e1 e2 -> f $ Conj (transformUp f e1) (transformUp f e2)
  Disj e1 e2 -> f $ Disj (transformUp f e1) (transformUp f e2)
  Iff e1 e2 -> f $ Iff (transformUp f e1) (transformUp f e2)
  Implies e1 e2 -> f $ Implies (transformUp f e1) (transformUp f e2)
  e -> f e

-- | Transform expression down from the top.
transformDown :: (Expr v -> Expr v) -> Expr v -> Expr v
-- TODO: This could probably be done with Data.Data, but it's outside my capabilities for now.
transformDown f ex = case f ex of
  Neg e -> Neg (transformDown f e)
  Conj e1 e2 -> Conj (transformDown f e1) (transformDown f e2)
  Disj e1 e2 -> Disj (transformDown f e1) (transformDown f e2)
  Iff e1 e2 -> Iff (transformDown f e1) (transformDown f e2)
  Implies e1 e2 -> Implies (transformDown f e1) (transformDown f e2)
  e -> e

-- | Convert expression to list of all subexpressions.
toList :: Expr v -> [Expr v]
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
propConst :: Expr v -> Expr v
propConst = transformUp propConst1

propConst1 :: Expr v -> Expr v
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
subst :: Ord v => M.Map v (Expr v) -> Expr v -> Expr v
subst vs = transformUp (propConst1 . subst1 vs)
  where
    subst1 vs ex = case ex of
      Var ident -> M.findWithDefault ex ident vs
      e -> e

-- | Partially evaluate expression.
partEval :: Ord v => Ctx v -> Expr v -> Expr v
partEval vs = subst (M.map constants vs)
  where
    constants True = Top
    constants False = Bottom


-- | Yield the solutions for an expression using the PicoSAT solver.
solveProp :: (Ord v, Show v, Tseitin v) => Expr v -> IO (Solutions v)
solveProp p = solveCNF $ tseitinCNF p

-- | Yield the solutions for an expression using the PicoSAT
-- solver. The Expression must be in CNF form already.
solveCNF :: (Ord v, Show v, Tseitin v) => Expr v -> IO (Solutions v)
solveCNF p = if isConst p
             then
               return $ if eval M.empty p
                        then Solutions [[]]
                        else Solutions []
             else do
                 solutions <- solveAll ds
                 return $ dropTseitinVarsInSolutions $ Solutions $ mapMaybe (backSubst vs') solutions
  where
    cs = clausesFromCNF p
    ds = cnfToDimacs vs cs
    vs  = M.fromList $ zip vars [1..]
    vs' = M.fromList $ zip [1..] vars
    vars = variables p

-- | Yield one single solution for an expression using the PicoSAT
-- solver. The Expression must be in CNF form already.
solveOneCNF :: (Ord v, Show v) => Expr v -> IO (Maybe [Expr v])
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

clausesFromCNF :: Show v => Expr v -> [[Expr v]]
clausesFromCNF p = [ [ case lit of
                       v@(Var name) -> v
                       v@(Neg (Var name)) -> v
                       x -> error $ "input not in CNF: \n" ++ show p
                     | lit <- ors [clause] ]
                   | clause <- ands [p]]

ands :: [Expr v] -> [Expr v]
ands [] = []
ands (Conj a b : xs) = ands [a] ++ ands [b] ++ ands xs
ands (x:xs) = x : ands xs

ors :: [Expr v] -> [Expr v]
ors [] = []
ors (Disj a b : xs) = ors [a] ++ ors [b] ++ ors xs
ors (x:xs) = x : ors xs

cnfToDimacs :: Ord v => M.Map v Int -> [[Expr v]] -> [[Int]]
cnfToDimacs vs = map (map encode)
  where encode (Var ident)       = vs M.! ident
        encode (Neg (Var ident)) = negate $ vs M.! ident


-- | Yield the integer clauses given to the SAT solver.
clausesExpr :: (Ord v, Show v) => Expr v -> [[Int]]
clausesExpr p = ds
  where
    cs = clausesFromCNF p
    vs  = M.fromList $ zip vars [1..]
    vars = variables p
    ds = cnfToDimacs vs cs

backSubst :: M.Map Int v -> Solution -> Maybe [Expr v]
backSubst env (Solution xs) = Just $ fmap go xs
  where
    go x | x >= 0 = Var (env M.! x)
    go x | x < 0 = Neg (Var (env M.! abs x))
backSubst _ Unsatisfiable = Nothing
backSubst _ Unknown = Nothing

addVarsToSolutions :: Ord v => [v] -> Solutions v -> Solutions v
addVarsToSolutions vars (Solutions sols) = Solutions $ concatMap addVarsToSolution sols
  where
    addVarsToSolution sol = map (sol ++) $ sequence  [ [Var v, Neg(Var v)] | v <- newVars $ head sols ]
    newVars sol = vars \\ concatMap variables sol

-- TODO: How efficient is the `mappend` used by Writer?
-- TODO: For cases like (Conj (Conj a b) c) the introduction
--       of one Tseitin var can be enough.
-- TODO: The outermost (Conj (Conj ...) ...) needn't be
--       Tseitin encoded at all.
--       Also, the (Disj (Disj ...) ...) below, needn't be encoded
--       when they use only variables or negated variables.
--       Tseitin transformation can be used specifically there to
--       turn other expressions into variables.

class Tseitin v where
  tseitinVar :: Int -> v
  isTseitinVar :: v -> Bool

evalTS :: TS v a -> (a, [Expr v])
evalTS action =
  runWriter (evalStateT action 1)

var :: Tseitin v => TS v (Expr v)
var = do
  n <- get
  put $ succ n
  return $ Var $ tseitinVar n

or :: [Expr v] -> Expr v
or = foldl1 Disj
and :: [Expr v] -> Expr v
and = foldl1 Conj

tseitinCNF :: Tseitin v => Expr v -> Expr v
tseitinCNF e =
  let (var, clauses) = evalTS $ tseitin $ propConst e
  in and (var : clauses)

neg :: Expr v -> Expr v
neg (Neg x) = x
neg x       = Neg x

tseitin :: Tseitin v => Expr v -> TS v (Expr v)

tseitin lit@(Var _) = return lit

tseitin lit@(Neg (Var _)) = return lit

tseitin (Conj x y) = do
  a <- tseitin x
  b <- tseitin y
  c <- var
  tell [or [neg a, neg b, c],
        or [a, neg c],
        or [b, neg c]]
  return c

tseitin (Neg (Conj x y)) = do
  a <- tseitin x
  b <- tseitin y
  c <- var
  tell [or [neg a, neg b, neg c],
        or [a, c],
        or [b, c]]
  return c

tseitin (Disj x y) = do
  a <- tseitin x
  b <- tseitin y
  c <- var
  tell [or [a, b, neg c],
        or [neg a, c],
        or [neg b, c]]
  return c

tseitin (Neg (Disj x y)) = do
  a <- tseitin x
  b <- tseitin y
  c <- var
  tell [or [a, b, c],
        or [neg a, neg c],
        or [neg b, neg c]]
  return c


-- |
-- @
-- (c -> (a -> b)) & (-c -> -(a->b))
-- (-c | (-a | b)) & (c | (a&-b))
-- (-a|b|-c) & (a|c) & (-b|c)
-- @
tseitin (Implies x y) = do
  a <- tseitin x
  b <- tseitin y
  c <- var
  tell [or [neg a, b, neg c],
        or [a, c],
        or [neg b, c]]
  return c

-- |
-- @
-- (c -> -(a -> b)) & (-c -> (a->b))
-- (-c | (a&-b)) & (c | (-a|b))
-- (a|-c) & (-b|-c) & (-a|b|c)
-- @
tseitin (Neg (Implies x y)) = do
  a <- tseitin x
  b <- tseitin y
  c <- var
  tell [or [a, neg c],
        or [neg b, neg c],
        or [neg a, b, c]]
  return c

-- |
-- @
-- (c -> a == b) & (-c -> a /= b)
-- (-c | ((-a|b) & (a|-b))) & (c | ((a|b) & (-a|-b)))
-- (-a|b|-c) & (a|-b|-c) & (a|b|c) & (-a|-b|c)
-- @
tseitin (Iff x y) = do
  a <- tseitin x
  b <- tseitin y
  c <- var
  tell [or [neg a, b, neg c],
        or [a, neg b, neg c],
        or [a, b, c],
        or [neg a, neg b, c]]
  return c

-- |
-- @
-- (c -> a /= b) & (-c -> a == b)
-- (-c | ((a|b) & (-a|-b))) & (c | ((-a|b) & (a|-b)))
-- (a|b|-c) & (-a|-b|-c) & (-a|b|c) & (a|-b|c)
-- @
tseitin (Neg (Iff x y)) = do
  a <- tseitin x
  b <- tseitin y
  c <- var
  tell [or [a, b, neg c],
        or [neg a, neg b, neg c],
        or [neg a, b, c],
        or [a, neg b, c]]
  return c

tseitin (Neg x) = do
  a <- tseitin x
  c <- var
  tell [or [neg a, neg c],
        or [a, c]]
  return c

tseitin Top = return Top

tseitin Bottom = return Bottom

dropTseitinVarsInSolutions :: Tseitin v => Solutions v -> Solutions v
dropTseitinVarsInSolutions (Solutions xs) =
  Solutions $ map dropTseitinVars xs

dropTseitinVars :: Tseitin v => [Expr v] -> [Expr v]
dropTseitinVars = filter (\x -> not $ isTseitinLiteral x)

isTseitinLiteral :: Tseitin v => Expr v -> Bool
isTseitinLiteral lit =
  case lit of
    (Var v) -> isTseitinVar v
    (Neg (Var v)) -> isTseitinVar v
