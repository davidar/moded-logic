{-# LANGUAGE BangPatterns, DeriveDataTypeable, LambdaCase #-}

-- adapted from picologic (c) 2014-2020, Stephen Diehl
module Control.Monad.Logic.Moded.Solver
  ( Expr(..)
  , Solutions(..)
  , Ctx
  , Tseitin(..)
  , partEval
  , solveProp
  ) where

import Control.Monad.State.Strict (MonadState(..), StateT, evalStateT)
import Control.Monad.Writer.Strict (MonadWriter(..), Writer, runWriter)
import Data.Data (Data, Typeable)
import Data.List (group, sort)
import qualified Data.Map as M
import Data.Maybe (mapMaybe)
import Picosat (Solution(..), solveAll)
import Prelude hiding (and, or)

newtype Solutions v =
  Solutions [[Expr v]]

type Ctx v = M.Map v Bool

data Expr v
    -- | Variable
  = Var v
    -- | Logical negation
  | Neg (Expr v)
    -- | Logical conjunction
  | Conj (Expr v) (Expr v)
    -- | Logical disjunction
  | Disj (Expr v) (Expr v)
    -- | Logical biconditional
  | Iff (Expr v) (Expr v)
    -- | Material implication
  | Implies (Expr v) (Expr v)
    -- | Constant true
  | Top
    -- | Constant false
  | Bottom
  deriving (Eq, Ord, Data, Typeable)

type TS v a = StateT Int (Writer [Expr v]) a

instance Show v => Show (Expr v) where
  show =
    \case
      Var v -> show v
      Neg expr -> "~" ++ show expr
      Conj e1 e2 -> "(" ++ show e1 ++ " & " ++ show e2 ++ ")"
      Disj e1 e2 -> "(" ++ show e1 ++ " | " ++ show e2 ++ ")"
      Implies e1 e2 -> "(" ++ show e1 ++ " -> " ++ show e2 ++ ")"
      Iff e1 e2 -> "(" ++ show e1 ++ " <-> " ++ show e2 ++ ")"
      Top -> "1"
      Bottom -> "0"

-- | Evaluate expression.
eval :: Ord v => Ctx v -> Expr v -> Bool
eval vs (Var v) = Just True == M.lookup v vs
eval vs (Neg expr) = not $ eval vs expr
eval vs (Conj e1 e2) = eval vs e1 && eval vs e2
eval vs (Disj e1 e2) = eval vs e1 || eval vs e2
eval vs (Implies e1 e2) = not (eval vs e1) || eval vs e2
eval vs (Iff e1 e2) = eval vs e1 == eval vs e2
eval _ Top = True
eval _ Bottom = False

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
    go Top !vs = vs
    go Bottom !vs = vs

-- | Test if expression is constant.
isConst :: Expr v -> Bool
isConst Top = True
isConst Bottom = True
isConst _ = False

-- | Transform expression up from the bottom.
transformUp :: (Expr v -> Expr v) -> Expr v -> Expr v
transformUp f =
  \case
    Neg e -> f $ Neg (transformUp f e)
    Conj e1 e2 -> f $ Conj (transformUp f e1) (transformUp f e2)
    Disj e1 e2 -> f $ Disj (transformUp f e1) (transformUp f e2)
    Iff e1 e2 -> f $ Iff (transformUp f e1) (transformUp f e2)
    Implies e1 e2 -> f $ Implies (transformUp f e1) (transformUp f e2)
    e -> f e

-- | Propagate constants (to simplify expression).
propConst :: Expr v -> Expr v
propConst = transformUp propConst1

propConst1 :: Expr v -> Expr v
propConst1 =
  \case
    Neg (Neg e) -> e
    Neg Top -> Bottom
    Neg Bottom -> Top
    Conj Top e2 -> e2
    Conj Bottom _ -> Bottom
    Conj e1 Top -> e1
    Conj _ Bottom -> Bottom
    Disj Top _ -> Top
    Disj Bottom e2 -> e2
    Disj _ Top -> Top
    Disj e1 Bottom -> e1
    Iff Top Bottom -> Bottom
    Iff Bottom Top -> Bottom
    Iff Bottom Bottom -> Top
    Iff Top e2 -> e2
    Iff Bottom e2 -> Neg e2
    Iff e1 Top -> e1
    Iff e1 Bottom -> Neg e1
    Implies Top e2 -> e2
    Implies Bottom _ -> Top
    Implies _ Top -> Top
    Implies e1 Bottom -> Neg e1
    e -> e

-- | Substitute expressions for variables. This doesn't resolve any potential variable name conflicts.
subst :: Ord v => M.Map v (Expr v) -> Expr v -> Expr v
subst vs = transformUp (propConst1 . subst1)
  where
    subst1 (Var ident) = M.findWithDefault (Var ident) ident vs
    subst1 ex = ex

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
solveCNF p =
  if isConst p
    then return $
         if eval M.empty p
           then Solutions [[]]
           else Solutions []
    else do
      solutions <- solveAll ds
      return $
        dropTseitinVarsInSolutions $
        Solutions $ mapMaybe (backSubst vs') solutions
  where
    cs = clausesFromCNF p
    ds = cnfToDimacs vs cs
    vs = M.fromList $ zip vars [1 ..]
    vs' = M.fromList $ zip [1 ..] vars
    vars = variables p

clausesFromCNF :: Show v => Expr v -> [[Expr v]]
clausesFromCNF p = do
  clause <- ands [p]
  pure $ do
    lit <- ors [clause]
    pure $
      case lit of
        v@Var {} -> v
        v@(Neg Var {}) -> v
        _ -> error $ "input not in CNF: \n" ++ show p

ands :: [Expr v] -> [Expr v]
ands [] = []
ands (Conj a b:xs) = ands [a] ++ ands [b] ++ ands xs
ands (x:xs) = x : ands xs

ors :: [Expr v] -> [Expr v]
ors [] = []
ors (Disj a b:xs) = ors [a] ++ ors [b] ++ ors xs
ors (x:xs) = x : ors xs

cnfToDimacs :: Ord v => M.Map v Int -> [[Expr v]] -> [[Int]]
cnfToDimacs vs = map (map encode)
  where
    encode (Var ident) = vs M.! ident
    encode (Neg (Var ident)) = negate $ vs M.! ident
    encode _ = error "invalid input"

backSubst :: M.Map Int v -> Solution -> Maybe [Expr v]
backSubst env (Solution xs) = Just $ fmap go xs
  where
    go x
      | x >= 0 = Var (env M.! x)
      | otherwise = Neg (Var (env M.! abs x))
backSubst _ Unsatisfiable = Nothing
backSubst _ Unknown = Nothing

class Tseitin v where
  tseitinVar :: Int -> v
  isTseitinVar :: v -> Bool

evalTS :: TS v a -> (a, [Expr v])
evalTS action = runWriter (evalStateT action 1)

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
  let (v, clauses) = evalTS $ tseitin $ propConst e
   in and (v : clauses)

neg :: Expr v -> Expr v
neg (Neg x) = x
neg x = Neg x

tseitin :: Tseitin v => Expr v -> TS v (Expr v)
tseitin lit@(Var _) = return lit
tseitin lit@(Neg (Var _)) = return lit
tseitin (Conj x y) = do
  a <- tseitin x
  b <- tseitin y
  c <- var
  tell [or [neg a, neg b, c], or [a, neg c], or [b, neg c]]
  return c
tseitin (Neg (Conj x y)) = do
  a <- tseitin x
  b <- tseitin y
  c <- var
  tell [or [neg a, neg b, neg c], or [a, c], or [b, c]]
  return c
tseitin (Disj x y) = do
  a <- tseitin x
  b <- tseitin y
  c <- var
  tell [or [a, b, neg c], or [neg a, c], or [neg b, c]]
  return c
tseitin (Neg (Disj x y)) = do
  a <- tseitin x
  b <- tseitin y
  c <- var
  tell [or [a, b, c], or [neg a, neg c], or [neg b, neg c]]
  return c
tseitin (Implies x y) = do
  a <- tseitin x
  b <- tseitin y
  c <- var
  tell [or [neg a, b, neg c], or [a, c], or [neg b, c]]
  return c
tseitin (Neg (Implies x y)) = do
  a <- tseitin x
  b <- tseitin y
  c <- var
  tell [or [a, neg c], or [neg b, neg c], or [neg a, b, c]]
  return c
tseitin (Iff x y) = do
  a <- tseitin x
  b <- tseitin y
  c <- var
  tell
    [ or [neg a, b, neg c]
    , or [a, neg b, neg c]
    , or [a, b, c]
    , or [neg a, neg b, c]
    ]
  return c
tseitin (Neg (Iff x y)) = do
  a <- tseitin x
  b <- tseitin y
  c <- var
  tell
    [ or [a, b, neg c]
    , or [neg a, neg b, neg c]
    , or [neg a, b, c]
    , or [a, neg b, c]
    ]
  return c
tseitin (Neg x) = do
  a <- tseitin x
  c <- var
  tell [or [neg a, neg c], or [a, c]]
  return c
tseitin Top = return Top
tseitin Bottom = return Bottom

dropTseitinVarsInSolutions :: Tseitin v => Solutions v -> Solutions v
dropTseitinVarsInSolutions (Solutions xs) = Solutions $ map dropTseitinVars xs

dropTseitinVars :: Tseitin v => [Expr v] -> [Expr v]
dropTseitinVars = filter (not . isTseitinLiteral)

isTseitinLiteral :: Tseitin v => Expr v -> Bool
isTseitinLiteral (Var v) = isTseitinVar v
isTseitinLiteral (Neg (Var v)) = isTseitinVar v
isTseitinLiteral _ = False
