{-# LANGUAGE BangPatterns, DeriveDataTypeable, DeriveFunctor,
  DeriveFoldable, LambdaCase #-}

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
import Data.Foldable (toList)
import Data.List (group, sort)
import qualified Data.Map as M
import Data.Maybe (mapMaybe)
import Picosat (Solution(..), unsafeSolve)
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
    -- | Constant true
  | Top
    -- | Constant false
  | Bottom
  deriving (Eq, Ord, Data, Typeable, Functor, Foldable)

type TS v a = StateT Int (Writer [Expr v]) a

instance Show v => Show (Expr v) where
  show =
    \case
      Var v -> show v
      Neg expr -> "~" ++ show expr
      Conj e1 e2 -> "(" ++ show e1 ++ " & " ++ show e2 ++ ")"
      Disj e1 e2 -> "(" ++ show e1 ++ " | " ++ show e2 ++ ")"
      Iff e1 e2 -> "(" ++ show e1 ++ " <-> " ++ show e2 ++ ")"
      Top -> "1"
      Bottom -> "0"

-- | Transform expression up from the bottom.
transformUp :: (Expr v -> Expr v) -> Expr v -> Expr v
transformUp f =
  \case
    Neg e -> f $ Neg (transformUp f e)
    Conj e1 e2 -> f $ Conj (transformUp f e1) (transformUp f e2)
    Disj e1 e2 -> f $ Disj (transformUp f e1) (transformUp f e2)
    Iff e1 e2 -> f $ Iff (transformUp f e1) (transformUp f e2)
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
solveProp :: (Ord v, Show v, Tseitin v) => Expr v -> Solutions v
solveProp p = solveCNF $ tseitinCNF p

-- | Yield the solutions for an expression using the PicoSAT
-- solver. The Expression must be in CNF form already.
solveCNF :: (Ord v, Show v, Tseitin v) => Expr v -> Solutions v
solveCNF Top = Solutions [[]]
solveCNF Bottom = Solutions []
solveCNF p =
  Solutions . mapMaybe (fmap dropTseitinVars . backSubst vs' . Solution) $
  unsafeSolveAll ds
  where
    cs = clausesFromCNF p
    ds = cnfToDimacs vs cs
    vs = M.fromList $ zip vars [1 ..]
    vs' = M.fromList $ zip [1 ..] vars
    vars = map head . group . sort $ toList p

unsafeSolveAll :: [[Int]] -> [[Int]]
unsafeSolveAll e =
  case unsafeSolve e of
    Solution x -> x : unsafeSolveAll (map negate x : e)
    _ -> []

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

dropTseitinVars :: Tseitin v => [Expr v] -> [Expr v]
dropTseitinVars = filter (not . isTseitinLiteral)

isTseitinLiteral :: Tseitin v => Expr v -> Bool
isTseitinLiteral (Var v) = isTseitinVar v
isTseitinLiteral (Neg (Var v)) = isTseitinVar v
isTseitinLiteral _ = False
