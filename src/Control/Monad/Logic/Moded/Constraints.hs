{-# LANGUAGE LambdaCase #-}

module Control.Monad.Logic.Moded.Constraints
  ( Constraints
  , CAtom(..)
  , Mode(..)
  , ModeString(..)
  , constraints
  , unsafeSolveConstraints
  ) where

import Control.Monad.Logic.Moded.AST
  ( Atom(..)
  , Goal(..)
  , Mode(..)
  , ModeString(..)
  , Name
  , Rule(..)
  , Var(..)
  )
import Control.Monad.Logic.Moded.Path
  ( Path
  , extendPath
  , extract
  , inside
  , insideNonneg
  , locals
  , nonlocals
  )
import qualified Control.Monad.Logic.Moded.Solver as Sat
import Data.List (nub, sort)
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import System.IO.Unsafe (unsafePerformIO)

type Constraint = Sat.Expr CAtom

type Constraints = Set Constraint

data CAtom
  = Produce Var Path
  | ProduceArg Var Int
  | TseitinVar Int
  deriving (Eq, Ord)

type Modes = Map Name [ModeString]

instance Show CAtom where
  show (Produce v p) = show v ++ show p
  show (ProduceArg v i) = show v ++ "(" ++ show i ++ ")"
  show (TseitinVar i) = "ts*" ++ show i

instance Sat.Tseitin CAtom where
  tseitinVar = TseitinVar
  isTseitinVar TseitinVar {} = True
  isTseitinVar _ = False

term :: Path -> Var -> Constraint
term p v = Sat.Var $ Produce v p

nand :: Path -> Var -> Var -> Constraint
nand p u v = Sat.Neg $ term p u `Sat.Conj` term p v

cOr :: [Constraint] -> Constraint
cOr = foldr Sat.Disj Sat.Bottom

cAnd :: [Constraint] -> Constraint
cAnd = foldr Sat.Conj Sat.Top

-- | Complete set of constraints (sec 5.2.2)
cComp :: Modes -> Path -> Rule Var Var -> Constraints
cComp m p r = cGen p r `Set.union` cGoal m p r

-- | General constraints (sec 5.2.2)
cGen :: Path -> Rule Var Var -> Constraints
cGen p r = cLocal p r `Set.union` cExt p r

-- | Local constraints (sec 5.2.2)
cLocal :: Path -> Rule Var Var -> Constraints
cLocal p r =
  term p `Set.map`
  (locals p r `Set.intersection` insideNonneg (extract p $ ruleBody r))

-- | External constraints (sec 5.2.2)
cExt :: Path -> Rule Var Var -> Constraints
cExt [] _ = Set.empty
cExt p r = (Sat.Neg . term p) `Set.map` (inside (init p) r Set.\\ inside p r)

-- | Goal-specific constraints
cGoal :: Modes -> Path -> Rule Var Var -> Constraints
cGoal m p r
  | Atom {} <- extract p (ruleBody r) = cAtom m p r
cGoal m p r =
  Set.unions [cComp m p' r | p' <- extendPath p r] `Set.union`
  case extract p (ruleBody r) of
    Disj {} -> cDisj p r
    Conj {} -> cConj p r
    Ifte {} -> cIte p r
    Anon {} -> cAnon p r
    Atom {} -> error "impossible"

-- | Disjunction constraints (sec 5.2.3)
cDisj :: Path -> Rule Var Var -> Constraints
cDisj p r =
  Set.fromList
    [ term p v `Sat.Iff` term p' v
    | v <- Set.elems $ nonlocals p r
    , p' <- extendPath p r
    ]

-- | Conjunction constraints (sec 5.2.3)
cConj :: Path -> Rule Var Var -> Constraints
cConj p r =
  Set.fromList $ do
    v <- Set.elems $ inside p r
    let ts = [term p' v | p' <- extendPath p r]
    (term p v `Sat.Iff` cOr ts) :
      [Sat.Neg (Sat.Conj s t) | s <- ts, t <- ts, s < t]

-- | If-then-else constraints (sec 5.2.3)
cIte :: Path -> Rule Var Var -> Constraints
cIte p r =
  Set.fromList . concat $
  [ [ term p v `Sat.Iff` (term pc v `Sat.Disj` term pt v `Sat.Disj` term pe v)
    | v <- vs
    ]
  , [Sat.Neg $ term pc v `Sat.Conj` term pt v | v <- vs]
  , [Sat.Neg $ term pc v | v <- nls]
  , [term pt v `Sat.Iff` term pe v | v <- nls]
  -- condition cannot consume variables produced by branches
  , [Sat.Neg $ term pt v | v <- Set.elems $ inside pc r]
  ]
  where
    vs = Set.elems $ inside p r
    nls = Set.elems $ nonlocals p r
    pc = p ++ [0]
    pt = p ++ [1]
    pe = p ++ [2]

-- | Higher-order terms (omitted from paper)
cAnon :: Path -> Rule Var Var -> Constraints
cAnon p r =
  Set.fromList $
  [Sat.Var (ProduceArg name i) `Sat.Iff` term p' v | (i, v) <- zip [1 ..] vs] ++
  [term p name] ++ [Sat.Neg $ term p v | v <- vs ++ Set.elems (nonlocals p' r)]
  where
    p' = p ++ [0]
    Anon name vs _ = extract p (ruleBody r)

-- | Atomic goals (sec 5.2.4)
cAtom :: Modes -> Path -> Rule Var Var -> Constraints
cAtom m p r =
  case let Atom a = extract p (ruleBody r)
        in a of
    Unif u v -> Set.singleton $ nand p u v
    Func _ [] _ -> Set.empty
    Func _ [v] u -> Set.singleton $ nand p u v
    Func _ (v:vs) u ->
      Set.fromList $ nand p u v : [term p v `Sat.Iff` term p v' | v' <- vs]
    Pred name vars
      | Rule rname rvars _ <- r
      , name == rname
      , length vars == length rvars ->
        Set.fromList $ do
          (u, v) <- zip vars rvars
          pure $ term p u `Sat.Iff` term [] v
      | Just modeset <- Map.lookup name m ->
        Set.singleton . cOr . nub . sort $ do
          ModeString modes <- modeset
          pure . cAnd $ do
            (v, mode) <- zip vars modes
            let t = term p v
            case mode of
              In -> pure $ Sat.Neg t
              Out -> pure t
              PredMode ms ->
                Sat.Neg t : do
                  (i, mode') <- zip [1 ..] ms
                  let t' = Sat.Var $ ProduceArg v i
                  pure $
                    case mode' of
                      In -> Sat.Neg t'
                      Out -> t'
                      PredMode _ -> error "nested modestring"
      | head name == '('
      , last name == ')' -> Set.singleton . cAnd $ Sat.Neg . term p <$> vars
      | V name `elem` ruleArgs r ->
        Set.fromList $ do
          (i, v) <- zip [1 ..] vars
          pure $ term p v `Sat.Iff` Sat.Var (ProduceArg (V name) i)
      | otherwise ->
        error $ "unknown predicate " ++ name ++ "/" ++ show (length vars)

constraints :: Modes -> Rule Var Var -> Constraints
constraints m rule = Set.map f cs
  where
    cs = cComp m [] rule
    env :: Sat.Ctx CAtom
    env =
      Map.fromList $
      [(i, True) | Sat.Var i <- Set.elems cs] ++
      [(i, False) | Sat.Neg (Sat.Var i) <- Set.elems cs]
    f c =
      case Sat.partEval env c of
        Sat.Bottom ->
          error $
          show rule ++ "\n" ++ show c ++ " always fails with " ++ show env
        e -> e

solveConstraints :: Modes -> Rule Var Var -> IO (Set Constraints)
solveConstraints m rule = do
  let cs = constraints m rule
  Sat.Solutions solutions <- Sat.solveProp . cAnd $ Set.elems cs
  return . Set.fromList $ Set.fromList <$> solutions

unsafeSolveConstraints :: Modes -> Rule Var Var -> Set Constraints
unsafeSolveConstraints m = unsafePerformIO . solveConstraints m
