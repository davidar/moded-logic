{-# LANGUAGE LambdaCase #-}

module Control.Monad.Logic.Moded.Constraints
  ( Constraints
  , Mode(..)
  , ModeString(..)
  , Solution
  , constraints
  , inferModes
  , solveConstraintsMode
  ) where

import Control.Monad.Logic.Moded.AST
  ( Atom(..)
  , Func(..)
  , Goal(..)
  , Name
  , Rule(..)
  , Var(..)
  , subgoals
  )
import Control.Monad.Logic.Moded.Mode (Mode(..), ModeString(..))
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
import Data.Equivalence.Monad (EquivM, MonadEquiv(..), runEquivM)
import Data.Foldable (Foldable(toList))
import Data.List (nub, sort)
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Maybe (fromMaybe)
import qualified Data.Set as Set
import Data.Set (Set)

type Constraint = Sat.Expr CAtom

type Constraints = Set Constraint

data CAtom
  = Produce Var Path
  | ProduceArg Var Int
  | TseitinVar Int
  deriving (Eq, Ord)

type Modes = Map Name [ModeString]

type Solution = Map (Var, Path) Mode

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
cComp m p r = cGen m p r `Set.union` cGoal m p r

-- | General constraints (sec 5.2.2)
cGen :: Modes -> Path -> Rule Var Var -> Constraints
cGen m p r = cLocal m p r `Set.union` cExt p r

-- | Local constraints (sec 5.2.2)
cLocal :: Modes -> Path -> Rule Var Var -> Constraints
cLocal m p r = term p `Set.map` locs
  where
    nonnegs = insideNonneg . extract p $ ruleBody r
    env = Set.map V $ ruleName r `Set.insert` Map.keysSet m
    locs = (locals p r `Set.intersection` nonnegs) Set.\\ env

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
    Unif u f ->
      case toList f of
        [] -> Set.empty
        (v:vs) ->
          Set.fromList $ nand p u v : [term p v `Sat.Iff` term p v' | v' <- vs]
    Pred (V name) vars ->
      Sat.Neg (term p (V name)) `Set.insert` cPred m p r name vars

cModeString :: Path -> [Var] -> ModeString -> [Constraint]
cModeString p vars (ModeString modes) = do
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

cPred :: Modes -> Path -> Rule Var Var -> Name -> [Var] -> Constraints
cPred m p r name vars
  | Rule rname rvars _ <- r
  , name == rname
  , length vars == length rvars =
    Set.fromList $ do
      (u, v) <- zip vars rvars
      pure $ term p u `Sat.Iff` term [] v
  | Just modeset <- Map.lookup name m =
    Set.singleton . cOr . nub . sort $ cAnd . cModeString p vars <$> modeset
  | equiv <- Set.elems . equivClassOf $ V name
  , (`elem` ruleArgs r) `any` equiv =
    Set.fromList $ do
      (i, v) <- zip [1 ..] vars
      u <- equiv
      pure $ term p v `Sat.Iff` Sat.Var (ProduceArg u i)
  | otherwise =
    error $
    "unknown predicate " ++
    name ++ "/" ++ show (length vars) ++ " in " ++ show r
  where
    equivClasses :: EquivM s (Set Var) Var ()
    equivClasses =
      let f (Atom (Unif u (FVar v))) = equate u v
          f (Atom _) = pure ()
          f g = f `mapM_` subgoals g
       in f (ruleBody r)
    equivClassOf :: Var -> Set Var
    equivClassOf v =
      runEquivM Set.singleton Set.union (equivClasses >> classDesc v)

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

convertSolution :: [Constraint] -> Solution
convertSolution soln =
  Map.fromList $ do
    c <- soln
    pure $
      case c of
        Sat.Var (Produce v p) -> ((v, p), Out)
        Sat.Neg (Sat.Var (Produce v p)) ->
          case predMode v of
            [] -> ((v, p), In)
            ms -> ((v, p), PredMode ms)
        Sat.Var (ProduceArg v _) -> ((v, []), PredMode $ predMode v)
        Sat.Neg (Sat.Var (ProduceArg v _)) -> ((v, []), PredMode $ predMode v)
        _ -> undefined
  where
    predMode name = go 1
      where
        go i
          | Sat.Neg t `elem` soln = In : go (i + 1)
          | t `elem` soln = Out : go (i + 1)
          | otherwise = []
          where
            t = Sat.Var $ ProduceArg name i

extractModeString :: Rule Var Var -> Solution -> ModeString
extractModeString rule soln = ModeString $ f <$> ruleArgs rule
  where
    f (V "_") = Out
    f v = fromMaybe undefined $ Map.lookup (v, []) soln

inferModes :: Modes -> Rule Var Var -> [ModeString]
inferModes m rule = go []
  where
    go mss =
      let extra =
            Set.fromList $
            cOr . map Sat.Neg . cModeString [] (ruleArgs rule) <$> mss
       in case Sat.solveProp . cAnd . Set.elems $
               extra `Set.union` constraints m rule of
            Sat.Solutions [] -> mss
            Sat.Solutions (soln:_) ->
              go (extractModeString rule (convertSolution soln) : mss)

solveConstraintsMode :: Modes -> Rule Var Var -> ModeString -> [Solution]
solveConstraintsMode m rule ms = convertSolution <$> solutions
  where
    Sat.Solutions solutions =
      Sat.solveProp . cAnd $
      cModeString [] (ruleArgs rule) ms ++ Set.elems (constraints m rule)
