{-# LANGUAGE TupleSections, OverloadedStrings #-}

module Control.Monad.Logic.Moded.Schedule
  ( ModedVar(..)
  , Procedure(..)
  , CompiledPredicate(..)
  , CompiledProgram(..)
  , stripMode
  , varMode
  , cost
  , compileRule
  ) where

import Algebra.Graph.AdjacencyMap (edges, overlay, vertices)
import Algebra.Graph.AdjacencyMap.Algorithm (Cycle, topSort)
import Control.Monad (guard)
import Control.Monad.Logic.Moded.AST
  ( Atom(..)
  , Goal(..)
  , Name
  , Pragma(..)
  , Rule(..)
  , Var(..)
  , subgoals
  )
import Control.Monad.Logic.Moded.Constraints
  ( CAtom(..)
  , Constraints
  , Mode(..)
  , ModeString(..)
  , constraints
  , solveConstraints
  )
import Control.Monad.Logic.Moded.Path (nonlocals)
import Control.Monad.Logic.Moded.Prelude (modesPrelude)
import Control.Monad.Logic.Moded.Preprocess
  ( Macro
  , inlinePreds
  , prunePreds
  , simp
  )
import qualified Control.Monad.Logic.Moded.Solver as Sat
import Control.Monad.State (evalState)
import Data.Foldable (Foldable(toList))
import Data.List (intercalate)
import Data.List.Extra (groupSort)
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Debug.Trace

data ModedVar =
  MV Name Mode
  deriving (Eq, Ord)

data Procedure =
  Procedure
    { modeSolution :: Constraints
    , modedRule :: Rule ModedVar ModedVar
    }

data CompiledPredicate =
  CompiledPredicate
    { unmodedRule :: Rule Var Var
    , modeConstraints :: Constraints
    , procedures :: Map ModeString [Procedure]
    , errors :: [String]
    }

data CompiledProgram =
  CompiledProgram
    { predicates :: [(Name, CompiledPredicate)]
    , macros :: [(Name, Macro)]
    }

instance Show ModedVar where
  show (MV v m) = v ++ "::" ++ show m

instance Semigroup CompiledProgram where
  CompiledProgram p m <> CompiledProgram p' m' =
    CompiledProgram (p <> p') (m <> m')

instance Monoid CompiledProgram where
  mempty = CompiledProgram [] []

data DepNode =
  DepNode Int (Goal ModedVar)
  deriving (Eq)

instance Show DepNode where
  show (DepNode i g) = "[" ++ show i ++ "] " ++ show g

instance Ord DepNode where
  DepNode i g `compare` DepNode j g' =
    case cost g `compare` cost g' of
      EQ -> (g, i) `compare` (g', j)
      r -> r

stripMode :: ModedVar -> Var
stripMode (MV v _) = V v

varMode :: ModedVar -> Mode
varMode (MV _ m) = m

unDepNode :: DepNode -> Goal ModedVar
unDepNode (DepNode _ g) = g

cost :: Goal ModedVar -> Int
cost (Atom Unif {}) = 0
cost g@(Atom Pred {}) = 1 + length [v | MV v Out <- toList g]
cost g = sum $ cost <$> subgoals g

mode :: Rule Var Var -> Constraints -> Either String (Rule ModedVar ModedVar)
mode r@(Rule name vars body) soln =
  case walk [] body of
    Left cyc ->
      Left $
      "mode ordering failure, cyclic dependency: " ++
      intercalate " -> " (show <$> toList cyc)
    Right body' -> Right $ Rule name (annotate [] <$> vars) body'
  where
    annotate p (V v)
      | t `Set.member` soln || v == "_" = MV v Out
      | Sat.Neg t `Set.member` soln || null p =
        MV v $
        case predMode (V v) soln of
          [] -> In
          ms' -> PredMode ms'
      | otherwise =
        error $
        show r ++
        "\n" ++
        show t ++
        " not in " ++ show soln ++ " (perhaps this variable is unused?)"
      where
        t = Sat.Var $ Produce (V v) p
    walk p (Disj disj) =
      Disj <$> sequence [walk (p ++ [d]) g | (d, g) <- zip [0 ..] disj]
    walk p (Conj conj) = do
      conj' <- sequence [walk (p ++ [c]) g | (c, g) <- zip [0 ..] conj]
      conj'' <-
        sortConj [(g, nonlocals (p ++ [c]) r) | (c, g) <- zip [0 ..] conj']
      pure $ Conj conj''
    walk p (Ifte c t e) = do
      c' <- walk (p ++ [0]) c
      t' <- walk (p ++ [1]) t
      e' <- walk (p ++ [2]) e
      pure $ Ifte c' t' e'
    walk p (Anon (V n) vs g) = do
      let vs' = do
            (i, V v) <- zip [1 ..] vs
            let t = Sat.Var $ ProduceArg (V n) i
            pure $
              if t `Set.member` soln
                then MV v Out
                else if Sat.Neg t `Set.member` soln
                       then MV v In
                       else error $ show t ++ " not in " ++ show soln
      g' <- walk (p ++ [0]) g
      pure $ Anon (MV n Out) vs' g'
    walk p (Atom (Pred (V n) vs)) =
      pure . Atom $ Pred (MV n In) (annotate p <$> vs)
    walk p (Atom a) = pure . Atom $ annotate p <$> a

compileRule :: [Pragma] -> CompiledProgram -> Rule Var Var -> CompiledProgram
compileRule pragmas cp r
  | Pragma ["inline", ruleName r] `elem` pragmas =
    cp <> mempty {macros = [(ruleName r, (ruleArgs r, ruleBody r, mempty))]}
  | otherwise =
    trace
      ("generated " ++
       show (length [() | Right _ <- eithers]) ++
       " procedures and " ++ show (length $ errors obj) ++ " errors") $
    cp <> mempty {predicates = [(ruleName rule, obj)]}
  where
    rule =
      evalState
        (fixpt (fmap (simp . prunePreds) . inlinePreds m (macros cp)) r)
        0
    userModes = do
      Pragma ("mode":n:ms) <- pragmas
      guard $ n == ruleName r
      pure . ModeString $ do
        io <- ms
        pure $
          case io of
            "In" -> In
            "Out" -> Out
            _ -> undefined
    eithers = do
      soln <-
        trace ("inferring modes for rule " ++ show rule) $
        solveConstraints m rule
      case mode rule soln of
        Left e -> pure $ Left (traceId e)
        Right mr ->
          trace (show ms ++ " (cost " ++ show (cost $ ruleBody mr) ++ ")") $ do
            guard $ null userModes || ms `elem` userModes
            pure $ Right (ms, Procedure {modeSolution = soln, modedRule = mr})
          where ms =
                  ModeString $ do
                    MV _ mv <- ruleArgs mr
                    pure mv
    obj =
      CompiledPredicate
        { unmodedRule = rule
        , modeConstraints = constraints m rule
        , procedures = Map.fromList $ groupSort [kv | Right kv <- eithers]
        , errors = [e | Left e <- eithers]
        }
    m =
      flip Map.union (Map.map (map ModeString) modesPrelude) . Map.fromList $ do
        (name', c) <- predicates cp
        pure (name', Map.keys (procedures c))
    fixpt f x = do
      y <- f x
      if x == y
        then pure x
        else fixpt f y

predMode :: Var -> Constraints -> [Mode]
predMode name soln = go 1
  where
    go i =
      let t = Sat.Var $ ProduceArg name i
       in if Sat.Neg t `Set.member` soln
            then In : go (i + 1)
            else if t `Set.member` soln
                   then Out : go (i + 1)
                   else []

sortConj :: [(Goal ModedVar, Set Var)] -> Either (Cycle DepNode) [Goal ModedVar]
sortConj gs = map unDepNode <$> topSort (overlay vs es)
  where
    vs = vertices $ zipWith DepNode [0 ..] (fst <$> gs)
    es =
      edges $ do
        let ins =
              [ Set.fromList
                [ v
                | MV v m <- toList g
                , m /= Out
                , V v `Set.member` nl
                , MV v Out `notElem` g
                ]
              | (g, nl) <- gs
              ]
            outs =
              [ Set.fromList [v | V v <- Set.elems nl, MV v Out `elem` g]
              | (g, nl) <- gs
              ]
        (i, (g, _)) <- zip [0 ..] gs
        (j, (h, _)) <- zip [0 ..] gs
        guard . not . Set.null $ Set.intersection (outs !! i) (ins !! j)
        return (DepNode i g, DepNode j h)
