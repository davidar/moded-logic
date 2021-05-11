{-# LANGUAGE TupleSections, OverloadedStrings #-}

module Control.Monad.Logic.Moded.Schedule
  ( ModedVar(..)
  , Procedure(..)
  , CompiledPredicate(..)
  , CompiledProgram(..)
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
  ( Constraints
  , Mode(..)
  , ModeString(..)
  , Solution
  , constraints
  , inferModes
  , solveConstraintsMode
  )
import Control.Monad.Logic.Moded.Path (nonlocals)
import Control.Monad.Logic.Moded.Prelude (modesPrelude)
import Control.Monad.Logic.Moded.Preprocess
  ( Macro
  , inlinePreds
  , prunePreds
  , simp
  )
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
  MV
    { stripMode :: Var
    , varMode :: Mode
    }
  deriving (Eq, Ord)

data Procedure =
  Procedure
    { modeSolution :: Solution
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
  show (MV v m) = show v ++ "::" ++ show m

instance Semigroup CompiledProgram where
  CompiledProgram p m <> CompiledProgram p' m' =
    CompiledProgram (p <> p') (m <> m')

instance Monoid CompiledProgram where
  mempty = CompiledProgram [] []

data DepNode =
  DepNode
    { _iDepNode :: Int
    , unDepNode :: Goal ModedVar
    }
  deriving (Eq)

instance Show DepNode where
  show (DepNode i g) = "[" ++ show i ++ "] " ++ show g

instance Ord DepNode where
  DepNode i g `compare` DepNode j g' =
    case cost g `compare` cost g' of
      EQ -> (g, i) `compare` (g', j)
      r -> r

maxCandidates :: Int
maxCandidates = 64

cost :: Goal ModedVar -> Int
cost (Atom Unif {}) = 0
cost g@(Atom Pred {}) = 1 + length [v | MV v Out <- toList g]
cost g = sum $ cost <$> subgoals g

mode :: Rule Var Var -> Solution -> Either String (Rule ModedVar ModedVar)
mode r@(Rule name vars body) soln =
  case walk [] body of
    Left cyc ->
      Left $
      "mode ordering failure, cyclic dependency: " ++
      intercalate " -> " (show <$> toList cyc)
    Right body' -> Right $ Rule name (annotate [] <$> vars) body'
  where
    annotate _ (V "_") = MV (V "_") Out
    annotate p v =
      case Map.lookup (v, p) soln of
        Just m -> MV v m
        Nothing ->
          error $
          show r ++
          "\n" ++
          show (v, p) ++
          " not in " ++ show soln ++ " (perhaps this variable is unused?)"
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
    walk p (Anon n vs g) = do
      let Just (PredMode ms) = Map.lookup (n, []) soln
          vs' = zipWith MV vs ms
      g' <- walk (p ++ [0]) g
      pure $ Anon (MV n Out) vs' g'
    walk p (Atom (Pred n vs)) = pure . Atom $ Pred (MV n In) (annotate p <$> vs)
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
    modes =
      if null userModes
        then inferModes m rule
        else userModes
    eithers =
      trace ("inferring modes for rule " ++ show rule) $ do
        ms <- modes
        soln <-
          trace ("mode " ++ show ms) take maxCandidates $
          solveConstraintsMode m rule ms
        pure $
          case mode rule soln of
            Left e -> trace e $ Left e
            Right mr ->
              trace ("cost " ++ show (cost $ ruleBody mr)) $
              Right (ms, Procedure {modeSolution = soln, modedRule = mr})
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
                , v `Set.member` nl
                , MV v Out `notElem` g
                ]
              | (g, nl) <- gs
              ]
            outs =
              [ Set.fromList [v | v <- Set.elems nl, MV v Out `elem` g]
              | (g, nl) <- gs
              ]
        (i, (g, _)) <- zip [0 ..] gs
        (j, (h, _)) <- zip [0 ..] gs
        guard . not . Set.null $ Set.intersection (outs !! i) (ins !! j)
        return (DepNode i g, DepNode j h)
