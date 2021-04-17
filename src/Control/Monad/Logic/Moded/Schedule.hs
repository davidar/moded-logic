{-# LANGUAGE TupleSections, OverloadedStrings #-}

module Control.Monad.Logic.Moded.Schedule
  ( ModedVar(..)
  , stripMode
  , mode'
  ) where

import Algebra.Graph.AdjacencyMap (edges, overlay, vertices)
import Algebra.Graph.AdjacencyMap.Algorithm (Cycle, topSort)
import Control.Monad (guard)
import Control.Monad.Logic.Moded.AST (Atom(..), Goal(..), Name, Rule(..), Var(..))
import Control.Monad.Logic.Moded.Constraints
  ( Constraints
  , CAtom(..)
  , Mode(..)
  , ModeString(..)
  , constraints
  , unsafeSolveConstraints
  )
import Control.Monad.Logic.Moded.Path (nonlocals)
import qualified Control.Monad.Logic.Moded.Solver as Sat
import Data.Foldable (Foldable(toList))
import Data.List (intercalate)
import qualified Data.Set as Set
import Data.Set (Set)

data ModedVar
  = In String
  | Out String
  deriving (Eq, Ord)

type CState
   = [( (Name, Int)
      , ( (Rule Var Var, Constraints)
        , [(Constraints, Either String (Rule ModedVar ModedVar))]))]

instance Show ModedVar where
  show (In v) = v ++ "::in"
  show (Out v) = v ++ "::out"

data DepNode =
  DepNode Int (Goal ModedVar)
  deriving (Eq)

instance Show DepNode where
  show (DepNode i g) = "[" ++ show i ++ "] " ++ show g

instance Ord DepNode where
  DepNode i g `compare` DepNode j g' =
    case priority g `compare` priority g' of
      EQ -> (g, i) `compare` (g', j)
      r -> r

stripMode :: ModedVar -> Var
stripMode (In v) = V v
stripMode (Out v) = V v

unDepNode :: DepNode -> Goal ModedVar
unDepNode (DepNode _ g) = g

priority :: Goal ModedVar -> Int
priority (Atom Unif{}) = 0
priority (Atom Func{}) = 1
priority g = 2 + length [v | Out v <- toList g]

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
      | t `Set.member` soln = Out v
      | Sat.Neg t `Set.member` soln = In v
      | v == "_" = Out v
      | otherwise = error $ show t ++ " not in " ++ show soln
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
    walk p (Anon n vs g) = do
      let vs' = do
            (i, V v) <- zip [1..] vs
            let t = Sat.Var $ ProduceArg n i
            pure $ if t `Set.member` soln then Out v
              else if Sat.Neg t `Set.member` soln then In v
              else error $ show t ++ " not in " ++ show soln
      g' <- walk (p ++ [0]) g
      pure $ Anon (annotate p n) vs' g'
    walk p (Atom a) = pure . Atom $ annotate p <$> a

mode' :: CState -> Rule Var Var -> CState
mode' procs rule@(Rule name vars _) =
  procs ++
  [ ( (name, length vars)
    , ( (rule, constraints m rule)
      , [ (soln, mode rule soln)
        | soln <- Set.elems $ unsafeSolveConstraints m rule
        ]))
  ]
  where
    builtins =
      [ ("succ", ["io", "oi", "ii"])
      , ("div",  ["iio", "iii"])
      , ("mod",  ["iio", "iii"])
      , ("divMod", ["iioo", "iioi", "iiio", "iiii"])
      , ("plus", ["iio", "ioi", "oii"])
      , ("times", ["iio", "ioi", "oii"])
      , ("timesInt", ["iio", "ioi", "oii"])
      , ("sum", ["io", "ii"])
      , ("empty", [""])
      , ("print", ["i"])
      ]
    m =
      builtins ++ do
        ((name', _), (_, procs')) <- procs
        pure . (name', ) $ do
          (soln, Right (Rule _ mvars _)) <- procs'
          pure . ModeString $ do
            mv <- mvars
            pure $
              case mv of
                In v -> case predMode (V v) soln of
                  [] -> MIn
                  ms -> MPred ms
                Out _ -> MOut

predMode :: Var -> Constraints -> [Mode]
predMode name soln = go 1
  where
    go i =
      let t = Sat.Var $ ProduceArg name i
       in if Sat.Neg t `Set.member` soln then MIn : go (i+1)
          else if t `Set.member` soln then MOut : go (i+1)
          else []

sortConj :: [(Goal ModedVar, Set Var)] -> Either (Cycle DepNode) [Goal ModedVar]
sortConj gs = map unDepNode <$> topSort (overlay vs es)
  where
    vs = vertices $ zipWith DepNode [0 ..] (fst <$> gs)
    es =
      edges $ do
        let ins =
              [ Set.fromList
                [v | V v <- Set.elems nl, In v `elem` g, Out v `notElem` g]
              | (g, nl) <- gs
              ]
            outs =
              [ Set.fromList [v | V v <- Set.elems nl, Out v `elem` g]
              | (g, nl) <- gs
              ]
        (i, (g, _)) <- zip [0 ..] gs
        (j, (h, _)) <- zip [0 ..] gs
        guard . not . Set.null $ Set.intersection (outs !! i) (ins !! j)
        return (DepNode i g, DepNode j h)
