{-# LANGUAGE TupleSections, OverloadedStrings #-}

module Control.Monad.Logic.Moded.Schedule
  ( ModedVar(..)
  , Procedure(..)
  , CompiledPredicate(..)
  , stripMode
  , varMode
  , mode'
  ) where

import Algebra.Graph.AdjacencyMap (edges, overlay, vertices)
import Algebra.Graph.AdjacencyMap.Algorithm (Cycle, topSort)
import Control.Monad (guard)
import Control.Monad.Logic.Moded.AST
  ( Atom(..)
  , Goal(..)
  , Name
  , Rule(..)
  , Var(..)
  )
import Control.Monad.Logic.Moded.Constraints
  ( CAtom(..)
  , Constraints
  , Mode(..)
  , ModeString(..)
  , constraints
  , unsafeSolveConstraints
  )
import Control.Monad.Logic.Moded.Path (nonlocals)
import qualified Control.Monad.Logic.Moded.Solver as Sat
import Data.Foldable (Foldable(toList))
import Data.List (intercalate)
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)

data ModedVar =
  MV Name Mode
  deriving (Eq, Ord)

data Procedure =
  Procedure
    { modeSolution :: Constraints
    , procModeString :: ModeString
    , modedRule :: Rule ModedVar ModedVar
    }

data CompiledPredicate =
  CompiledPredicate
    { unmodedRule :: Rule Var Var
    , modeConstraints :: Constraints
    , procedures :: [Either String Procedure]
    }

type CompiledProgram = [(Name, CompiledPredicate)]

instance Show ModedVar where
  show (MV v m) = v ++ "::" ++ show m

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

builtins :: Map Name [ModeString]
builtins =
  Map.fromList
    [ ("succ", ["io", "oi", "ii"])
    , ("div", ["iio", "iii"])
    , ("mod", ["iio", "iii"])
    , ("divMod", ["iioo", "iioi", "iiio", "iiii"])
    , ("plus", ["iio", "ioi", "oii"])
    , ("times", ["iio", "ioi", "oii"])
    , ("timesInt", ["iio", "ioi", "oii"])
    , ("sum", ["io", "ii"])
    , ("maximum", ["io", "ii"])
    , ("empty", [""])
    , ("print", ["i"])
    , ("observeAll", [ModeString [MPred [MOut], MOut]])
    ]

stripMode :: ModedVar -> Var
stripMode (MV v _) = V v

varMode :: ModedVar -> Mode
varMode (MV _ m) = m

unDepNode :: DepNode -> Goal ModedVar
unDepNode (DepNode _ g) = g

priority :: Goal ModedVar -> Int
priority (Atom Unif {}) = 0
priority (Atom Func {}) = 1
priority g = 2 + length [v | MV v MOut <- toList g]

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
      | t `Set.member` soln = MV v MOut
      | Sat.Neg t `Set.member` soln =
        MV v $
        case predMode (V v) soln of
          [] -> MIn
          ms' -> MPred ms'
      | v == "_" = MV v MOut
      | null p = MV v MIn
      | otherwise = error $ show r ++ "\n" ++ show t ++ " not in " ++ show soln
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
                then MV v MOut
                else if Sat.Neg t `Set.member` soln
                       then MV v MIn
                       else error $ show t ++ " not in " ++ show soln
      g' <- walk (p ++ [0]) g
      pure $ Anon (MV n MOut) vs' g'
    walk p (Atom a) = pure . Atom $ annotate p <$> a

mode' :: CompiledProgram -> Rule Var Var -> CompiledProgram
mode' procs rule = procs ++ [(ruleName rule, obj)]
  where
    obj =
      CompiledPredicate
        { unmodedRule = rule
        , modeConstraints = constraints m rule
        , procedures =
            do soln <- Set.elems $ unsafeSolveConstraints m rule
               pure $ do
                 mr <- mode rule soln
                 let ms =
                       ModeString $ do
                         MV _ mv <- ruleArgs mr
                         pure mv
                 pure $
                   Procedure
                     {modeSolution = soln, procModeString = ms, modedRule = mr}
        }
    m =
      flip Map.union builtins . Map.fromList $ do
        (name', CompiledPredicate {procedures = procs'}) <- procs
        pure (name', [procModeString p | Right p <- procs'])

predMode :: Var -> Constraints -> [Mode]
predMode name soln = go 1
  where
    go i =
      let t = Sat.Var $ ProduceArg name i
       in if Sat.Neg t `Set.member` soln
            then MIn : go (i + 1)
            else if t `Set.member` soln
                   then MOut : go (i + 1)
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
                , m /= MOut
                , V v `Set.member` nl
                , MV v MOut `notElem` g
                ]
              | (g, nl) <- gs
              ]
            outs =
              [ Set.fromList [v | V v <- Set.elems nl, MV v MOut `elem` g]
              | (g, nl) <- gs
              ]
        (i, (g, _)) <- zip [0 ..] gs
        (j, (h, _)) <- zip [0 ..] gs
        guard . not . Set.null $ Set.intersection (outs !! i) (ins !! j)
        return (DepNode i g, DepNode j h)
