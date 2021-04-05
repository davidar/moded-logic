{-# LANGUAGE DeriveFunctor, DeriveFoldable #-}

module Control.Monad.Logic.Moded.AST
  ( Prog
  , Rule(..)
  , Goal(..)
  , Atom(..)
  , Var(..)
  , Name
  , body
  , subgoals
  ) where

import Data.List (intercalate)
import qualified Data.Set as Set
import Data.Set (Set)

type Name = String

newtype Var =
  V String
  deriving (Eq, Ord)

data Atom v
  = Unif v v
  | Func Name [v] v
  | Pred Name [v]
  deriving (Eq, Ord, Functor, Foldable)

data Goal v
  = Atom (Atom v)
  | Conj [Goal v]
  | Disj [Goal v]
  | Ifte (Goal v) (Goal v) (Goal v)
  deriving (Eq, Ord, Functor, Foldable)

data Rule u v =
  Rule Name [u] (Goal v)

type Path = [Int]

type Prog u v = [Rule u v]

instance Show Var where
  show (V v) = v

instance (Show v) => Show (Atom v) where
  show (Unif u v) = show u ++ " = " ++ show v
  show (Func ":" [h, t] u) = show u ++ " = " ++ show h ++ " : " ++ show t
  show (Func name vs u) = show u ++ " = " ++ unwords (name : map show vs)
  show (Pred name []) = name
  show (Pred name vs) = unwords (name : map show vs)

instance (Show v) => Show (Goal v) where
  show (Atom a) = show a
  show (Conj gs) = "(" ++ intercalate ", " (map show gs) ++ ")"
  show (Disj gs) = "(" ++ intercalate "; " (map show gs) ++ ")"
  show (Ifte c t e) =
    "if " <> show c <> " then " <> show t <> " else " <> show e

instance (Show u, Show v) => Show (Rule u v) where
  show (Rule name vars g) =
    unwords (name : map show vars) ++ " :- " ++ show g ++ "."

body :: Rule u v -> Goal v
body (Rule _ _ goal) = goal

subgoals :: Goal v -> [Goal v]
subgoals (Conj gs) = gs
subgoals (Disj gs) = gs
subgoals (Ifte c t e) = [c, t, e]