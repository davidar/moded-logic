{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable,
  DeriveLift, LambdaCase #-}

module Control.Monad.Logic.Moded.AST
  ( Prog(..)
  , Pragma(..)
  , Rule(..)
  , Func(..)
  , Goal(..)
  , Atom(..)
  , Var(..)
  , Name
  , subgoals
  ) where

import Data.List (intercalate)
import Language.Haskell.TH.Syntax (Lift)

type Name = String

newtype Var =
  V Name
  deriving (Eq, Ord, Lift)

data Func v
  = Func Name [Func v]
  | FVar v
  deriving (Eq, Ord, Functor, Foldable, Traversable, Lift)

data Atom v
  = Unif v (Func v)
  | Pred v [v]
  deriving (Eq, Ord, Functor, Foldable, Traversable, Lift)

data Goal v
  = Atom (Atom v)
  | Conj [Goal v]
  | Disj [Goal v]
  | Ifte (Goal v) (Goal v) (Goal v)
  | Anon v [v] (Goal v)
  deriving (Eq, Ord, Functor, Foldable, Traversable, Lift)

data Rule u v =
  Rule
    { ruleName :: Name
    , ruleArgs :: [u]
    , ruleBody :: Goal v
    }
  deriving (Eq, Ord, Lift)

newtype Pragma =
  Pragma [Name]
  deriving (Eq, Ord, Lift)

data Prog u v =
  Prog [Pragma] [Rule u v]
  deriving (Eq, Ord, Lift)

instance Show Var where
  show (V v) = v

instance (Show v) => Show (Func v) where
  show (FVar v) = show v
  show (Func ":" vs)
    | length vs > 1 = intercalate ":" (map show vs)
  show (Func name vs) = unwords (name : map show vs)

instance (Show v) => Show (Atom v) where
  show (Unif u v) = show u ++ " = " ++ show v
  show (Pred name []) = show name
  show (Pred name vs) = unwords (show name : map show vs)

instance (Show v) => Show (Goal v) where
  show (Atom a) = show a
  show (Conj gs) = "(" ++ intercalate ", " (map show gs) ++ ")"
  show (Disj gs) = "(" ++ intercalate "; " (map show gs) ++ ")"
  show (Ifte c t e) =
    "if " <> show c <> " then " <> show t <> " else " <> show e
  show (Anon name vars g) =
    "(" ++ unwords (show name : map show vars) ++ " :- " ++ show g ++ ")"

instance (Show u, Show v) => Show (Rule u v) where
  show (Rule name vars g) =
    unwords (name : map show vars) ++ " :- " ++ show g ++ "."

instance Show Pragma where
  show (Pragma ws) = unwords ("#pragma" : ws) ++ "."

instance (Show u, Show v) => Show (Prog u v) where
  show (Prog pragmas rules) = unlines $ map show pragmas ++ map show rules

subgoals :: Goal v -> [Goal v]
subgoals (Conj gs) = gs
subgoals (Disj gs) = gs
subgoals (Ifte c t e) = [c, t, e]
subgoals (Anon _ _ g) = [g]
subgoals (Atom _) = error "not a compound goal"
