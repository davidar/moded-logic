{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveLift, LambdaCase
  #-}

module Control.Monad.Logic.Moded.AST
  ( Prog(..)
  , Pragma(..)
  , Rule(..)
  , Goal(..)
  , Atom(..)
  , Var(..)
  , Mode(..)
  , ModeString(..)
  , Name
  , subgoals
  ) where

import Data.List (intercalate)
import Language.Haskell.TH.Syntax (Lift)

type Name = String

newtype Var =
  V Name
  deriving (Eq, Ord, Lift)

data Atom v
  = Unif v v
  | Func Name [v] v
  | Pred Name [v]
  deriving (Eq, Ord, Functor, Foldable, Lift)

data Goal v
  = Atom (Atom v)
  | Conj [Goal v]
  | Disj [Goal v]
  | Ifte (Goal v) (Goal v) (Goal v)
  | Anon v [v] (Goal v)
  deriving (Eq, Ord, Functor, Foldable, Lift)

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

data Mode
  = In
  | Out
  | PredMode [Mode]
  deriving (Eq, Ord)

newtype ModeString =
  ModeString
    { unModeString :: [Mode]
    }
  deriving (Eq, Ord)

instance Show Var where
  show (V v) = v

instance (Show v) => Show (Atom v) where
  show (Unif u v) = show u ++ " = " ++ show v
  show (Func ":" vs u)
    | length vs > 1 = show u ++ " = " ++ intercalate ":" (map show vs)
  show (Func name vs u) = show u ++ " = " ++ unwords (name : map show vs)
  show (Pred name []) = name
  show (Pred name vs) = unwords (name : map show vs)

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

instance Show Mode where
  show In = "I"
  show Out = "O"
  show (PredMode ms) = "P" ++ show (length ms) ++ show (ModeString ms)

instance Show ModeString where
  show (ModeString ms) = concat $ show <$> ms

subgoals :: Goal v -> [Goal v]
subgoals (Conj gs) = gs
subgoals (Disj gs) = gs
subgoals (Ifte c t e) = [c, t, e]
subgoals (Anon _ _ g) = [g]
subgoals (Atom _) = error "not a compound goal"
