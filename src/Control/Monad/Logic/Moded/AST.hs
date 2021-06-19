{-# LANGUAGE DeriveTraversable #-}

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

type Name = String

newtype Var =
  V Name
  deriving (Eq, Ord)

data Func v
  = Func Name [Func v]
  | FVar v
  deriving (Eq, Ord, Functor, Foldable, Traversable)

data Atom v
  = Unif v (Func v)
  | Pred v [v]
  deriving (Eq, Ord, Functor, Foldable, Traversable)

data Goal v
  = Atom (Atom v)
  | Conj [Goal v]
  | Disj [Goal v]
  | Ifte (Goal v) (Goal v) (Goal v)
  | Anon v [v] (Goal v)
  deriving (Eq, Ord, Functor, Foldable, Traversable)

data Rule u v =
  Rule
    { ruleName :: Name
    , ruleArgs :: [u]
    , ruleBody :: Goal v
    }
  deriving (Eq)

data Pragma
  = Pragma [Name]
  | TypeSig Name [Name] [Name]
  deriving (Eq, Show)

data Prog u v =
  Prog [Pragma] [Rule u v]

subgoals :: Goal v -> [Goal v]
subgoals (Conj gs) = gs
subgoals (Disj gs) = gs
subgoals (Ifte c t e) = [c, t, e]
subgoals (Anon _ _ g) = [g]
subgoals (Atom _) = error "not a compound goal"
