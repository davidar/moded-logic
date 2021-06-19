module Control.Monad.Logic.Moded.Mode
  ( Mode(..)
  ) where

data Mode
  = In
  | Out
  | PredMode [Mode]
  deriving (Eq, Ord, Show)
