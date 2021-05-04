module Control.Monad.Logic.Moded.Mode
  ( Mode(..)
  , ModeString(..)
  ) where

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

instance Show Mode where
  show In = "I"
  show Out = "O"
  show (PredMode ms) = "P" ++ show (length ms) ++ show (ModeString ms)

instance Show ModeString where
  show (ModeString ms) = concat $ show <$> ms
