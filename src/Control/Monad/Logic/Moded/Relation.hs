module Control.Monad.Logic.Moded.Relation where

data Relation1 m a = R1
  { callI :: a -> m ()
  , callO :: m a
  }

data Relation2 m a b = R2
  { callII :: a -> b -> m ()
  , callIO :: a -> m b
  , callOI :: b -> m a
  , callOO :: m (a, b)
  }

data Relation3 m a b c = R3
  { callIII :: a -> b -> c -> m ()
  , callIIO :: a -> b -> m c
  , callIOI :: a -> c -> m b
  , callIOO :: a -> m (b, c)
  , callOII :: b -> c -> m a
  , callOIO :: b -> m (a, c)
  , callOOI :: c -> m (a, b)
  , callOOO :: m (a, b, c)
  }
