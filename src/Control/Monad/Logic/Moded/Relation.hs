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

data Relation4 m a b c d = R4
  { callIIII :: a -> b -> c -> d -> m ()
  , callIIIO :: a -> b -> c -> m d
  , callIIOI :: a -> b -> d -> m c
  , callIIOO :: a -> b -> m (c, d)
  , callIOII :: a -> c -> d -> m b
  , callIOIO :: a -> c -> m (b, d)
  , callIOOI :: a -> d -> m (b, c)
  , callIOOO :: a -> m (b, c, d)
  , callOIII :: b -> c -> d -> m a
  , callOIIO :: b -> c -> m (a, d)
  , callOIOI :: b -> d -> m (a, c)
  , callOIOO :: b -> m (a, c, d)
  , callOOII :: c -> d -> m (a, b)
  , callOOIO :: c -> m (a, b, d)
  , callOOOI :: d -> m (a, b, c)
  , callOOOO :: m (a, b, c, d)
  }
