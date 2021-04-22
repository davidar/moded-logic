{-# LANGUAGE NoMonomorphismRestriction #-}
{-# OPTIONS_GHC -Wwarn #-}
module Control.Monad.Logic.Moded.Prelude where

import qualified Prelude
import Prelude (Eq(..), Num(..), Fractional(..), (.))
import Control.Applicative
import Control.Monad
import Control.Monad.IO.Class
import qualified Control.Monad.Logic as Logic
import Control.Monad.Logic.Moded.Relation

choose :: (Prelude.Foldable t, Alternative f) => t a -> f a
choose = Prelude.foldr ((<|>) . pure) empty

succ :: (Alternative m, Prelude.Eq a, Prelude.Enum a) => Relation2 m a a
succ = R2
  { callIO = pure . Prelude.succ
  , callOI = pure . Prelude.pred
  , callII = \a b -> guard (Prelude.succ a == b)
  }

div :: (Alternative m, Prelude.Integral a) => Relation3 m a a a
div = R3
  { callIIO = \a b -> pure (Prelude.div a b)
  , callIII = \a b c -> guard (Prelude.div a b == c)
  }

mod :: (Alternative m, Prelude.Integral a) => Relation3 m a a a
mod = R3
  { callIIO = \a b -> pure (Prelude.mod a b)
  , callIII = \a b c -> guard (Prelude.mod a b == c)
  }

divMod :: (Alternative m, Prelude.Integral a) => Relation4 m a a a a
divMod = R4
  { callIIOO = \a b -> pure (Prelude.divMod a b)
  , callIIOI = \a b m -> if Prelude.mod a b == m then pure (Prelude.div a b) else empty
  , callIIII = \a b d m -> guard (Prelude.divMod a b == (d, m))
  }

plus :: (Applicative m, Num a) => Relation3 m a a a
plus = R3
  { callIIO = \a b -> pure (a + b)
  , callIOI = \a c -> pure (c - a)
  , callOII = \b c -> pure (c - b)
  }

times :: (Applicative m, Fractional a) => Relation3 m a a a
times = R3
  { callIIO = \a b -> pure (a * b)
  , callIOI = \a c -> pure (c / a)
  , callOII = \b c -> pure (c / b)
  }

timesInt :: (Alternative m, Prelude.Integral a) => Relation3 m a a a
timesInt = R3
  { callIIO = \a b -> pure (a * b)
  , callIOI = \a c -> callIIOI divMod c a 0
  , callOII = \b c -> callIIOI divMod c b 0
  }

sum :: (Alternative m, Prelude.Foldable t, Num a, Eq a) => Relation2 m (t a) a
sum = R2
  { callIO = pure . Prelude.sum
  , callII = \xs s -> guard (Prelude.sum xs == s)
  }

maximum :: (Alternative m, Prelude.Foldable t, Prelude.Ord a) => Relation2 m (t a) a
maximum = R2
  { callIO = pure . Prelude.maximum
  , callII = \xs m -> guard (Prelude.maximum xs == m)
  }

print :: (MonadIO m, Prelude.Show a) => Relation1 m a
print = R1
  { callI = liftIO . Prelude.print
  }

show :: (Applicative m, Prelude.Show a, Prelude.Read a) => Relation2 m a Prelude.String
show = R2
  { callIO = pure . Prelude.show
  , callOI = pure . Prelude.read
  }

observeAll :: Applicative m => Relation2 m (Relation1 Logic.Logic a) [a]
observeAll = R2
  { callIO = pure . Logic.observeAll . callO
  }
