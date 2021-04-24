{-# LANGUAGE NoMonomorphismRestriction, TypeOperators, DataKinds #-}
{-# OPTIONS_GHC -Wwarn #-}

module Control.Monad.Logic.Moded.Prelude where

import Control.Applicative
import Control.Monad
import Control.Monad.IO.Class
import qualified Control.Monad.Logic as Logic
import Control.Monad.Logic.Moded.Relation
import qualified Prelude
import Prelude (Eq(..), Fractional(..), Num(..), Ord(..), (.), ($))

choose :: (Prelude.Foldable t, Alternative f) => t a -> f a
choose = Prelude.foldr ((<|>) . pure) empty

succ :: (Alternative m, Eq a, Prelude.Enum a) => Relation m () '[a, a]
succ =
  RIO
    (\a -> RIO
      (\b -> RNil $ guard (Prelude.succ a == b))
      (RNil $ pure (() :* Prelude.succ a)))
    (RI $ \b -> RNil $ pure (() :* Prelude.pred b))

div :: (Alternative m, Prelude.Integral a) => Relation m () '[a, a, a]
div = RI $ \a -> RI $ \b -> RIO
  (\c -> RNil $ guard (Prelude.div a b == c))
  (RNil $ pure (() :* Prelude.div a b))

mod :: (Alternative m, Prelude.Integral a) => Relation m () '[a, a, a]
mod = RI $ \a -> RI $ \b -> RIO
  (\c -> RNil $ guard (Prelude.mod a b == c))
  (RNil $ pure (() :* Prelude.mod a b))

divMod :: (Alternative m, Prelude.Integral a) => Relation m () '[a, a, a, a]
divMod = RI $ \a -> RI $ \b -> RIO
  (\d -> RI $ \m -> RNil $ guard (Prelude.divMod a b == (d, m)))
  (RIO
    (\m -> RNil $ if Prelude.mod a b == m then pure (() :* Prelude.div a b) else empty)
    (RNil $ pure (let (d,m) = Prelude.divMod a b in () :* d :* m)))

plus :: (Alternative m, Eq a, Num a) => Relation m () '[a, a, a]
plus = RIO
  (\a -> RIO
    (\b -> RIO
      (\c -> RNil $ guard (a + b == c))
      (RNil $ pure (() :* a + b)))
    (RI $ \c -> RNil $ pure (() :* c - a)))
  (RI $ \b -> RI $ \c -> RNil $ pure (() :* c - b))


times :: (Alternative m, Eq a, Fractional a) => Relation m () '[a, a, a]
times = RIO
  (\a -> RIO
    (\b -> RIO
      (\c -> RNil $ guard (a * b == c))
      (RNil $ pure (() :* a * b)))
    (RI $ \c -> RNil $ pure (() :* c / a)))
  (RI $ \b -> RI $ \c -> RNil $ pure (() :* c / b))

timesInt :: (Alternative m, Prelude.Integral a) => Relation m () '[a, a, a]
timesInt = RIO
  (\a -> RIO
    (\b -> RIO
      (\c -> RNil $ guard (a * b == c))
      (RNil $ pure (() :* a * b)))
    (RI $ \c -> callO (divMod `callI` c `callI` a) `callI` 0))
  (RI $ \b -> RI $ \c -> callO (divMod `callI` c `callI` b) `callI` 0)

sum :: (Alternative m, Prelude.Foldable t, Num a, Eq a) => Relation m () '[t a, a]
sum = RI $ \xs -> RIO
  (\s -> RNil $ guard (Prelude.sum xs == s))
  (RNil $ pure (() :* Prelude.sum xs))

maximum :: (Alternative m, Prelude.Foldable t, Ord a) => Relation m () '[t a, a]
maximum = RI $ \xs -> RIO
  (\s -> RNil $ guard (Prelude.maximum xs == s))
  (RNil $ pure (() :* Prelude.maximum xs))

print :: (MonadIO m, Prelude.Show a) => Relation m () '[a]
print = RI $ \a -> RNil $ liftIO $ Prelude.print a

show :: (Alternative m, Prelude.Show a, Prelude.Read a) => Relation m () '[a, Prelude.String]
show = RIO
    (\a -> RIO
      (\s -> RNil $ guard (Prelude.show a == s))
      (RNil $ pure (() :* Prelude.show a)))
    (RI $ \s -> RNil $ pure (() :* Prelude.read s))

observeAll :: (Alternative m, Eq a) => Relation m () '[Relation Logic.Logic () '[a], [a]]
observeAll = RI $ \p ->
  let q = do
        () :* x <- call (callO p)
        pure x
  in RIO
    (\o -> RNil $ guard (Logic.observeAll q == o))
    (RNil $ pure (() :* Logic.observeAll q))

