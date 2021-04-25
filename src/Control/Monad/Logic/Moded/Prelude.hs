{-# LANGUAGE NoMonomorphismRestriction, TypeOperators, DataKinds, FlexibleContexts, TypeFamilies #-}
{-# OPTIONS_GHC -Wwarn #-}

module Control.Monad.Logic.Moded.Prelude where

import Control.Applicative (Applicative(..), Alternative(..))
import Control.Monad (guard)
import Control.Monad.IO.Class (MonadIO(..))
import qualified Control.Monad.Logic as Logic
import Control.Monad.Logic.Moded.Relation
import qualified Prelude
import Prelude (Eq(..), Fractional(..), Num(..), Ord(..), (.), ($))

choose :: (Prelude.Foldable t, Alternative f) => t a -> f a
choose = Prelude.foldr ((<|>) . pure) empty

succ =
  RIO
    (\a -> RIO
      (\b -> RNil $ guard (Prelude.succ a == b))
      (RNil $ pure (Prelude.succ a)))
    (RI $ \b -> RNil $ pure (Prelude.pred b))

div = RI $ \a -> RI $ \b -> RIO
  (\c -> RNil $ guard (Prelude.div a b == c))
  (RNil $ pure (Prelude.div a b))

mod = RI $ \a -> RI $ \b -> RIO
  (\c -> RNil $ guard (Prelude.mod a b == c))
  (RNil $ pure (Prelude.mod a b))

divMod = RI $ \a -> RI $ \b -> RIO
  (\d -> RI $ \m -> RNil $ guard (Prelude.divMod a b == (d, m)))
  (RIO
    (\m -> RNil $ if Prelude.mod a b == m then pure (Prelude.div a b) else empty)
    (RNil $ pure (Prelude.divMod a b)))

plus = RIO
  (\a -> RIO
    (\b -> RIO
      (\c -> RNil $ guard (a + b == c))
      (RNil $ pure (a + b)))
    (RI $ \c -> RNil $ pure (c - a)))
  (RI $ \b -> RI $ \c -> RNil $ pure (c - b))

times = RIO
  (\a -> RIO
    (\b -> RIO
      (\c -> RNil $ guard (a * b == c))
      (RNil $ pure (a * b)))
    (RI $ \c -> RNil $ pure (c / a)))
  (RI $ \b -> RI $ \c -> RNil $ pure (c / b))

timesInt = RIO
  (\a -> RIO
    (\b -> RIO
      (\c -> RNil $ guard (a * b == c))
      (RNil $ pure (a * b)))
    (RI $ \c -> RNil $ call (In :> In :> Out :> In :> Nil) divMod c a 0))
  (RI $ \b -> RI $ \c -> RNil $ call (In :> In :> Out :> In :> Nil) divMod c b 0)

sum = RI $ \xs -> RIO
  (\s -> RNil $ guard (Prelude.sum xs == s))
  (RNil $ pure (Prelude.sum xs))

maximum = RI $ \xs -> RIO
  (\s -> RNil $ guard (Prelude.maximum xs == s))
  (RNil $ pure (Prelude.maximum xs))

print = RI $ \a -> RNil $ liftIO $ Prelude.print a

show = RIO
    (\a -> RIO
      (\s -> RNil $ guard (Prelude.show a == s))
      (RNil $ pure (Prelude.show a)))
    (RI $ \s -> RNil $ pure (Prelude.read s))

observeAll = RI $ \p ->
  RIO
    (\o -> RNil $ guard (Logic.observeAll (call (Out :> Nil) p) == o))
    (RNil $ pure (Logic.observeAll (call (Out :> Nil) p)))
