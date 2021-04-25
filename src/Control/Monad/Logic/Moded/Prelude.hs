{-# LANGUAGE NoMonomorphismRestriction, TypeOperators, DataKinds, FlexibleContexts, TypeFamilies, RankNTypes, TypeApplications, TypeFamilyDependencies, BlockArguments, ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wwarn #-}

module Control.Monad.Logic.Moded.Prelude where

import Control.Applicative (Applicative(..), Alternative(..))
import Control.Monad (guard)
import Control.Monad.IO.Class (MonadIO(..))
import qualified Control.Monad.Logic as Logic
import Control.Monad.Logic.Moded.Relation (Procedure(..), Relation, Out, In)
import Data.Vinyl (rget, type (∈), Rec(..))
import qualified Prelude
import Prelude (Eq(..), Fractional(..), Num(..), Ord(..), (.), ($))

choose :: (Prelude.Foldable t, Alternative f) => t a -> f a
choose = Prelude.foldr ((<|>) . pure) empty

succ :: (Alternative m, Prelude.Enum a, Eq a)
     => Relation m '[a, a] '[ '[In, In], '[In, Out], '[Out, In] ]
succ = (Procedure @'[In, In] \a b -> guard (Prelude.succ a == b))
    :& (Procedure @'[In, Out] \a -> pure (Prelude.succ a))
    :& (Procedure @'[Out, In] \b -> pure (Prelude.pred b))
    :& RNil

div :: (Alternative m, Prelude.Integral a)
    => Relation m '[a, a, a] '[ '[In, In, In], '[In, In, Out] ]
div = (Procedure @'[In, In, In] \a b c -> guard (Prelude.div a b == c))
   :& (Procedure @'[In, In, Out] \a b -> pure (Prelude.div a b))
   :& RNil

mod :: (Alternative m, Prelude.Integral a)
    => Relation m '[a, a, a] '[ '[In, In, In], '[In, In, Out] ]
mod = (Procedure @'[In, In, In] \a b c -> guard (Prelude.mod a b == c))
   :& (Procedure @'[In, In, Out] \a b -> pure (Prelude.mod a b))
   :& RNil

divMod :: (Alternative m, Prelude.Integral a)
       => Relation m '[a, a, a, a] '[ '[In, In, In, In], '[In, In, Out, In], '[In, In, Out, Out] ]
divMod = (Procedure @'[In, In, In, In] \a b d m -> guard (Prelude.divMod a b == (d, m)))
      :& (Procedure @'[In, In, Out, In] \a b m ->
          if Prelude.mod a b == m then pure (Prelude.div a b) else empty)
      :& (Procedure @'[In, In, Out, Out] \a b -> pure (Prelude.divMod a b))
      :& RNil

plus :: (Alternative m, Num a, Eq a)
     => Relation m '[a, a, a] '[ '[In, In, In], '[In, In, Out], '[In, Out, In], '[Out, In, In] ]
plus = (Procedure @'[In, In, In] \a b c -> guard (a + b == c))
    :& (Procedure @'[In, In, Out] \a b -> pure (a + b))
    :& (Procedure @'[In, Out, In] \a c -> pure (c - a))
    :& (Procedure @'[Out, In, In] \b c -> pure (c - b))
    :& RNil

times :: (Alternative m, Fractional a, Eq a)
     => Relation m '[a, a, a] '[ '[In, In, In], '[In, In, Out], '[In, Out, In], '[Out, In, In] ]
times = (Procedure @'[In, In, In] \a b c -> guard (a * b == c))
    :& (Procedure @'[In, In, Out] \a b -> pure (a * b))
    :& (Procedure @'[In, Out, In] \a c -> pure (c / a))
    :& (Procedure @'[Out, In, In] \b c -> pure (c / b))
    :& RNil

timesInt :: (Alternative m, Prelude.Integral a)
         => Relation m '[a, a, a] '[ '[In, In, In], '[In, In, Out], '[In, Out, In], '[Out, In, In] ]
timesInt = (Procedure @'[In, In, In] \a b c -> guard (a * b == c))
        :& (Procedure @'[In, In, Out] \a b -> pure (a * b))
        :& (Procedure @'[In, Out, In] \a c -> call (rget @'[In, In, Out, In] divMod) c a 0)
        :& (Procedure @'[Out, In, In] \b c -> call (rget @'[In, In, Out, In] divMod) c b 0)
        :& RNil

sum :: (Alternative m, Prelude.Foldable t, Num a, Eq a)
    => Relation m '[t a, a] '[ '[In, In], '[In, Out] ]
sum = (Procedure @'[In, In] \xs s -> guard (Prelude.sum xs == s))
   :& (Procedure @'[In, Out] \xs -> pure (Prelude.sum xs))
   :& RNil

maximum :: (Alternative m, Prelude.Foldable t, Ord a)
        => Relation m '[t a, a] '[ '[In, In], '[In, Out] ]
maximum = (Procedure @'[In, In] \xs s -> guard (Prelude.maximum xs == s))
       :& (Procedure @'[In, Out] \xs -> pure (Prelude.maximum xs))
       :& RNil

print :: (MonadIO m, Prelude.Show a) => Relation m '[a] '[ '[In] ]
print = (Procedure @'[In] $ liftIO . Prelude.print) :& RNil

show :: (Alternative m, Prelude.Read a, Prelude.Show a)
     => Relation m '[a, Prelude.String] '[ '[In, In], '[In, Out], '[Out, In] ]
show = (Procedure @'[In, In] \a s -> guard (Prelude.show a == s))
    :& (Procedure @'[In, Out] \a -> pure (Prelude.show a))
    :& (Procedure @'[Out, In] \s -> pure (Prelude.read s))
    :& RNil

observeAll :: (Applicative m, '[Out] ∈ rs) =>
  Relation m '[Relation Logic.Logic '[a] rs, [a]] '[ '[In, Out] ]
observeAll = (Procedure @'[In, Out] \p ->
              pure (Logic.observeAll (call (rget @'[Out] p))))
          :& RNil
