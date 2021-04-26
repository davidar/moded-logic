{-# LANGUAGE NoMonomorphismRestriction, TypeOperators, DataKinds, FlexibleContexts, TypeFamilies, RankNTypes, TypeApplications, TypeFamilyDependencies, BlockArguments, ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wwarn #-}

module Control.Monad.Logic.Moded.Prelude where

import Control.Applicative (Applicative(..), Alternative(..))
import Control.Monad (guard)
import Control.Monad.IO.Class (MonadIO(..))
import qualified Control.Monad.Logic as Logic
import Control.Monad.Logic.Moded.AST (Mode(..))
import Control.Monad.Logic.Moded.Relation (Relation, ConstructProcedure(..), PredType)
import Data.Tuple.OneTuple (OneTuple(..), only)
import Data.Vinyl (rget, Rec(..))
import qualified Prelude
import Prelude (Eq(..), Fractional(..), Num(..), Ord(..), (.), ($), (<$>))

choose :: (Prelude.Foldable t, Alternative f) => t a -> f a
choose = Prelude.foldr ((<|>) . pure) empty

succ :: (Alternative m, Eq a, Prelude.Enum a)
     => Relation m '[a, a] '[ '[In, In], '[In, Out], '[Out, In]]
succ = (procedure @'[In, In] \a b -> guard (Prelude.succ a == b))
    :& (procedure @'[In, Out] \a -> pure (OneTuple $ Prelude.succ a))
    :& (procedure @'[Out, In] \b -> pure (OneTuple $ Prelude.pred b))
    :& RNil

div :: (Alternative m, Prelude.Integral a)
    => Relation m '[a, a, a] '[ '[In, In, In], '[In, In, Out] ]
div = (procedure @'[In, In, In] \a b c -> guard (Prelude.div a b == c))
   :& (procedure @'[In, In, Out] \a b -> pure (OneTuple $ Prelude.div a b))
   :& RNil

mod :: (Alternative m, Prelude.Integral a)
    => Relation m '[a, a, a] '[ '[In, In, In], '[In, In, Out] ]
mod = (procedure @'[In, In, In] \a b c -> guard (Prelude.mod a b == c))
   :& (procedure @'[In, In, Out] \a b -> pure (OneTuple $ Prelude.mod a b))
   :& RNil

divMod :: (Alternative m, Prelude.Integral a)
       => Relation m '[a, a, a, a] '[ '[In, In, In, In], '[In, In, Out, In], '[In, In, Out, Out] ]
divMod = (procedure @'[In, In, In, In] \a b d m -> guard (Prelude.divMod a b == (d, m)))
      :& (procedure @'[In, In, Out, In] \a b m ->
          if Prelude.mod a b == m then pure (OneTuple $ Prelude.div a b) else empty)
      :& (procedure @'[In, In, Out, Out] \a b -> pure (Prelude.divMod a b))
      :& RNil

plus :: (Alternative m, Num a, Eq a)
     => Relation m '[a, a, a] '[ '[In, In, In], '[In, In, Out], '[In, Out, In], '[Out, In, In] ]
plus = (procedure @'[In, In, In] \a b c -> guard (a + b == c))
    :& (procedure @'[In, In, Out] \a b -> pure (OneTuple $ a + b))
    :& (procedure @'[In, Out, In] \a c -> pure (OneTuple $ c - a))
    :& (procedure @'[Out, In, In] \b c -> pure (OneTuple $ c - b))
    :& RNil

times :: (Alternative m, Fractional a, Eq a)
     => Relation m '[a, a, a] '[ '[In, In, In], '[In, In, Out], '[In, Out, In], '[Out, In, In] ]
times = (procedure @'[In, In, In] \a b c -> guard (a * b == c))
    :& (procedure @'[In, In, Out] \a b -> pure (OneTuple $ a * b))
    :& (procedure @'[In, Out, In] \a c -> pure (OneTuple $ c / a))
    :& (procedure @'[Out, In, In] \b c -> pure (OneTuple $ c / b))
    :& RNil

timesInt :: (Alternative m, Prelude.Integral a)
         => Relation m '[a, a, a] '[ '[In, In, In], '[In, In, Out], '[In, Out, In], '[Out, In, In] ]
timesInt = (procedure @'[In, In, In] \a b c -> guard (a * b == c))
        :& (procedure @'[In, In, Out] \a b -> pure (OneTuple $ a * b))
        :& (procedure @'[In, Out, In] \a c -> call (rget @'[In, In, Out, In] divMod) c a 0)
        :& (procedure @'[Out, In, In] \b c -> call (rget @'[In, In, Out, In] divMod) c b 0)
        :& RNil

sum :: (Alternative m, Prelude.Foldable t, Num a, Eq a)
    => Relation m '[t a, a] '[ '[In, In], '[In, Out] ]
sum = (procedure @'[In, In] \xs s -> guard (Prelude.sum xs == s))
   :& (procedure @'[In, Out] \xs -> pure (OneTuple $ Prelude.sum xs))
   :& RNil

maximum :: (Alternative m, Prelude.Foldable t, Ord a)
        => Relation m '[t a, a] '[ '[In, In], '[In, Out] ]
maximum = (procedure @'[In, In] \xs s -> guard (Prelude.maximum xs == s))
       :& (procedure @'[In, Out] \xs -> pure (OneTuple $ Prelude.maximum xs))
       :& RNil

print :: (MonadIO m, Prelude.Show a) => Relation m '[a] '[ '[In] ]
print = (procedure @'[In] $ liftIO . Prelude.print) :& RNil

show :: (Alternative m, Prelude.Read a, Prelude.Show a)
     => Relation m '[a, Prelude.String] '[ '[In, In], '[In, Out], '[Out, In] ]
show = (procedure @'[In, In] \a s -> guard (Prelude.show a == s))
    :& (procedure @'[In, Out] \a -> pure (OneTuple $ Prelude.show a))
    :& (procedure @'[Out, In] \s -> pure (OneTuple $ Prelude.read s))
    :& RNil

observeAll :: Applicative m
           => Relation m '[PredType Logic.Logic () '[a], [a]] '[ '[PredMode '[Out], Out] ]
observeAll = (procedure @'[PredMode '[Out], Out] \p ->
              pure (OneTuple $ Logic.observeAll (only <$> call p)))
          :& RNil
