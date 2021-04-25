{-# LANGUAGE NoMonomorphismRestriction, TypeOperators, DataKinds, FlexibleContexts, TypeFamilies, RankNTypes, TypeApplications, TypeFamilyDependencies, BlockArguments, ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wwarn #-}

module Control.Monad.Logic.Moded.Prelude where

import Control.Applicative (Applicative(..), Alternative(..))
import Control.Monad (guard)
import Control.Monad.IO.Class (MonadIO(..))
import qualified Control.Monad.Logic as Logic
import Control.Monad.Logic.Moded.Relation
import Data.Vinyl hiding (HList)
import qualified Prelude
import Prelude (Eq(..), Fractional(..), Num(..), Ord(..), (.), ($))

choose :: (Prelude.Foldable t, Alternative f) => t a -> f a
choose = Prelude.foldr ((<|>) . pure) empty

succ :: (Alternative m, Prelude.Enum a, Eq a)
     => Relation m '[a, a] '[ '[In, In], '[In, Out], '[Out, In] ]
succ = (procedure @[In, In] \a b -> guard (Prelude.succ a == b))
    :& (procedure @[In, Out] \a -> pure (() :* Prelude.succ a))
    :& (procedure @[Out, In] \b -> pure (() :* Prelude.pred b))
    :& RNil

div :: (Alternative m, Prelude.Integral a)
    => Relation m '[a, a, a] '[ '[In, In, In], '[In, In, Out] ]
div = (procedure @[In, In, In] \a b c -> guard (Prelude.div a b == c))
   :& (procedure @[In, In, Out] \a b -> pure (() :* Prelude.div a b))
   :& RNil

mod :: (Alternative m, Prelude.Integral a)
    => Relation m '[a, a, a] '[ '[In, In, In], '[In, In, Out] ]
mod = (procedure @[In, In, In] \a b c -> guard (Prelude.mod a b == c))
   :& (procedure @[In, In, Out] \a b -> pure (() :* Prelude.mod a b))
   :& RNil

divMod :: (Alternative m, Prelude.Integral a)
       => Relation m '[a, a, a, a] '[ '[In, In, In, In], '[In, In, Out, In], '[In, In, Out, Out] ]
divMod = (procedure @[In, In, In, In] \a b d m -> guard (Prelude.divMod a b == (d, m)))
      :& (procedure @[In, In, Out, In] \a b m ->
          if Prelude.mod a b == m then pure (() :* Prelude.div a b) else empty)
      :& (procedure @[In, In, Out, Out] \a b ->
          let (d, m) = Prelude.divMod a b in pure (() :* d :* m))
      :& RNil

plus = RIO
  (\a -> RIO
    (\b -> RIO
      (\c -> RN $ guard (a + b == c))
      (RN $ pure (a + b)))
    (RI $ \c -> RN $ pure (c - a)))
  (RI $ \b -> RI $ \c -> RN $ pure (c - b))

times = RIO
  (\a -> RIO
    (\b -> RIO
      (\c -> RN $ guard (a * b == c))
      (RN $ pure (a * b)))
    (RI $ \c -> RN $ pure (c / a)))
  (RI $ \b -> RI $ \c -> RN $ pure (c / b))

--rget' :: (r ∈ rs) => Rec (Procedure m z as) rs -> Procedure m z as r
--rget' = rget

timesInt :: (Alternative m, Prelude.Integral a)
         => Relation m '[a, a, a] '[ '[In, In, In], '[In, In, Out], '[In, Out, In], '[Out, In, In] ]
timesInt = (procedure @[In, In, In] \a b c -> guard (a * b == c))
        :& (procedure @[In, In, Out] \a b -> pure (() :* a * b))
        :& (procedure @[In, Out, In] \a c -> call' (rget @[In, In, Out, In] divMod) c a 0)
        :& (procedure @[Out, In, In] \b c -> call' (rget @[In, In, Out, In] divMod) c b 0)
        :& RNil

sum = RI $ \xs -> RIO
  (\s -> RN $ guard (Prelude.sum xs == s))
  (RN $ pure (Prelude.sum xs))

maximum = RI $ \xs -> RIO
  (\s -> RN $ guard (Prelude.maximum xs == s))
  (RN $ pure (Prelude.maximum xs))

print = RI $ \a -> RN $ liftIO $ Prelude.print a

show = RIO
    (\a -> RIO
      (\s -> RN $ guard (Prelude.show a == s))
      (RN $ pure (Prelude.show a)))
    (RI $ \s -> RN $ pure (Prelude.read s))

observeAll :: (Applicative m, '[Out] ∈ rs) =>
  Relation m '[Relation Logic.Logic '[a] rs, [a]] '[ '[In, Out] ]
observeAll = (procedure @[In, Out] \p ->
              let q = do
                    () :* x <- pcall (Out :> Nil) p
                    pure x
               in pure (() :* Logic.observeAll q))
          :& RNil
