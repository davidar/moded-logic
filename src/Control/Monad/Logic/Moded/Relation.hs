{-# LANGUAGE TypeOperators, DataKinds, KindSignatures, TypeFamilies, GADTs, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, PolyKinds, UndecidableInstances, RankNTypes, ScopedTypeVariables #-}

module Control.Monad.Logic.Moded.Relation
  ( Relation
  , Procedure(..)
  , In
  , Out
  ) where

import Data.Vinyl (Rec)

data In
data Out
data a :* b

type family Flatten z where
  Flatten (() :* a :* b :* c :* d :* e) = (a, b, c, d, e)
  Flatten (() :* a :* b :* c :* d) = (a, b, c, d)
  Flatten (() :* a :* b :* c) = (a, b, c)
  Flatten (() :* a :* b) = (a, b)
  Flatten (() :* a) = a
  Flatten () = ()

type family ProcedureType m z as (ms :: [*]) where
  ProcedureType m z '[] '[] = m (Flatten z)
  ProcedureType m z (a : as) (In : ms) = a -> ProcedureType m z as ms
  ProcedureType m z (a : as) (Out : ms) = ProcedureType m (z :* a) as ms

newtype Procedure m z as ms where
  Procedure :: forall ms m z as. { call :: ProcedureType m z as ms } -> Procedure m z as ms

type Relation m as rs = Rec (Procedure m () as) rs
