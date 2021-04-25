{-# LANGUAGE TypeOperators, DataKinds, KindSignatures, TypeFamilies, GADTs, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, PolyKinds, UndecidableInstances, RankNTypes, ScopedTypeVariables #-}

module Control.Monad.Logic.Moded.Relation where

import Data.Vinyl hiding (HList)

data HList (as :: [*]) where
  Nil :: HList '[]
  (:>) :: a -> HList as -> HList (a ': as)
infixr 5 :>

data a :* b = a :* b deriving (Show)
infixl 5 :*

data In = In
data Out = Out

type family ProcedureType m z as (ms :: [*]) where
  ProcedureType m z '[] '[] = m z
  ProcedureType m z (a : as) (In : ms) = a -> ProcedureType m z as ms
  ProcedureType m z (a : as) (Out : ms) = ProcedureType m (z :* a) as ms

newtype Procedure m z as ms where
  Procedure :: forall ms m z as. { call' :: ProcedureType m z as ms } -> Procedure m z as ms

pcall :: forall r rs m z as. (r ∈ rs)
      => HList r -> Rec (Procedure m z as) rs -> ProcedureType m z as r
pcall _ r = f
  where Procedure f = rget r :: Procedure m z as r

type Relation m as rs = Rec (Procedure m () as) rs
