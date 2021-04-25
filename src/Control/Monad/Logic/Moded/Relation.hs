{-# LANGUAGE TypeOperators, DataKinds, KindSignatures, TypeFamilies, GADTs, MultiParamTypeClasses, FlexibleInstances, FunctionalDependencies, UndecidableInstances #-}

module Control.Monad.Logic.Moded.Relation where

data a :* b = a :* b deriving (Show)
infixl 5 :*

data CurriedRelation m z (as :: [*]) where
  RIO  :: { callI :: a -> CurriedRelation m z as
          , callO :: CurriedRelation m (z :* a) as } -> CurriedRelation m z (a : as)
  RI   :: { callI :: a -> CurriedRelation m z as }   -> CurriedRelation m z (a : as)
  RNil :: { callNil :: m z }                         -> CurriedRelation m z '[]

type Relation m as = CurriedRelation m () as

data HList (as :: [*]) where
  Nil :: HList '[]
  (:>) :: a -> HList as -> HList (a ': as)

infixr 5 :>

data In = In
data Out = Out

class CallRelation ms r f | ms r -> f, ms f -> r where
  call :: HList ms -> r -> f

instance CallRelation '[] (CurriedRelation m z '[]) (m z) where
  call Nil r = callNil r

instance CallRelation ms (CurriedRelation m z as) f => CallRelation (In : ms) (CurriedRelation m z (a : as)) (a -> f) where
  call (In :> ms) r a = call ms (callI r a)

instance CallRelation ms (CurriedRelation m (z :* a) as) f => CallRelation (Out : ms) (CurriedRelation m z (a : as)) f where
  call (Out :> ms) r = call ms (callO r)
