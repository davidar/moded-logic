{-# LANGUAGE TypeOperators, DataKinds, KindSignatures, TypeFamilies, GADTs, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts #-}

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

type family CallResult ms r where
  CallResult '[] (CurriedRelation m z '[]) = m z
  CallResult (In : ms) (CurriedRelation m z (a : as)) = a -> CallResult ms (CurriedRelation m z as)
  CallResult (Out : ms) (CurriedRelation m z (a : as)) = CallResult ms (CurriedRelation m (z :* a) as)

class CallRelation ms r where
  call :: HList ms -> r -> CallResult ms r

instance CallRelation '[] (CurriedRelation m z '[]) where
  call Nil r = callNil r

instance CallRelation ms (CurriedRelation m z as) => CallRelation (In : ms) (CurriedRelation m z (a : as)) where
  call (In :> ms) r a = call ms (callI r a)

instance CallRelation ms (CurriedRelation m (z :* a) as) => CallRelation (Out : ms) (CurriedRelation m z (a : as)) where
  call (Out :> ms) r = call ms (callO r)
