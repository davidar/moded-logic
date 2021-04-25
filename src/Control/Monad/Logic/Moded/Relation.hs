{-# LANGUAGE TypeOperators, DataKinds, KindSignatures, TypeFamilies, GADTs, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, PolyKinds, UndecidableInstances #-}

module Control.Monad.Logic.Moded.Relation where

import GHC.TypeLits (TypeError, ErrorMessage(..))

data HList (as :: [*]) where
  Nil :: HList '[]
  (:>) :: a -> HList as -> HList (a ': as)

infixr 5 :>

data In = In
data Out = Out

data RIO a i o m = RIO (a -> i m) (o m)
newtype RI a i m = RI (a -> i m)
newtype RNil z m = RNil (m z)

type family CallResult ms r where
  CallResult '[] (RNil z m) = m z
  CallResult (In : ms) (RI a i m) = a -> CallResult ms (i m)
  CallResult (Out : ms) (RI a i m) = a -> TypeError ('Text "Unsupported mode, trying to output an input-only argument")
  CallResult (In : ms) (RIO a i o m) = a -> CallResult ms (i m)
  CallResult (Out : ms) (RIO a i o m) = CallResult ms (o m)

class CallRelation ms r where
  call :: HList ms -> r -> CallResult ms r

instance CallRelation '[] (RNil z m) where
  call Nil (RNil m) = m

instance CallRelation ms (i m) => CallRelation (In : ms) (RI a i m) where
  call (In :> ms) (RI i) a = call ms (i a)

instance TypeError ('Text "Unsupported mode, trying to output an input-only argument") => CallRelation (Out : ms) (RI a i m) where
  call = error "unreachable"

instance CallRelation ms (i m) => CallRelation (In : ms) (RIO a i o m) where
  call (In :> ms) (RIO i _) a = call ms (i a)

instance CallRelation ms (o m) => CallRelation (Out : ms) (RIO a i o m) where
  call (Out :> ms) (RIO _ o) = call ms o
