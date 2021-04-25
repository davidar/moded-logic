{-# LANGUAGE TypeOperators, DataKinds, KindSignatures, TypeFamilies, GADTs, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, PolyKinds, UndecidableInstances, RankNTypes, ScopedTypeVariables #-}

module Control.Monad.Logic.Moded.Relation where

import Data.Vinyl hiding (HList)
import GHC.TypeLits (TypeError, ErrorMessage(..))

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

newtype Procedure m z as ms = Procedure { call' :: ProcedureType m z as ms }

procedure :: forall ms m z as. ProcedureType m z as ms -> Procedure m z as ms
procedure = Procedure

pcall :: forall r rs m z as. (r ∈ rs)
      => HList r -> Rec (Procedure m z as) rs -> ProcedureType m z as r
pcall _ r = let Procedure f = (rget r :: Procedure m z as r) in f

type Relation m as rs = Rec (Procedure m () as) rs

data RIO a i o m = RIO (a -> i m) (o m)
newtype RI a i m = RI (a -> i m)
newtype RN z m = RN (m z)

type family CallResult ms r where
  CallResult '[] (RN z m) = m z
  CallResult (In : ms) (RI a i m) = a -> CallResult ms (i m)
  CallResult (Out : ms) (RI a i m) = a -> TypeError ('Text "Unsupported mode, trying to output an input-only argument")
  CallResult (In : ms) (RIO a i o m) = a -> CallResult ms (i m)
  CallResult (Out : ms) (RIO a i o m) = CallResult ms (o m)

class CallRelation ms r where
  call :: HList ms -> r -> CallResult ms r

instance CallRelation '[] (RN z m) where
  call Nil (RN m) = m

instance CallRelation ms (i m) => CallRelation (In : ms) (RI a i m) where
  call (In :> ms) (RI i) a = call ms (i a)

instance TypeError ('Text "Unsupported mode, trying to output an input-only argument") => CallRelation (Out : ms) (RI a i m) where
  call = error "unreachable"

instance CallRelation ms (i m) => CallRelation (In : ms) (RIO a i o m) where
  call (In :> ms) (RIO i _) a = call ms (i a)

instance CallRelation ms (o m) => CallRelation (Out : ms) (RIO a i o m) where
  call (Out :> ms) (RIO _ o) = call ms o
