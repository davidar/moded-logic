{-# LANGUAGE TypeOperators, DataKinds, KindSignatures, TypeFamilies, GADTs, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, PolyKinds, UndecidableInstances, RankNTypes, ScopedTypeVariables, FunctionalDependencies #-}

module Control.Monad.Logic.Moded.Relation
  ( Relation
  , ConstructProcedure(..)
  , PredType
  ) where

import Control.Monad.Logic.Moded.AST (Mode(..))
import Data.Tuple.OneTuple (OneTuple(..))
import Data.Vinyl (Rec)

data PredType m z as

data a :* b = a :* b
infixl 5 :*

class Snoc z t | z -> t, t -> z where
  snoc :: t -> z
  unsnoc :: z -> t

instance Snoc (() :* a :* b :* c :* d :* e) (a, b, c, d, e) where
  snoc (a, b, c, d, e) = () :* a :* b :* c :* d :* e
  unsnoc (() :* a :* b :* c :* d :* e) = (a, b, c, d, e)

instance Snoc (() :* a :* b :* c :* d) (a, b, c, d) where
  snoc (a, b, c, d) = () :* a :* b :* c :* d
  unsnoc (() :* a :* b :* c :* d) = (a, b, c, d)

instance Snoc (() :* a :* b :* c) (a, b, c) where
  snoc (a, b, c) = () :* a :* b :* c
  unsnoc (() :* a :* b :* c) = (a, b, c)

instance Snoc (() :* a :* b) (a, b) where
  snoc (a, b) = () :* a :* b
  unsnoc (() :* a :* b) = (a, b)

instance Snoc (() :* a) (OneTuple a) where
  snoc (OneTuple a) = () :* a
  unsnoc (() :* a) = OneTuple a

instance Snoc () () where
  snoc () = ()
  unsnoc () = ()

data Procedure m z (as :: [*]) (ms :: [Mode]) where
  PI :: (a -> Procedure m z as ms) -> Procedure m z (a : as) ('In : ms)
  PP :: (Procedure m' z' as' ms' -> Procedure m z as ms) -> Procedure m z (PredType m' z' as' : as) ('PredMode ms' : ms)
  PO :: Procedure m (z :* a) as ms -> Procedure m z (a : as) ('Out : ms)
  PN :: m z -> Procedure m z '[] '[]

type Relation m as rs = Rec (Procedure m () as) rs

class ConstructProcedure ms m z as f where
  procedure :: f -> Procedure m z as ms
  call :: Procedure m z as ms -> f

-- https://lexi-lambda.github.io/blog/2021/03/25/an-introduction-to-typeclass-metaprogramming/#guiding-type-inference
instance (ConstructProcedure ms m z as f, bs ~ (a : as), g ~ (a -> f)) => ConstructProcedure ('In : ms) m z bs g where
  procedure f = PI $ \a -> procedure (f a :: f)
  call (PI f) = call . f

instance (ConstructProcedure ms m z as f, bs ~ (PredType m' z' as' : as), g ~ (Procedure m' z' as' ms' -> f)) => ConstructProcedure ('PredMode ms' : ms) m z bs g where
  procedure f = PP $ \a -> procedure (f a :: f)
  call (PP f) = call . f

instance (ConstructProcedure ms m (z :* a) as f, bs ~ (a : as)) => ConstructProcedure ('Out : ms) m z bs f where
  procedure f = PO $ procedure f
  call (PO f) = call f

instance (Functor m, Snoc z t, bs ~ '[], g ~ m t) => ConstructProcedure '[] m z bs g where
  procedure f = PN (snoc <$> f)
  call (PN f) = unsnoc <$> f
