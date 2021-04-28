{-# LANGUAGE TypeOperators, DataKinds, GADTs, FlexibleInstances,
  PolyKinds, UndecidableInstances, ScopedTypeVariables,
  FunctionalDependencies #-}

module Control.Monad.Logic.Moded.Procedure
  ( Procedure
  , ConstructProcedure(..)
  , CallProcedure(..)
  , PredType
  ) where

import Control.Monad.Logic.Moded.AST (Mode(..))
import Data.Tuple.OneTuple (OneTuple(..), only)

data PredType m z as

data a :* b =
  a :* b

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
  PP
    :: (Procedure m' z' as' ms' -> Procedure m z as ms)
    -> Procedure m z (PredType m' z' as' : as) ('PredMode ms' : ms)
  PO :: Procedure m (z :* a) as ms -> Procedure m z (a : as) ('Out : ms)
  PN :: m z -> Procedure m z '[] '[]

class ConstructProcedure ms m z as f | ms m z as -> f where
  procedure :: f -> Procedure m z as ms
  runProcedure :: Procedure m z as ms -> f

-- https://lexi-lambda.github.io/blog/2021/03/25/an-introduction-to-typeclass-metaprogramming/#guiding-type-inference
instance (ConstructProcedure ms m z as f, bs ~ (a : as), g ~ (a -> f)) =>
         ConstructProcedure ('In : ms) m z bs g where
  procedure f = PI $ \a -> procedure (f a :: f)
  runProcedure (PI f) = runProcedure . f

instance ( ConstructProcedure ms m z as f
         , bs ~ (PredType m' z' as' : as)
         , g ~ (Procedure m' z' as' ms' -> f)
         ) =>
         ConstructProcedure ('PredMode ms' : ms) m z bs g where
  procedure f = PP $ \a -> procedure (f a :: f)
  runProcedure (PP f) = runProcedure . f

instance (ConstructProcedure ms m (z :* a) as f, bs ~ (a : as)) =>
         ConstructProcedure ('Out : ms) m z bs f where
  procedure f = PO $ procedure f
  runProcedure (PO f) = runProcedure f

instance (Functor m, Snoc z t, bs ~ '[], f ~ m t) =>
         ConstructProcedure '[] m z bs f where
  procedure f = PN (snoc <$> f)
  runProcedure (PN f) = unsnoc <$> f

class CallProcedure ms m z as f | ms m z as -> f where
  call :: Procedure m z as ms -> f

instance (CallProcedure ms m z as f, bs ~ (a : as), g ~ (a -> f)) =>
         CallProcedure ('In : ms) m z bs g where
  call (PI f) = call . f

instance ( CallProcedure ms m z as f
         , bs ~ (PredType m' z' as' : as)
         , g ~ (Procedure m' z' as' ms' -> f)
         ) =>
         CallProcedure ('PredMode ms' : ms) m z bs g where
  call (PP f) = call . f

instance (CallProcedure ms m (z :* a) as f, bs ~ (a : as)) =>
         CallProcedure ('Out : ms) m z bs f where
  call (PO f) = call f

instance (Functor m, Snoc (zs :* z :* z') t, bs ~ '[]) =>
         CallProcedure '[] m (zs :* z :* z') bs (m t) where
  call (PN f) = unsnoc <$> f

instance (Functor m, bs ~ '[]) => CallProcedure '[] m (() :* z) bs (m z) where
  call (PN f) = only . unsnoc <$> f

instance (Functor m, bs ~ '[]) => CallProcedure '[] m () bs (m ()) where
  call (PN f) = f
