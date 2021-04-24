{-# LANGUAGE TypeOperators, DataKinds, KindSignatures, TypeFamilies, GADTs #-}

module Control.Monad.Logic.Moded.Relation where

data a :* b = a :* b
infixl 5 :*

data Relation m z (as :: [*]) where
  RIO  :: { callI :: a -> Relation m z as
          , callO :: Relation m (z :* a) as } -> Relation m z (a ': as)
  RI   :: { callI :: a -> Relation m z as }   -> Relation m z (a ': as)
  RNil :: { call :: m z }                     -> Relation m z '[]

{-
data Relation1 m z a =
  R1
    { callI :: a -> m z
    , callO :: m (z :* a)
    }

data Relation2 m z a b =
  R2
    { callI_ :: a -> Relation1 m z b
    , callO_ :: Relation1 m (z :* a) b
    }

data Relation3 m z a b c =
  R3
    { callIII :: a -> b -> c -> m z
    , callIIO :: a -> b -> m (z :* c)
    , callIOI :: a -> c -> m (z :* b)
    , callIOO :: a -> m (z :* b :* c)
    , callOII :: b -> c -> m (z :* a)
    , callOIO :: b -> m (z :* a :* c)
    , callOOI :: c -> m (z :* a :* b)
    , callOOO :: m (z :* a :* b :* c)
    }

data Relation4 m z a b c d =
  R4
    { callIIII :: a -> b -> c -> d -> m z
    , callIIIO :: a -> b -> c -> m (z :* d)
    , callIIOI :: a -> b -> d -> m (z :* c)
    , callIIOO :: a -> b -> m (z :* c :* d)
    , callIOII :: a -> c -> d -> m (z :* b)
    , callIOIO :: a -> c -> m (z :* b :* d)
    , callIOOI :: a -> d -> m (z :* b :* c)
    , callIOOO :: a -> m (z :* b :* c :* d)
    , callOIII :: b -> c -> d -> m (z :* a)
    , callOIIO :: b -> c -> m (z :* a :* d)
    , callOIOI :: b -> d -> m (z :* a :* c)
    , callOIOO :: b -> m (z :* a :* c :* d)
    , callOOII :: c -> d -> m (z :* a :* b)
    , callOOIO :: c -> m (z :* a :* b :* d)
    , callOOOI :: d -> m (z :* a :* b :* c)
    , callOOOO :: m (z :* a :* b :* c :* d)
    }
-}
