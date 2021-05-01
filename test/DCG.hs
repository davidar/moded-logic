{-# LANGUAGE DataKinds, FlexibleContexts, NoImplicitPrelude, NoMonomorphismRestriction, TypeApplications #-}
module DCG where

import qualified Control.Monad.Logic as Logic
import Control.Monad.Logic.Moded.Prelude

data Tree = S Tree Tree | NP String String | VP String Tree deriving (Eq, Ord, Show)
{- det/3
det arg1 arg2 x :- ((arg1 = "the", arg2 = data0:x0, x0 = x, data0 = "the"); (arg1 = "a", arg2 = data1:x1, x1 = x, data1 = "a")).
constraints:
~(arg2[0,1] & data0[0,1])
~(arg2[1,1] & data1[1,1])
~(data0[0,1] & data0[0,3])
~(data1[1,1] & data1[1,3])
~(x0[0,1] & x0[0,2])
~(x0[0,2] & x[0,2])
~(x1[1,1] & x1[1,2])
~(x1[1,2] & x[1,2])
(data0[0,1] | data0[0,3])
(data1[1,1] | data1[1,3])
(x0[0,1] | x0[0,2])
(x1[1,1] | x1[1,2])
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg1[0] <-> arg1[0,0])
(arg1[1] <-> arg1[1,0])
(arg2[] <-> arg2[0])
(arg2[] <-> arg2[1])
(arg2[0] <-> arg2[0,1])
(arg2[1] <-> arg2[1,1])
(data0[0,1] <-> x0[0,1])
(data1[1,1] <-> x1[1,1])
(x[] <-> x[0])
(x[] <-> x[1])
(x[0] <-> x[0,2])
(x[1] <-> x[1,2])
1
-}

det = rget $ (procedure @'[ 'In, 'In, 'In ] detIII) :& (procedure @'[ 'In, 'In, 'Out ] detIIO) :& (procedure @'[ 'In, 'Out, 'In ] detIOI) :& (procedure @'[ 'Out, 'In, 'In ] detOII) :& (procedure @'[ 'Out, 'In, 'Out ] detOIO) :& (procedure @'[ 'Out, 'Out, 'In ] detOOI) :& RNil
  where
    detIII = \arg1 arg2 x -> Logic.once $ do
      -- solution: data0[0,1] data1[1,1] x0[0,1] x1[1,1] ~arg1[] ~arg1[0] ~arg1[0,0] ~arg1[1] ~arg1[1,0] ~arg2[] ~arg2[0] ~arg2[0,1] ~arg2[1] ~arg2[1,1] ~data0[0,3] ~data1[1,3] ~x[] ~x[0] ~x[0,2] ~x[1] ~x[1,2] ~x0[0,2] ~x1[1,2]
      -- cost: 0
      () <- (do
        guard $ arg1 == "the"
        (data0:x0) <- pure arg2
        guard $ x0 == x
        guard $ data0 == "the"
        pure ()
       ) <|> (do
        guard $ arg1 == "a"
        (data1:x1) <- pure arg2
        guard $ x1 == x
        guard $ data1 == "a"
        pure ()
       )
      pure ()
    
    detIIO = \arg1 arg2 -> do
      -- solution: data0[0,1] data1[1,1] x[] x[0] x[0,2] x[1] x[1,2] x0[0,1] x1[1,1] ~arg1[] ~arg1[0] ~arg1[0,0] ~arg1[1] ~arg1[1,0] ~arg2[] ~arg2[0] ~arg2[0,1] ~arg2[1] ~arg2[1,1] ~data0[0,3] ~data1[1,3] ~x0[0,2] ~x1[1,2]
      -- cost: 0
      (x) <- (do
        guard $ arg1 == "the"
        (data0:x0) <- pure arg2
        x <- pure x0
        guard $ data0 == "the"
        pure (x)
       ) <|> (do
        guard $ arg1 == "a"
        (data1:x1) <- pure arg2
        x <- pure x1
        guard $ data1 == "a"
        pure (x)
       )
      pure (OneTuple (x))
    
    detIOI = \arg1 x -> do
      -- solution: arg2[] arg2[0] arg2[0,1] arg2[1] arg2[1,1] data0[0,3] data1[1,3] x0[0,2] x1[1,2] ~arg1[] ~arg1[0] ~arg1[0,0] ~arg1[1] ~arg1[1,0] ~data0[0,1] ~data1[1,1] ~x[] ~x[0] ~x[0,2] ~x[1] ~x[1,2] ~x0[0,1] ~x1[1,1]
      -- cost: 0
      (arg2) <- (do
        x0 <- pure x
        guard $ arg1 == "the"
        data0 <- pure "the"
        arg2 <- pure (data0:x0)
        pure (arg2)
       ) <|> (do
        x1 <- pure x
        guard $ arg1 == "a"
        data1 <- pure "a"
        arg2 <- pure (data1:x1)
        pure (arg2)
       )
      pure (OneTuple (arg2))
    
    detOII = \arg2 x -> do
      -- solution: arg1[] arg1[0] arg1[0,0] arg1[1] arg1[1,0] data0[0,1] data1[1,1] x0[0,1] x1[1,1] ~arg2[] ~arg2[0] ~arg2[0,1] ~arg2[1] ~arg2[1,1] ~data0[0,3] ~data1[1,3] ~x[] ~x[0] ~x[0,2] ~x[1] ~x[1,2] ~x0[0,2] ~x1[1,2]
      -- cost: 0
      (arg1) <- (do
        arg1 <- pure "the"
        (data0:x0) <- pure arg2
        guard $ x0 == x
        guard $ data0 == "the"
        pure (arg1)
       ) <|> (do
        arg1 <- pure "a"
        (data1:x1) <- pure arg2
        guard $ x1 == x
        guard $ data1 == "a"
        pure (arg1)
       )
      pure (OneTuple (arg1))
    
    detOIO = \arg2 -> do
      -- solution: arg1[] arg1[0] arg1[0,0] arg1[1] arg1[1,0] data0[0,1] data1[1,1] x[] x[0] x[0,2] x[1] x[1,2] x0[0,1] x1[1,1] ~arg2[] ~arg2[0] ~arg2[0,1] ~arg2[1] ~arg2[1,1] ~data0[0,3] ~data1[1,3] ~x0[0,2] ~x1[1,2]
      -- cost: 0
      (arg1,x) <- (do
        arg1 <- pure "the"
        (data0:x0) <- pure arg2
        x <- pure x0
        guard $ data0 == "the"
        pure (arg1,x)
       ) <|> (do
        arg1 <- pure "a"
        (data1:x1) <- pure arg2
        x <- pure x1
        guard $ data1 == "a"
        pure (arg1,x)
       )
      pure (arg1,x)
    
    detOOI = \x -> do
      -- solution: arg1[] arg1[0] arg1[0,0] arg1[1] arg1[1,0] arg2[] arg2[0] arg2[0,1] arg2[1] arg2[1,1] data0[0,3] data1[1,3] x0[0,2] x1[1,2] ~data0[0,1] ~data1[1,1] ~x[] ~x[0] ~x[0,2] ~x[1] ~x[1,2] ~x0[0,1] ~x1[1,1]
      -- cost: 0
      (arg1,arg2) <- (do
        x0 <- pure x
        arg1 <- pure "the"
        data0 <- pure "the"
        arg2 <- pure (data0:x0)
        pure (arg1,arg2)
       ) <|> (do
        x1 <- pure x
        arg1 <- pure "a"
        data1 <- pure "a"
        arg2 <- pure (data1:x1)
        pure (arg1,arg2)
       )
      pure (arg1,arg2)
    
{- noun/3
noun arg1 arg2 x :- ((arg1 = "cat", arg2 = data0:x0, x0 = x, data0 = "cat"); (arg1 = "bat", arg2 = data1:x1, x1 = x, data1 = "bat")).
constraints:
~(arg2[0,1] & data0[0,1])
~(arg2[1,1] & data1[1,1])
~(data0[0,1] & data0[0,3])
~(data1[1,1] & data1[1,3])
~(x0[0,1] & x0[0,2])
~(x0[0,2] & x[0,2])
~(x1[1,1] & x1[1,2])
~(x1[1,2] & x[1,2])
(data0[0,1] | data0[0,3])
(data1[1,1] | data1[1,3])
(x0[0,1] | x0[0,2])
(x1[1,1] | x1[1,2])
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg1[0] <-> arg1[0,0])
(arg1[1] <-> arg1[1,0])
(arg2[] <-> arg2[0])
(arg2[] <-> arg2[1])
(arg2[0] <-> arg2[0,1])
(arg2[1] <-> arg2[1,1])
(data0[0,1] <-> x0[0,1])
(data1[1,1] <-> x1[1,1])
(x[] <-> x[0])
(x[] <-> x[1])
(x[0] <-> x[0,2])
(x[1] <-> x[1,2])
1
-}

noun = rget $ (procedure @'[ 'In, 'In, 'In ] nounIII) :& (procedure @'[ 'In, 'In, 'Out ] nounIIO) :& (procedure @'[ 'In, 'Out, 'In ] nounIOI) :& (procedure @'[ 'Out, 'In, 'In ] nounOII) :& (procedure @'[ 'Out, 'In, 'Out ] nounOIO) :& (procedure @'[ 'Out, 'Out, 'In ] nounOOI) :& RNil
  where
    nounIII = \arg1 arg2 x -> Logic.once $ do
      -- solution: data0[0,1] data1[1,1] x0[0,1] x1[1,1] ~arg1[] ~arg1[0] ~arg1[0,0] ~arg1[1] ~arg1[1,0] ~arg2[] ~arg2[0] ~arg2[0,1] ~arg2[1] ~arg2[1,1] ~data0[0,3] ~data1[1,3] ~x[] ~x[0] ~x[0,2] ~x[1] ~x[1,2] ~x0[0,2] ~x1[1,2]
      -- cost: 0
      () <- (do
        guard $ arg1 == "cat"
        (data0:x0) <- pure arg2
        guard $ x0 == x
        guard $ data0 == "cat"
        pure ()
       ) <|> (do
        guard $ arg1 == "bat"
        (data1:x1) <- pure arg2
        guard $ x1 == x
        guard $ data1 == "bat"
        pure ()
       )
      pure ()
    
    nounIIO = \arg1 arg2 -> do
      -- solution: data0[0,1] data1[1,1] x[] x[0] x[0,2] x[1] x[1,2] x0[0,1] x1[1,1] ~arg1[] ~arg1[0] ~arg1[0,0] ~arg1[1] ~arg1[1,0] ~arg2[] ~arg2[0] ~arg2[0,1] ~arg2[1] ~arg2[1,1] ~data0[0,3] ~data1[1,3] ~x0[0,2] ~x1[1,2]
      -- cost: 0
      (x) <- (do
        guard $ arg1 == "cat"
        (data0:x0) <- pure arg2
        x <- pure x0
        guard $ data0 == "cat"
        pure (x)
       ) <|> (do
        guard $ arg1 == "bat"
        (data1:x1) <- pure arg2
        x <- pure x1
        guard $ data1 == "bat"
        pure (x)
       )
      pure (OneTuple (x))
    
    nounIOI = \arg1 x -> do
      -- solution: arg2[] arg2[0] arg2[0,1] arg2[1] arg2[1,1] data0[0,3] data1[1,3] x0[0,2] x1[1,2] ~arg1[] ~arg1[0] ~arg1[0,0] ~arg1[1] ~arg1[1,0] ~data0[0,1] ~data1[1,1] ~x[] ~x[0] ~x[0,2] ~x[1] ~x[1,2] ~x0[0,1] ~x1[1,1]
      -- cost: 0
      (arg2) <- (do
        x0 <- pure x
        guard $ arg1 == "cat"
        data0 <- pure "cat"
        arg2 <- pure (data0:x0)
        pure (arg2)
       ) <|> (do
        x1 <- pure x
        guard $ arg1 == "bat"
        data1 <- pure "bat"
        arg2 <- pure (data1:x1)
        pure (arg2)
       )
      pure (OneTuple (arg2))
    
    nounOII = \arg2 x -> do
      -- solution: arg1[] arg1[0] arg1[0,0] arg1[1] arg1[1,0] data0[0,1] data1[1,1] x0[0,1] x1[1,1] ~arg2[] ~arg2[0] ~arg2[0,1] ~arg2[1] ~arg2[1,1] ~data0[0,3] ~data1[1,3] ~x[] ~x[0] ~x[0,2] ~x[1] ~x[1,2] ~x0[0,2] ~x1[1,2]
      -- cost: 0
      (arg1) <- (do
        arg1 <- pure "cat"
        (data0:x0) <- pure arg2
        guard $ x0 == x
        guard $ data0 == "cat"
        pure (arg1)
       ) <|> (do
        arg1 <- pure "bat"
        (data1:x1) <- pure arg2
        guard $ x1 == x
        guard $ data1 == "bat"
        pure (arg1)
       )
      pure (OneTuple (arg1))
    
    nounOIO = \arg2 -> do
      -- solution: arg1[] arg1[0] arg1[0,0] arg1[1] arg1[1,0] data0[0,1] data1[1,1] x[] x[0] x[0,2] x[1] x[1,2] x0[0,1] x1[1,1] ~arg2[] ~arg2[0] ~arg2[0,1] ~arg2[1] ~arg2[1,1] ~data0[0,3] ~data1[1,3] ~x0[0,2] ~x1[1,2]
      -- cost: 0
      (arg1,x) <- (do
        arg1 <- pure "cat"
        (data0:x0) <- pure arg2
        x <- pure x0
        guard $ data0 == "cat"
        pure (arg1,x)
       ) <|> (do
        arg1 <- pure "bat"
        (data1:x1) <- pure arg2
        x <- pure x1
        guard $ data1 == "bat"
        pure (arg1,x)
       )
      pure (arg1,x)
    
    nounOOI = \x -> do
      -- solution: arg1[] arg1[0] arg1[0,0] arg1[1] arg1[1,0] arg2[] arg2[0] arg2[0,1] arg2[1] arg2[1,1] data0[0,3] data1[1,3] x0[0,2] x1[1,2] ~data0[0,1] ~data1[1,1] ~x[] ~x[0] ~x[0,2] ~x[1] ~x[1,2] ~x0[0,1] ~x1[1,1]
      -- cost: 0
      (arg1,arg2) <- (do
        x0 <- pure x
        arg1 <- pure "cat"
        data0 <- pure "cat"
        arg2 <- pure (data0:x0)
        pure (arg1,arg2)
       ) <|> (do
        x1 <- pure x
        arg1 <- pure "bat"
        data1 <- pure "bat"
        arg2 <- pure (data1:x1)
        pure (arg1,arg2)
       )
      pure (arg1,arg2)
    
{- verb/3
verb arg1 arg2 x :- ((arg1 = "eats", arg2 = data0:x, data0 = "eats")).
constraints:
~(arg2[0,1] & data0[0,1])
~(data0[0,1] & data0[0,2])
(data0[0,1] | data0[0,2])
(arg1[] <-> arg1[0])
(arg1[0] <-> arg1[0,0])
(arg2[] <-> arg2[0])
(arg2[0] <-> arg2[0,1])
(data0[0,1] <-> x[0,1])
(x[] <-> x[0])
(x[0] <-> x[0,1])
1
-}

verb = rget $ (procedure @'[ 'In, 'In, 'In ] verbIII) :& (procedure @'[ 'In, 'In, 'Out ] verbIIO) :& (procedure @'[ 'In, 'Out, 'In ] verbIOI) :& (procedure @'[ 'Out, 'In, 'In ] verbOII) :& (procedure @'[ 'Out, 'In, 'Out ] verbOIO) :& (procedure @'[ 'Out, 'Out, 'In ] verbOOI) :& RNil
  where
    verbIII = \arg1 arg2 x -> Logic.once $ do
      -- solution: data0[0,2] ~arg1[] ~arg1[0] ~arg1[0,0] ~arg2[] ~arg2[0] ~arg2[0,1] ~data0[0,1] ~x[] ~x[0] ~x[0,1]
      -- cost: 0
      () <- (do
        guard $ arg1 == "eats"
        data0 <- pure "eats"
        guard $ arg2 == (data0:x)
        pure ()
       )
      pure ()
    
    verbIIO = \arg1 arg2 -> do
      -- solution: data0[0,1] x[] x[0] x[0,1] ~arg1[] ~arg1[0] ~arg1[0,0] ~arg2[] ~arg2[0] ~arg2[0,1] ~data0[0,2]
      -- cost: 0
      (x) <- (do
        guard $ arg1 == "eats"
        (data0:x) <- pure arg2
        guard $ data0 == "eats"
        pure (x)
       )
      pure (OneTuple (x))
    
    verbIOI = \arg1 x -> do
      -- solution: arg2[] arg2[0] arg2[0,1] data0[0,2] ~arg1[] ~arg1[0] ~arg1[0,0] ~data0[0,1] ~x[] ~x[0] ~x[0,1]
      -- cost: 0
      (arg2) <- (do
        guard $ arg1 == "eats"
        data0 <- pure "eats"
        arg2 <- pure (data0:x)
        pure (arg2)
       )
      pure (OneTuple (arg2))
    
    verbOII = \arg2 x -> do
      -- solution: arg1[] arg1[0] arg1[0,0] data0[0,2] ~arg2[] ~arg2[0] ~arg2[0,1] ~data0[0,1] ~x[] ~x[0] ~x[0,1]
      -- cost: 0
      (arg1) <- (do
        arg1 <- pure "eats"
        data0 <- pure "eats"
        guard $ arg2 == (data0:x)
        pure (arg1)
       )
      pure (OneTuple (arg1))
    
    verbOIO = \arg2 -> do
      -- solution: arg1[] arg1[0] arg1[0,0] data0[0,1] x[] x[0] x[0,1] ~arg2[] ~arg2[0] ~arg2[0,1] ~data0[0,2]
      -- cost: 0
      (arg1,x) <- (do
        arg1 <- pure "eats"
        (data0:x) <- pure arg2
        guard $ data0 == "eats"
        pure (arg1,x)
       )
      pure (arg1,x)
    
    verbOOI = \x -> do
      -- solution: arg1[] arg1[0] arg1[0,0] arg2[] arg2[0] arg2[0,1] data0[0,2] ~data0[0,1] ~x[] ~x[0] ~x[0,1]
      -- cost: 0
      (arg1,arg2) <- (do
        arg1 <- pure "eats"
        data0 <- pure "eats"
        arg2 <- pure (data0:x)
        pure (arg1,arg2)
       )
      pure (arg1,arg2)
    
{- np/3
np arg1 a z :- ((arg1 = NP d n, det d a b, noun n b z)).
constraints:
~(arg1[0,0] & d[0,0])
~(b[0,1] & b[0,2])
~(d[0,0] & d[0,1])
~(n[0,0] & n[0,2])
(b[0,1] | b[0,2])
(d[0,0] | d[0,1])
(n[0,0] | n[0,2])
((d[0,1] & (a[0,1] & ~b[0,1])) | ((d[0,1] & (~a[0,1] & b[0,1])) | ((d[0,1] & (~a[0,1] & ~b[0,1])) | ((~d[0,1] & (a[0,1] & ~b[0,1])) | ((~d[0,1] & (~a[0,1] & b[0,1])) | (~d[0,1] & (~a[0,1] & ~b[0,1])))))))
((n[0,2] & (b[0,2] & ~z[0,2])) | ((n[0,2] & (~b[0,2] & z[0,2])) | ((n[0,2] & (~b[0,2] & ~z[0,2])) | ((~n[0,2] & (b[0,2] & ~z[0,2])) | ((~n[0,2] & (~b[0,2] & z[0,2])) | (~n[0,2] & (~b[0,2] & ~z[0,2])))))))
(a[] <-> a[0])
(a[0] <-> a[0,1])
(arg1[] <-> arg1[0])
(arg1[0] <-> arg1[0,0])
(d[0,0] <-> n[0,0])
(z[] <-> z[0])
(z[0] <-> z[0,2])
1
-}

np = rget $ (procedure @'[ 'In, 'In, 'In ] npIII) :& (procedure @'[ 'In, 'In, 'Out ] npIIO) :& (procedure @'[ 'In, 'Out, 'In ] npIOI) :& (procedure @'[ 'Out, 'In, 'In ] npOII) :& (procedure @'[ 'Out, 'In, 'Out ] npOIO) :& (procedure @'[ 'Out, 'Out, 'In ] npOOI) :& RNil
  where
    npIII = \arg1 a z -> Logic.once $ do
      -- solution: b[0,1] d[0,0] n[0,0] ~a[] ~a[0] ~a[0,1] ~arg1[] ~arg1[0] ~arg1[0,0] ~b[0,2] ~d[0,1] ~n[0,2] ~z[] ~z[0] ~z[0,2]
      -- cost: 3
      () <- (do
        (NP d n) <- pure arg1
        (OneTuple (b)) <- runProcedure @'[ 'In, 'In, 'Out ] det d a
        () <- runProcedure @'[ 'In, 'In, 'In ] noun n b z
        pure ()
       )
      pure ()
    
    npIIO = \arg1 a -> do
      -- solution: b[0,1] d[0,0] n[0,0] z[] z[0] z[0,2] ~a[] ~a[0] ~a[0,1] ~arg1[] ~arg1[0] ~arg1[0,0] ~b[0,2] ~d[0,1] ~n[0,2]
      -- cost: 4
      (z) <- (do
        (NP d n) <- pure arg1
        (OneTuple (b)) <- runProcedure @'[ 'In, 'In, 'Out ] det d a
        (OneTuple (z)) <- runProcedure @'[ 'In, 'In, 'Out ] noun n b
        pure (z)
       )
      pure (OneTuple (z))
    
    npIOI = \arg1 z -> do
      -- solution: a[] a[0] a[0,1] b[0,2] d[0,0] n[0,0] ~arg1[] ~arg1[0] ~arg1[0,0] ~b[0,1] ~d[0,1] ~n[0,2] ~z[] ~z[0] ~z[0,2]
      -- cost: 4
      (a) <- (do
        (NP d n) <- pure arg1
        (OneTuple (b)) <- runProcedure @'[ 'In, 'Out, 'In ] noun n z
        (OneTuple (a)) <- runProcedure @'[ 'In, 'Out, 'In ] det d b
        pure (a)
       )
      pure (OneTuple (a))
    
    npOII = \a z -> do
      -- solution: arg1[] arg1[0] arg1[0,0] b[0,1] d[0,1] n[0,2] ~a[] ~a[0] ~a[0,1] ~b[0,2] ~d[0,0] ~n[0,0] ~z[] ~z[0] ~z[0,2]
      -- cost: 5
      (arg1) <- (do
        (d,b) <- runProcedure @'[ 'Out, 'In, 'Out ] det a
        (OneTuple (n)) <- runProcedure @'[ 'Out, 'In, 'In ] noun b z
        arg1 <- pure (NP d n)
        pure (arg1)
       )
      pure (OneTuple (arg1))
    
    npOIO = \a -> do
      -- solution: arg1[] arg1[0] arg1[0,0] b[0,1] d[0,1] n[0,2] z[] z[0] z[0,2] ~a[] ~a[0] ~a[0,1] ~b[0,2] ~d[0,0] ~n[0,0]
      -- cost: 6
      (arg1,z) <- (do
        (d,b) <- runProcedure @'[ 'Out, 'In, 'Out ] det a
        (n,z) <- runProcedure @'[ 'Out, 'In, 'Out ] noun b
        arg1 <- pure (NP d n)
        pure (arg1,z)
       )
      pure (arg1,z)
    
    npOOI = \z -> do
      -- solution: a[] a[0] a[0,1] arg1[] arg1[0] arg1[0,0] b[0,2] d[0,1] n[0,2] ~b[0,1] ~d[0,0] ~n[0,0] ~z[] ~z[0] ~z[0,2]
      -- cost: 6
      (a,arg1) <- (do
        (n,b) <- runProcedure @'[ 'Out, 'Out, 'In ] noun z
        (d,a) <- runProcedure @'[ 'Out, 'Out, 'In ] det b
        arg1 <- pure (NP d n)
        pure (a,arg1)
       )
      pure (arg1,a)
    
{- vp/3
vp arg1 a z :- ((arg1 = VP v n, verb v a b, np n b z)).
constraints:
~(arg1[0,0] & v[0,0])
~(b[0,1] & b[0,2])
~(n[0,0] & n[0,2])
~(v[0,0] & v[0,1])
(b[0,1] | b[0,2])
(n[0,0] | n[0,2])
(v[0,0] | v[0,1])
((n[0,2] & (b[0,2] & ~z[0,2])) | ((n[0,2] & (~b[0,2] & z[0,2])) | ((n[0,2] & (~b[0,2] & ~z[0,2])) | ((~n[0,2] & (b[0,2] & ~z[0,2])) | ((~n[0,2] & (~b[0,2] & z[0,2])) | (~n[0,2] & (~b[0,2] & ~z[0,2])))))))
((v[0,1] & (a[0,1] & ~b[0,1])) | ((v[0,1] & (~a[0,1] & b[0,1])) | ((v[0,1] & (~a[0,1] & ~b[0,1])) | ((~v[0,1] & (a[0,1] & ~b[0,1])) | ((~v[0,1] & (~a[0,1] & b[0,1])) | (~v[0,1] & (~a[0,1] & ~b[0,1])))))))
(a[] <-> a[0])
(a[0] <-> a[0,1])
(arg1[] <-> arg1[0])
(arg1[0] <-> arg1[0,0])
(v[0,0] <-> n[0,0])
(z[] <-> z[0])
(z[0] <-> z[0,2])
1
-}

vp = rget $ (procedure @'[ 'In, 'In, 'In ] vpIII) :& (procedure @'[ 'In, 'In, 'Out ] vpIIO) :& (procedure @'[ 'In, 'Out, 'In ] vpIOI) :& (procedure @'[ 'Out, 'In, 'In ] vpOII) :& (procedure @'[ 'Out, 'In, 'Out ] vpOIO) :& (procedure @'[ 'Out, 'Out, 'In ] vpOOI) :& RNil
  where
    vpIII = \arg1 a z -> Logic.once $ do
      -- solution: b[0,1] n[0,0] v[0,0] ~a[] ~a[0] ~a[0,1] ~arg1[] ~arg1[0] ~arg1[0,0] ~b[0,2] ~n[0,2] ~v[0,1] ~z[] ~z[0] ~z[0,2]
      -- cost: 3
      () <- (do
        (VP v n) <- pure arg1
        (OneTuple (b)) <- runProcedure @'[ 'In, 'In, 'Out ] verb v a
        () <- runProcedure @'[ 'In, 'In, 'In ] np n b z
        pure ()
       )
      pure ()
    
    vpIIO = \arg1 a -> do
      -- solution: b[0,1] n[0,0] v[0,0] z[] z[0] z[0,2] ~a[] ~a[0] ~a[0,1] ~arg1[] ~arg1[0] ~arg1[0,0] ~b[0,2] ~n[0,2] ~v[0,1]
      -- cost: 4
      (z) <- (do
        (VP v n) <- pure arg1
        (OneTuple (b)) <- runProcedure @'[ 'In, 'In, 'Out ] verb v a
        (OneTuple (z)) <- runProcedure @'[ 'In, 'In, 'Out ] np n b
        pure (z)
       )
      pure (OneTuple (z))
    
    vpIOI = \arg1 z -> do
      -- solution: a[] a[0] a[0,1] b[0,2] n[0,0] v[0,0] ~arg1[] ~arg1[0] ~arg1[0,0] ~b[0,1] ~n[0,2] ~v[0,1] ~z[] ~z[0] ~z[0,2]
      -- cost: 4
      (a) <- (do
        (VP v n) <- pure arg1
        (OneTuple (b)) <- runProcedure @'[ 'In, 'Out, 'In ] np n z
        (OneTuple (a)) <- runProcedure @'[ 'In, 'Out, 'In ] verb v b
        pure (a)
       )
      pure (OneTuple (a))
    
    vpOII = \a z -> do
      -- solution: arg1[] arg1[0] arg1[0,0] b[0,1] n[0,2] v[0,1] ~a[] ~a[0] ~a[0,1] ~b[0,2] ~n[0,0] ~v[0,0] ~z[] ~z[0] ~z[0,2]
      -- cost: 5
      (arg1) <- (do
        (v,b) <- runProcedure @'[ 'Out, 'In, 'Out ] verb a
        (OneTuple (n)) <- runProcedure @'[ 'Out, 'In, 'In ] np b z
        arg1 <- pure (VP v n)
        pure (arg1)
       )
      pure (OneTuple (arg1))
    
    vpOIO = \a -> do
      -- solution: arg1[] arg1[0] arg1[0,0] b[0,1] n[0,2] v[0,1] z[] z[0] z[0,2] ~a[] ~a[0] ~a[0,1] ~b[0,2] ~n[0,0] ~v[0,0]
      -- cost: 6
      (arg1,z) <- (do
        (v,b) <- runProcedure @'[ 'Out, 'In, 'Out ] verb a
        (n,z) <- runProcedure @'[ 'Out, 'In, 'Out ] np b
        arg1 <- pure (VP v n)
        pure (arg1,z)
       )
      pure (arg1,z)
    
    vpOOI = \z -> do
      -- solution: a[] a[0] a[0,1] arg1[] arg1[0] arg1[0,0] b[0,2] n[0,2] v[0,1] ~b[0,1] ~n[0,0] ~v[0,0] ~z[] ~z[0] ~z[0,2]
      -- cost: 6
      (a,arg1) <- (do
        (n,b) <- runProcedure @'[ 'Out, 'Out, 'In ] np z
        (v,a) <- runProcedure @'[ 'Out, 'Out, 'In ] verb b
        arg1 <- pure (VP v n)
        pure (a,arg1)
       )
      pure (arg1,a)
    
{- sentence/3
sentence arg1 a z :- ((arg1 = S n v, np n a b, vp v b z)).
constraints:
~(arg1[0,0] & n[0,0])
~(b[0,1] & b[0,2])
~(n[0,0] & n[0,1])
~(v[0,0] & v[0,2])
(b[0,1] | b[0,2])
(n[0,0] | n[0,1])
(v[0,0] | v[0,2])
((n[0,1] & (a[0,1] & ~b[0,1])) | ((n[0,1] & (~a[0,1] & b[0,1])) | ((n[0,1] & (~a[0,1] & ~b[0,1])) | ((~n[0,1] & (a[0,1] & ~b[0,1])) | ((~n[0,1] & (~a[0,1] & b[0,1])) | (~n[0,1] & (~a[0,1] & ~b[0,1])))))))
((v[0,2] & (b[0,2] & ~z[0,2])) | ((v[0,2] & (~b[0,2] & z[0,2])) | ((v[0,2] & (~b[0,2] & ~z[0,2])) | ((~v[0,2] & (b[0,2] & ~z[0,2])) | ((~v[0,2] & (~b[0,2] & z[0,2])) | (~v[0,2] & (~b[0,2] & ~z[0,2])))))))
(a[] <-> a[0])
(a[0] <-> a[0,1])
(arg1[] <-> arg1[0])
(arg1[0] <-> arg1[0,0])
(n[0,0] <-> v[0,0])
(z[] <-> z[0])
(z[0] <-> z[0,2])
1
-}

sentence = rget $ (procedure @'[ 'In, 'In, 'In ] sentenceIII) :& (procedure @'[ 'In, 'In, 'Out ] sentenceIIO) :& (procedure @'[ 'In, 'Out, 'In ] sentenceIOI) :& (procedure @'[ 'Out, 'In, 'In ] sentenceOII) :& (procedure @'[ 'Out, 'In, 'Out ] sentenceOIO) :& (procedure @'[ 'Out, 'Out, 'In ] sentenceOOI) :& RNil
  where
    sentenceIII = \arg1 a z -> Logic.once $ do
      -- solution: b[0,1] n[0,0] v[0,0] ~a[] ~a[0] ~a[0,1] ~arg1[] ~arg1[0] ~arg1[0,0] ~b[0,2] ~n[0,1] ~v[0,2] ~z[] ~z[0] ~z[0,2]
      -- cost: 3
      () <- (do
        (S n v) <- pure arg1
        (OneTuple (b)) <- runProcedure @'[ 'In, 'In, 'Out ] np n a
        () <- runProcedure @'[ 'In, 'In, 'In ] vp v b z
        pure ()
       )
      pure ()
    
    sentenceIIO = \arg1 a -> do
      -- solution: b[0,1] n[0,0] v[0,0] z[] z[0] z[0,2] ~a[] ~a[0] ~a[0,1] ~arg1[] ~arg1[0] ~arg1[0,0] ~b[0,2] ~n[0,1] ~v[0,2]
      -- cost: 4
      (z) <- (do
        (S n v) <- pure arg1
        (OneTuple (b)) <- runProcedure @'[ 'In, 'In, 'Out ] np n a
        (OneTuple (z)) <- runProcedure @'[ 'In, 'In, 'Out ] vp v b
        pure (z)
       )
      pure (OneTuple (z))
    
    sentenceIOI = \arg1 z -> do
      -- solution: a[] a[0] a[0,1] b[0,2] n[0,0] v[0,0] ~arg1[] ~arg1[0] ~arg1[0,0] ~b[0,1] ~n[0,1] ~v[0,2] ~z[] ~z[0] ~z[0,2]
      -- cost: 4
      (a) <- (do
        (S n v) <- pure arg1
        (OneTuple (b)) <- runProcedure @'[ 'In, 'Out, 'In ] vp v z
        (OneTuple (a)) <- runProcedure @'[ 'In, 'Out, 'In ] np n b
        pure (a)
       )
      pure (OneTuple (a))
    
    sentenceOII = \a z -> do
      -- solution: arg1[] arg1[0] arg1[0,0] b[0,1] n[0,1] v[0,2] ~a[] ~a[0] ~a[0,1] ~b[0,2] ~n[0,0] ~v[0,0] ~z[] ~z[0] ~z[0,2]
      -- cost: 5
      (arg1) <- (do
        (n,b) <- runProcedure @'[ 'Out, 'In, 'Out ] np a
        (OneTuple (v)) <- runProcedure @'[ 'Out, 'In, 'In ] vp b z
        arg1 <- pure (S n v)
        pure (arg1)
       )
      pure (OneTuple (arg1))
    
    sentenceOIO = \a -> do
      -- solution: arg1[] arg1[0] arg1[0,0] b[0,1] n[0,1] v[0,2] z[] z[0] z[0,2] ~a[] ~a[0] ~a[0,1] ~b[0,2] ~n[0,0] ~v[0,0]
      -- cost: 6
      (arg1,z) <- (do
        (n,b) <- runProcedure @'[ 'Out, 'In, 'Out ] np a
        (v,z) <- runProcedure @'[ 'Out, 'In, 'Out ] vp b
        arg1 <- pure (S n v)
        pure (arg1,z)
       )
      pure (arg1,z)
    
    sentenceOOI = \z -> do
      -- solution: a[] a[0] a[0,1] arg1[] arg1[0] arg1[0,0] b[0,2] n[0,1] v[0,2] ~b[0,1] ~n[0,0] ~v[0,0] ~z[] ~z[0] ~z[0,2]
      -- cost: 6
      (a,arg1) <- (do
        (v,b) <- runProcedure @'[ 'Out, 'Out, 'In ] vp z
        (n,a) <- runProcedure @'[ 'Out, 'Out, 'In ] np b
        arg1 <- pure (S n v)
        pure (a,arg1)
       )
      pure (arg1,a)
    