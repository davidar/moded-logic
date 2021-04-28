{-# LANGUAGE DataKinds, FlexibleContexts, NoImplicitPrelude, NoMonomorphismRestriction, TypeApplications #-}
module DCG where

import qualified Control.Monad.Logic as Logic
import Control.Monad.Logic.Moded.Prelude

{- det/2
det arg1 x :- ((arg1 = data0:x0, x0 = x, data0 = "the"); (arg1 = data1:x1, x1 = x, data1 = "a")).
constraints:
~(arg1[0,0] & data0[0,0])
~(arg1[1,0] & data1[1,0])
~(data0[0,0] & data0[0,2])
~(data1[1,0] & data1[1,2])
~(x0[0,0] & x0[0,1])
~(x0[0,1] & x[0,1])
~(x1[1,0] & x1[1,1])
~(x1[1,1] & x[1,1])
(data0[0,0] | data0[0,2])
(data1[1,0] | data1[1,2])
(x0[0,0] | x0[0,1])
(x1[1,0] | x1[1,1])
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg1[0] <-> arg1[0,0])
(arg1[1] <-> arg1[1,0])
(data0[0,0] <-> x0[0,0])
(data1[1,0] <-> x1[1,0])
(x[] <-> x[0])
(x[] <-> x[1])
(x[0] <-> x[0,1])
(x[1] <-> x[1,1])
1
-}

det = rget $ (procedure @'[ 'In, 'In ] detII) :& (procedure @'[ 'In, 'Out ] detIO) :& (procedure @'[ 'Out, 'In ] detOI) :& RNil
  where
    detII = \arg1 x -> Logic.once $ do
      -- solution: data0[0,0] data1[1,0] x0[0,0] x1[1,0] ~arg1[] ~arg1[0] ~arg1[0,0] ~arg1[1] ~arg1[1,0] ~data0[0,2] ~data1[1,2] ~x[] ~x[0] ~x[0,1] ~x[1] ~x[1,1] ~x0[0,1] ~x1[1,1]
      -- cost: 0
      () <- (do
        (data0:x0) <- pure arg1
        guard $ x0 == x
        guard $ data0 == "the"
        pure ()
       ) <|> (do
        (data1:x1) <- pure arg1
        guard $ x1 == x
        guard $ data1 == "a"
        pure ()
       )
      pure ()
    
    detIO = \arg1 -> do
      -- solution: data0[0,0] data1[1,0] x[] x[0] x[0,1] x[1] x[1,1] x0[0,0] x1[1,0] ~arg1[] ~arg1[0] ~arg1[0,0] ~arg1[1] ~arg1[1,0] ~data0[0,2] ~data1[1,2] ~x0[0,1] ~x1[1,1]
      -- cost: 0
      (x) <- (do
        (data0:x0) <- pure arg1
        x <- pure x0
        guard $ data0 == "the"
        pure (x)
       ) <|> (do
        (data1:x1) <- pure arg1
        x <- pure x1
        guard $ data1 == "a"
        pure (x)
       )
      pure (OneTuple (x))
    
    detOI = \x -> do
      -- solution: arg1[] arg1[0] arg1[0,0] arg1[1] arg1[1,0] data0[0,2] data1[1,2] x0[0,1] x1[1,1] ~data0[0,0] ~data1[1,0] ~x[] ~x[0] ~x[0,1] ~x[1] ~x[1,1] ~x0[0,0] ~x1[1,0]
      -- cost: 0
      (arg1) <- (do
        x0 <- pure x
        data0 <- pure "the"
        arg1 <- pure (data0:x0)
        pure (arg1)
       ) <|> (do
        x1 <- pure x
        data1 <- pure "a"
        arg1 <- pure (data1:x1)
        pure (arg1)
       )
      pure (OneTuple (arg1))
    
{- noun/2
noun arg1 x :- ((arg1 = data0:x0, x0 = x, data0 = "cat"); (arg1 = data1:x1, x1 = x, data1 = "bat")).
constraints:
~(arg1[0,0] & data0[0,0])
~(arg1[1,0] & data1[1,0])
~(data0[0,0] & data0[0,2])
~(data1[1,0] & data1[1,2])
~(x0[0,0] & x0[0,1])
~(x0[0,1] & x[0,1])
~(x1[1,0] & x1[1,1])
~(x1[1,1] & x[1,1])
(data0[0,0] | data0[0,2])
(data1[1,0] | data1[1,2])
(x0[0,0] | x0[0,1])
(x1[1,0] | x1[1,1])
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg1[0] <-> arg1[0,0])
(arg1[1] <-> arg1[1,0])
(data0[0,0] <-> x0[0,0])
(data1[1,0] <-> x1[1,0])
(x[] <-> x[0])
(x[] <-> x[1])
(x[0] <-> x[0,1])
(x[1] <-> x[1,1])
1
-}

noun = rget $ (procedure @'[ 'In, 'In ] nounII) :& (procedure @'[ 'In, 'Out ] nounIO) :& (procedure @'[ 'Out, 'In ] nounOI) :& RNil
  where
    nounII = \arg1 x -> Logic.once $ do
      -- solution: data0[0,0] data1[1,0] x0[0,0] x1[1,0] ~arg1[] ~arg1[0] ~arg1[0,0] ~arg1[1] ~arg1[1,0] ~data0[0,2] ~data1[1,2] ~x[] ~x[0] ~x[0,1] ~x[1] ~x[1,1] ~x0[0,1] ~x1[1,1]
      -- cost: 0
      () <- (do
        (data0:x0) <- pure arg1
        guard $ x0 == x
        guard $ data0 == "cat"
        pure ()
       ) <|> (do
        (data1:x1) <- pure arg1
        guard $ x1 == x
        guard $ data1 == "bat"
        pure ()
       )
      pure ()
    
    nounIO = \arg1 -> do
      -- solution: data0[0,0] data1[1,0] x[] x[0] x[0,1] x[1] x[1,1] x0[0,0] x1[1,0] ~arg1[] ~arg1[0] ~arg1[0,0] ~arg1[1] ~arg1[1,0] ~data0[0,2] ~data1[1,2] ~x0[0,1] ~x1[1,1]
      -- cost: 0
      (x) <- (do
        (data0:x0) <- pure arg1
        x <- pure x0
        guard $ data0 == "cat"
        pure (x)
       ) <|> (do
        (data1:x1) <- pure arg1
        x <- pure x1
        guard $ data1 == "bat"
        pure (x)
       )
      pure (OneTuple (x))
    
    nounOI = \x -> do
      -- solution: arg1[] arg1[0] arg1[0,0] arg1[1] arg1[1,0] data0[0,2] data1[1,2] x0[0,1] x1[1,1] ~data0[0,0] ~data1[1,0] ~x[] ~x[0] ~x[0,1] ~x[1] ~x[1,1] ~x0[0,0] ~x1[1,0]
      -- cost: 0
      (arg1) <- (do
        x0 <- pure x
        data0 <- pure "cat"
        arg1 <- pure (data0:x0)
        pure (arg1)
       ) <|> (do
        x1 <- pure x
        data1 <- pure "bat"
        arg1 <- pure (data1:x1)
        pure (arg1)
       )
      pure (OneTuple (arg1))
    
{- verb/2
verb arg1 x :- ((arg1 = data0:x, data0 = "eats")).
constraints:
~(arg1[0,0] & data0[0,0])
~(data0[0,0] & data0[0,1])
(data0[0,0] | data0[0,1])
(arg1[] <-> arg1[0])
(arg1[0] <-> arg1[0,0])
(data0[0,0] <-> x[0,0])
(x[] <-> x[0])
(x[0] <-> x[0,0])
1
-}

verb = rget $ (procedure @'[ 'In, 'In ] verbII) :& (procedure @'[ 'In, 'Out ] verbIO) :& (procedure @'[ 'Out, 'In ] verbOI) :& RNil
  where
    verbII = \arg1 x -> Logic.once $ do
      -- solution: data0[0,1] ~arg1[] ~arg1[0] ~arg1[0,0] ~data0[0,0] ~x[] ~x[0] ~x[0,0]
      -- cost: 0
      () <- (do
        data0 <- pure "eats"
        guard $ arg1 == (data0:x)
        pure ()
       )
      pure ()
    
    verbIO = \arg1 -> do
      -- solution: data0[0,0] x[] x[0] x[0,0] ~arg1[] ~arg1[0] ~arg1[0,0] ~data0[0,1]
      -- cost: 0
      (x) <- (do
        (data0:x) <- pure arg1
        guard $ data0 == "eats"
        pure (x)
       )
      pure (OneTuple (x))
    
    verbOI = \x -> do
      -- solution: arg1[] arg1[0] arg1[0,0] data0[0,1] ~data0[0,0] ~x[] ~x[0] ~x[0,0]
      -- cost: 0
      (arg1) <- (do
        data0 <- pure "eats"
        arg1 <- pure (data0:x)
        pure (arg1)
       )
      pure (OneTuple (arg1))
    
{- np/2
np a z :- ((det a b, noun b z)).
constraints:
~(b[0,0] & b[0,1])
(b[0,0] | b[0,1])
((a[0,0] & ~b[0,0]) | ((~a[0,0] & b[0,0]) | (~a[0,0] & ~b[0,0])))
((b[0,1] & ~z[0,1]) | ((~b[0,1] & z[0,1]) | (~b[0,1] & ~z[0,1])))
(a[] <-> a[0])
(a[0] <-> a[0,0])
(z[] <-> z[0])
(z[0] <-> z[0,1])
1
-}

np = rget $ (procedure @'[ 'In, 'In ] npII) :& (procedure @'[ 'In, 'Out ] npIO) :& (procedure @'[ 'Out, 'In ] npOI) :& RNil
  where
    npII = \a z -> Logic.once $ do
      -- solution: b[0,0] ~a[] ~a[0] ~a[0,0] ~b[0,1] ~z[] ~z[0] ~z[0,1]
      -- cost: 3
      () <- (do
        (OneTuple (b)) <- runProcedure @'[ 'In, 'Out ] det a
        () <- runProcedure @'[ 'In, 'In ] noun b z
        pure ()
       )
      pure ()
    
    npIO = \a -> do
      -- solution: b[0,0] z[] z[0] z[0,1] ~a[] ~a[0] ~a[0,0] ~b[0,1]
      -- cost: 4
      (z) <- (do
        (OneTuple (b)) <- runProcedure @'[ 'In, 'Out ] det a
        (OneTuple (z)) <- runProcedure @'[ 'In, 'Out ] noun b
        pure (z)
       )
      pure (OneTuple (z))
    
    npOI = \z -> do
      -- solution: a[] a[0] a[0,0] b[0,1] ~b[0,0] ~z[] ~z[0] ~z[0,1]
      -- cost: 4
      (a) <- (do
        (OneTuple (b)) <- runProcedure @'[ 'Out, 'In ] noun z
        (OneTuple (a)) <- runProcedure @'[ 'Out, 'In ] det b
        pure (a)
       )
      pure (OneTuple (a))
    
{- vp/2
vp a z :- ((verb a b, np b z)).
constraints:
~(b[0,0] & b[0,1])
(b[0,0] | b[0,1])
((a[0,0] & ~b[0,0]) | ((~a[0,0] & b[0,0]) | (~a[0,0] & ~b[0,0])))
((b[0,1] & ~z[0,1]) | ((~b[0,1] & z[0,1]) | (~b[0,1] & ~z[0,1])))
(a[] <-> a[0])
(a[0] <-> a[0,0])
(z[] <-> z[0])
(z[0] <-> z[0,1])
1
-}

vp = rget $ (procedure @'[ 'In, 'In ] vpII) :& (procedure @'[ 'In, 'Out ] vpIO) :& (procedure @'[ 'Out, 'In ] vpOI) :& RNil
  where
    vpII = \a z -> Logic.once $ do
      -- solution: b[0,0] ~a[] ~a[0] ~a[0,0] ~b[0,1] ~z[] ~z[0] ~z[0,1]
      -- cost: 3
      () <- (do
        (OneTuple (b)) <- runProcedure @'[ 'In, 'Out ] verb a
        () <- runProcedure @'[ 'In, 'In ] np b z
        pure ()
       )
      pure ()
    
    vpIO = \a -> do
      -- solution: b[0,0] z[] z[0] z[0,1] ~a[] ~a[0] ~a[0,0] ~b[0,1]
      -- cost: 4
      (z) <- (do
        (OneTuple (b)) <- runProcedure @'[ 'In, 'Out ] verb a
        (OneTuple (z)) <- runProcedure @'[ 'In, 'Out ] np b
        pure (z)
       )
      pure (OneTuple (z))
    
    vpOI = \z -> do
      -- solution: a[] a[0] a[0,0] b[0,1] ~b[0,0] ~z[] ~z[0] ~z[0,1]
      -- cost: 4
      (a) <- (do
        (OneTuple (b)) <- runProcedure @'[ 'Out, 'In ] np z
        (OneTuple (a)) <- runProcedure @'[ 'Out, 'In ] verb b
        pure (a)
       )
      pure (OneTuple (a))
    
{- sentence/2
sentence a z :- ((np a b, vp b z)).
constraints:
~(b[0,0] & b[0,1])
(b[0,0] | b[0,1])
((a[0,0] & ~b[0,0]) | ((~a[0,0] & b[0,0]) | (~a[0,0] & ~b[0,0])))
((b[0,1] & ~z[0,1]) | ((~b[0,1] & z[0,1]) | (~b[0,1] & ~z[0,1])))
(a[] <-> a[0])
(a[0] <-> a[0,0])
(z[] <-> z[0])
(z[0] <-> z[0,1])
1
-}

sentence = rget $ (procedure @'[ 'In, 'In ] sentenceII) :& (procedure @'[ 'In, 'Out ] sentenceIO) :& (procedure @'[ 'Out, 'In ] sentenceOI) :& RNil
  where
    sentenceII = \a z -> Logic.once $ do
      -- solution: b[0,0] ~a[] ~a[0] ~a[0,0] ~b[0,1] ~z[] ~z[0] ~z[0,1]
      -- cost: 3
      () <- (do
        (OneTuple (b)) <- runProcedure @'[ 'In, 'Out ] np a
        () <- runProcedure @'[ 'In, 'In ] vp b z
        pure ()
       )
      pure ()
    
    sentenceIO = \a -> do
      -- solution: b[0,0] z[] z[0] z[0,1] ~a[] ~a[0] ~a[0,0] ~b[0,1]
      -- cost: 4
      (z) <- (do
        (OneTuple (b)) <- runProcedure @'[ 'In, 'Out ] np a
        (OneTuple (z)) <- runProcedure @'[ 'In, 'Out ] vp b
        pure (z)
       )
      pure (OneTuple (z))
    
    sentenceOI = \z -> do
      -- solution: a[] a[0] a[0,0] b[0,1] ~b[0,0] ~z[] ~z[0] ~z[0,1]
      -- cost: 4
      (a) <- (do
        (OneTuple (b)) <- runProcedure @'[ 'Out, 'In ] vp z
        (OneTuple (a)) <- runProcedure @'[ 'Out, 'In ] np b
        pure (a)
       )
      pure (OneTuple (a))
    