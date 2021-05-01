{-# LANGUAGE DataKinds, FlexibleContexts, NoImplicitPrelude, NoMonomorphismRestriction, TypeApplications #-}
module DCG where

import qualified Control.Monad.Logic as Logic
import Control.Monad.Logic.Moded.Prelude

data Tree = S Tree Tree | NP String String | VP String Tree deriving (Eq, Ord, Show)
{- append/3
append arg1 b arg3 :- ((arg1 = [], arg3 = b); (arg1 = h0:t, h0 = h, arg3 = h1:tb, h1 = h, append t b tb)).
constraints:
~(arg1[1,0] & h0[1,0])
~(arg3[0,1] & b[0,1])
~(arg3[1,2] & h1[1,2])
~(h[1,1] & h[1,3])
~(h0[1,0] & h0[1,1])
~(h0[1,1] & h[1,1])
~(h1[1,2] & h1[1,3])
~(h1[1,3] & h[1,3])
~(t[1,0] & t[1,4])
~(tb[1,2] & tb[1,4])
(h[1,1] | h[1,3])
(h0[1,0] | h0[1,1])
(h1[1,2] | h1[1,3])
(t[1,0] | t[1,4])
(tb[1,2] | tb[1,4])
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg1[0] <-> arg1[0,0])
(arg1[1] <-> arg1[1,0])
(arg3[] <-> arg3[0])
(arg3[] <-> arg3[1])
(arg3[0] <-> arg3[0,1])
(arg3[1] <-> arg3[1,2])
(b[] <-> b[0])
(b[] <-> b[1])
(b[0] <-> b[0,1])
(b[1] <-> b[1,4])
(b[1,4] <-> b[])
(h0[1,0] <-> t[1,0])
(h1[1,2] <-> tb[1,2])
(t[1,4] <-> arg1[])
(tb[1,4] <-> arg3[])
1
-}

append = rget $ (procedure @'[ 'In, 'In, 'In ] appendIII) :& (procedure @'[ 'In, 'In, 'Out ] appendIIO) :& (procedure @'[ 'In, 'Out, 'In ] appendIOI) :& (procedure @'[ 'Out, 'In, 'In ] appendOII) :& (procedure @'[ 'Out, 'Out, 'In ] appendOOI) :& RNil
  where
    appendIII = \arg1 b arg3 -> Logic.once $ do
      -- solution: h[1,1] h0[1,0] h1[1,2] t[1,0] tb[1,2] ~arg1[] ~arg1[0] ~arg1[0,0] ~arg1[1] ~arg1[1,0] ~arg3[] ~arg3[0] ~arg3[0,1] ~arg3[1] ~arg3[1,2] ~b[] ~b[0] ~b[0,1] ~b[1] ~b[1,4] ~h[1,3] ~h0[1,1] ~h1[1,3] ~t[1,4] ~tb[1,4]
      -- cost: 1
      () <- (do
        guard $ arg3 == b
        guard $ arg1 == []
        pure ()
       ) <|> (do
        (h0:t) <- pure arg1
        h <- pure h0
        (h1:tb) <- pure arg3
        guard $ h1 == h
        () <- appendIII t b tb
        pure ()
       )
      pure ()
    
    appendIIO = \arg1 b -> do
      -- solution: arg3[] arg3[0] arg3[0,1] arg3[1] arg3[1,2] h[1,1] h0[1,0] h1[1,3] t[1,0] tb[1,4] ~arg1[] ~arg1[0] ~arg1[0,0] ~arg1[1] ~arg1[1,0] ~b[] ~b[0] ~b[0,1] ~b[1] ~b[1,4] ~h[1,3] ~h0[1,1] ~h1[1,2] ~t[1,4] ~tb[1,2]
      -- cost: 2
      (arg3) <- (do
        arg3 <- pure b
        guard $ arg1 == []
        pure (arg3)
       ) <|> (do
        (h0:t) <- pure arg1
        h <- pure h0
        h1 <- pure h
        (OneTuple (tb)) <- appendIIO t b
        arg3 <- pure (h1:tb)
        pure (arg3)
       )
      pure (OneTuple (arg3))
    
    appendIOI = \arg1 arg3 -> do
      -- solution: b[] b[0] b[0,1] b[1] b[1,4] h[1,1] h0[1,0] h1[1,2] t[1,0] tb[1,2] ~arg1[] ~arg1[0] ~arg1[0,0] ~arg1[1] ~arg1[1,0] ~arg3[] ~arg3[0] ~arg3[0,1] ~arg3[1] ~arg3[1,2] ~h[1,3] ~h0[1,1] ~h1[1,3] ~t[1,4] ~tb[1,4]
      -- cost: 2
      (b) <- (do
        b <- pure arg3
        guard $ arg1 == []
        pure (b)
       ) <|> (do
        (h0:t) <- pure arg1
        h <- pure h0
        (h1:tb) <- pure arg3
        guard $ h1 == h
        (OneTuple (b)) <- appendIOI t tb
        pure (b)
       )
      pure (OneTuple (b))
    
    appendOII = \b arg3 -> do
      -- solution: arg1[] arg1[0] arg1[0,0] arg1[1] arg1[1,0] h[1,3] h0[1,1] h1[1,2] t[1,4] tb[1,2] ~arg3[] ~arg3[0] ~arg3[0,1] ~arg3[1] ~arg3[1,2] ~b[] ~b[0] ~b[0,1] ~b[1] ~b[1,4] ~h[1,1] ~h0[1,0] ~h1[1,3] ~t[1,0] ~tb[1,4]
      -- cost: 2
      (arg1) <- (do
        guard $ arg3 == b
        arg1 <- pure []
        pure (arg1)
       ) <|> (do
        (h1:tb) <- pure arg3
        h <- pure h1
        h0 <- pure h
        (OneTuple (t)) <- appendOII b tb
        arg1 <- pure (h0:t)
        pure (arg1)
       )
      pure (OneTuple (arg1))
    
    appendOOI = \arg3 -> do
      -- solution: arg1[] arg1[0] arg1[0,0] arg1[1] arg1[1,0] b[] b[0] b[0,1] b[1] b[1,4] h[1,3] h0[1,1] h1[1,2] t[1,4] tb[1,2] ~arg3[] ~arg3[0] ~arg3[0,1] ~arg3[1] ~arg3[1,2] ~h[1,1] ~h0[1,0] ~h1[1,3] ~t[1,0] ~tb[1,4]
      -- cost: 3
      (arg1,b) <- (do
        b <- pure arg3
        arg1 <- pure []
        pure (arg1,b)
       ) <|> (do
        (h1:tb) <- pure arg3
        h <- pure h1
        h0 <- pure h
        (t,b) <- appendOOI tb
        arg1 <- pure (h0:t)
        pure (arg1,b)
       )
      pure (arg1,b)
    
{- det/1
det arg1 :- ((arg1 = "the"); (arg1 = "a")).
constraints:
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg1[0] <-> arg1[0,0])
(arg1[1] <-> arg1[1,0])
-}

det = rget $ (procedure @'[ 'In ] detI) :& (procedure @'[ 'Out ] detO) :& RNil
  where
    detI = \arg1 -> Logic.once $ do
      -- solution: ~arg1[] ~arg1[0] ~arg1[0,0] ~arg1[1] ~arg1[1,0]
      -- cost: 0
      () <- (do
        guard $ arg1 == "the"
        pure ()
       ) <|> (do
        guard $ arg1 == "a"
        pure ()
       )
      pure ()
    
    detO = do
      -- solution: arg1[] arg1[0] arg1[0,0] arg1[1] arg1[1,0]
      -- cost: 0
      (arg1) <- (do
        arg1 <- pure "the"
        pure (arg1)
       ) <|> (do
        arg1 <- pure "a"
        pure (arg1)
       )
      pure (OneTuple (arg1))
    
{- noun/1
noun arg1 :- ((arg1 = "cat"); (arg1 = "bat")).
constraints:
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg1[0] <-> arg1[0,0])
(arg1[1] <-> arg1[1,0])
-}

noun = rget $ (procedure @'[ 'In ] nounI) :& (procedure @'[ 'Out ] nounO) :& RNil
  where
    nounI = \arg1 -> Logic.once $ do
      -- solution: ~arg1[] ~arg1[0] ~arg1[0,0] ~arg1[1] ~arg1[1,0]
      -- cost: 0
      () <- (do
        guard $ arg1 == "cat"
        pure ()
       ) <|> (do
        guard $ arg1 == "bat"
        pure ()
       )
      pure ()
    
    nounO = do
      -- solution: arg1[] arg1[0] arg1[0,0] arg1[1] arg1[1,0]
      -- cost: 0
      (arg1) <- (do
        arg1 <- pure "cat"
        pure (arg1)
       ) <|> (do
        arg1 <- pure "bat"
        pure (arg1)
       )
      pure (OneTuple (arg1))
    
{- verb/1
verb arg1 :- ((arg1 = "eats")).
constraints:
(arg1[] <-> arg1[0])
(arg1[0] <-> arg1[0,0])
-}

verb = rget $ (procedure @'[ 'In ] verbI) :& (procedure @'[ 'Out ] verbO) :& RNil
  where
    verbI = \arg1 -> Logic.once $ do
      -- solution: ~arg1[] ~arg1[0] ~arg1[0,0]
      -- cost: 0
      () <- (do
        guard $ arg1 == "eats"
        pure ()
       )
      pure ()
    
    verbO = do
      -- solution: arg1[] arg1[0] arg1[0,0]
      -- cost: 0
      (arg1) <- (do
        arg1 <- pure "eats"
        pure (arg1)
       )
      pure (OneTuple (arg1))
    
{- np/3
np arg1 z a :- ((arg1 = NP d0 n1, d0 = d, n1 = n, det d, noun n, append data1 z a, data0 = [], data1 = d2:n3:data0, d2 = d, n3 = n)).
constraints:
~(arg1[0,0] & d0[0,0])
~(d[0,1] & d[0,3])
~(d[0,1] & d[0,8])
~(d[0,3] & d[0,8])
~(d0[0,0] & d0[0,1])
~(d0[0,1] & d[0,1])
~(d2[0,7] & d2[0,8])
~(d2[0,8] & d[0,8])
~(data0[0,6] & data0[0,7])
~(data1[0,5] & data1[0,7])
~(data1[0,7] & d2[0,7])
~(n[0,2] & n[0,4])
~(n[0,2] & n[0,9])
~(n[0,4] & n[0,9])
~(n1[0,0] & n1[0,2])
~(n1[0,2] & n[0,2])
~(n3[0,7] & n3[0,9])
~(n3[0,9] & n[0,9])
(d[0,1] | (d[0,3] | d[0,8]))
(d[0,3] | ~d[0,3])
(d0[0,0] | d0[0,1])
(d2[0,7] | d2[0,8])
(data0[0,6] | data0[0,7])
(data1[0,5] | data1[0,7])
(n[0,2] | (n[0,4] | n[0,9]))
(n[0,4] | ~n[0,4])
(n1[0,0] | n1[0,2])
(n3[0,7] | n3[0,9])
((data1[0,5] & (z[0,5] & ~a[0,5])) | ((data1[0,5] & (~z[0,5] & ~a[0,5])) | ((~data1[0,5] & (z[0,5] & ~a[0,5])) | ((~data1[0,5] & (~z[0,5] & a[0,5])) | (~data1[0,5] & (~z[0,5] & ~a[0,5]))))))
(a[] <-> a[0])
(a[0] <-> a[0,5])
(arg1[] <-> arg1[0])
(arg1[0] <-> arg1[0,0])
(d0[0,0] <-> n1[0,0])
(d2[0,7] <-> data0[0,7])
(d2[0,7] <-> n3[0,7])
(z[] <-> z[0])
(z[0] <-> z[0,5])
1
-}

np = rget $ (procedure @'[ 'In, 'In, 'In ] npIII) :& (procedure @'[ 'In, 'In, 'Out ] npIIO) :& (procedure @'[ 'In, 'Out, 'In ] npIOI) :& (procedure @'[ 'Out, 'In, 'In ] npOII) :& (procedure @'[ 'Out, 'In, 'Out ] npOIO) :& (procedure @'[ 'Out, 'Out, 'In ] npOOI) :& RNil
  where
    npIII = \arg1 z a -> Logic.once $ do
      -- solution: d[0,1] d0[0,0] d2[0,8] data0[0,6] data1[0,7] n[0,2] n1[0,0] n3[0,9] ~a[] ~a[0] ~a[0,5] ~arg1[] ~arg1[0] ~arg1[0,0] ~d[0,3] ~d[0,8] ~d0[0,1] ~d2[0,7] ~data0[0,7] ~data1[0,5] ~n[0,4] ~n[0,9] ~n1[0,2] ~n3[0,7] ~z[] ~z[0] ~z[0,5]
      -- cost: 3
      () <- (do
        (NP d0 n1) <- pure arg1
        d <- pure d0
        d2 <- pure d
        n <- pure n1
        n3 <- pure n
        data0 <- pure []
        data1 <- pure (d2:n3:data0)
        () <- runProcedure @'[ 'In, 'In, 'In ] append data1 z a
        () <- runProcedure @'[ 'In ] det d
        () <- runProcedure @'[ 'In ] noun n
        pure ()
       )
      pure ()
    
    npIIO = \arg1 z -> do
      -- solution: a[] a[0] a[0,5] d[0,1] d0[0,0] d2[0,8] data0[0,6] data1[0,7] n[0,2] n1[0,0] n3[0,9] ~arg1[] ~arg1[0] ~arg1[0,0] ~d[0,3] ~d[0,8] ~d0[0,1] ~d2[0,7] ~data0[0,7] ~data1[0,5] ~n[0,4] ~n[0,9] ~n1[0,2] ~n3[0,7] ~z[] ~z[0] ~z[0,5]
      -- cost: 4
      (a) <- (do
        (NP d0 n1) <- pure arg1
        d <- pure d0
        d2 <- pure d
        n <- pure n1
        n3 <- pure n
        data0 <- pure []
        data1 <- pure (d2:n3:data0)
        () <- runProcedure @'[ 'In ] det d
        () <- runProcedure @'[ 'In ] noun n
        (OneTuple (a)) <- runProcedure @'[ 'In, 'In, 'Out ] append data1 z
        pure (a)
       )
      pure (OneTuple (a))
    
    npIOI = \arg1 a -> do
      -- solution: d[0,1] d0[0,0] d2[0,8] data0[0,6] data1[0,7] n[0,2] n1[0,0] n3[0,9] z[] z[0] z[0,5] ~a[] ~a[0] ~a[0,5] ~arg1[] ~arg1[0] ~arg1[0,0] ~d[0,3] ~d[0,8] ~d0[0,1] ~d2[0,7] ~data0[0,7] ~data1[0,5] ~n[0,4] ~n[0,9] ~n1[0,2] ~n3[0,7]
      -- cost: 4
      (z) <- (do
        (NP d0 n1) <- pure arg1
        d <- pure d0
        d2 <- pure d
        n <- pure n1
        n3 <- pure n
        data0 <- pure []
        data1 <- pure (d2:n3:data0)
        () <- runProcedure @'[ 'In ] det d
        () <- runProcedure @'[ 'In ] noun n
        (OneTuple (z)) <- runProcedure @'[ 'In, 'Out, 'In ] append data1 a
        pure (z)
       )
      pure (OneTuple (z))
    
    npOII = \z a -> do
      -- solution: arg1[] arg1[0] arg1[0,0] d[0,8] d0[0,1] d2[0,7] data0[0,7] data1[0,5] n[0,9] n1[0,2] n3[0,7] ~a[] ~a[0] ~a[0,5] ~d[0,1] ~d[0,3] ~d0[0,0] ~d2[0,8] ~data0[0,6] ~data1[0,7] ~n[0,2] ~n[0,4] ~n1[0,0] ~n3[0,9] ~z[] ~z[0] ~z[0,5]
      -- cost: 4
      (arg1) <- (do
        (OneTuple (data1)) <- runProcedure @'[ 'Out, 'In, 'In ] append z a
        (d2:n3:data0) <- pure data1
        d <- pure d2
        d0 <- pure d
        () <- runProcedure @'[ 'In ] det d
        n <- pure n3
        n1 <- pure n
        arg1 <- pure (NP d0 n1)
        () <- runProcedure @'[ 'In ] noun n
        guard $ data0 == []
        pure (arg1)
       )
      pure (OneTuple (arg1))
    
    npOIO = \z -> do
      -- solution: a[] a[0] a[0,5] arg1[] arg1[0] arg1[0,0] d[0,3] d0[0,1] d2[0,8] data0[0,6] data1[0,7] n[0,4] n1[0,2] n3[0,9] ~d[0,1] ~d[0,8] ~d0[0,0] ~d2[0,7] ~data0[0,7] ~data1[0,5] ~n[0,2] ~n[0,9] ~n1[0,0] ~n3[0,7] ~z[] ~z[0] ~z[0,5]
      -- cost: 6
      (a,arg1) <- (do
        data0 <- pure []
        (OneTuple (d)) <- runProcedure @'[ 'Out ] det 
        d0 <- pure d
        d2 <- pure d
        (OneTuple (n)) <- runProcedure @'[ 'Out ] noun 
        n1 <- pure n
        arg1 <- pure (NP d0 n1)
        n3 <- pure n
        data1 <- pure (d2:n3:data0)
        (OneTuple (a)) <- runProcedure @'[ 'In, 'In, 'Out ] append data1 z
        pure (a,arg1)
       )
      pure (arg1,a)
    
    npOOI = \a -> do
      -- solution: arg1[] arg1[0] arg1[0,0] d[0,8] d0[0,1] d2[0,7] data0[0,7] data1[0,5] n[0,9] n1[0,2] n3[0,7] z[] z[0] z[0,5] ~a[] ~a[0] ~a[0,5] ~d[0,1] ~d[0,3] ~d0[0,0] ~d2[0,8] ~data0[0,6] ~data1[0,7] ~n[0,2] ~n[0,4] ~n1[0,0] ~n3[0,9]
      -- cost: 5
      (arg1,z) <- (do
        (data1,z) <- runProcedure @'[ 'Out, 'Out, 'In ] append a
        (d2:n3:data0) <- pure data1
        d <- pure d2
        d0 <- pure d
        () <- runProcedure @'[ 'In ] det d
        n <- pure n3
        n1 <- pure n
        arg1 <- pure (NP d0 n1)
        () <- runProcedure @'[ 'In ] noun n
        guard $ data0 == []
        pure (arg1,z)
       )
      pure (arg1,z)
    
{- vp/3
vp arg1 z a :- ((arg1 = VP v0 n, v0 = v, verb v, append data1 b a, data0 = [], data1 = v1:data0, v1 = v, np n z b)).
constraints:
~(arg1[0,0] & v0[0,0])
~(b[0,3] & b[0,7])
~(data0[0,4] & data0[0,5])
~(data1[0,3] & data1[0,5])
~(data1[0,5] & v1[0,5])
~(n[0,0] & n[0,7])
~(v[0,1] & v[0,2])
~(v[0,1] & v[0,6])
~(v[0,2] & v[0,6])
~(v0[0,0] & v0[0,1])
~(v0[0,1] & v[0,1])
~(v1[0,5] & v1[0,6])
~(v1[0,6] & v[0,6])
(b[0,3] | b[0,7])
(data0[0,4] | data0[0,5])
(data1[0,3] | data1[0,5])
(n[0,0] | n[0,7])
(v[0,1] | (v[0,2] | v[0,6]))
(v[0,2] | ~v[0,2])
(v0[0,0] | v0[0,1])
(v1[0,5] | v1[0,6])
((data1[0,3] & (b[0,3] & ~a[0,3])) | ((data1[0,3] & (~b[0,3] & ~a[0,3])) | ((~data1[0,3] & (b[0,3] & ~a[0,3])) | ((~data1[0,3] & (~b[0,3] & a[0,3])) | (~data1[0,3] & (~b[0,3] & ~a[0,3]))))))
((n[0,7] & (z[0,7] & ~b[0,7])) | ((n[0,7] & (~z[0,7] & b[0,7])) | ((n[0,7] & (~z[0,7] & ~b[0,7])) | ((~n[0,7] & (z[0,7] & ~b[0,7])) | ((~n[0,7] & (~z[0,7] & b[0,7])) | (~n[0,7] & (~z[0,7] & ~b[0,7])))))))
(a[] <-> a[0])
(a[0] <-> a[0,3])
(arg1[] <-> arg1[0])
(arg1[0] <-> arg1[0,0])
(v0[0,0] <-> n[0,0])
(v1[0,5] <-> data0[0,5])
(z[] <-> z[0])
(z[0] <-> z[0,7])
1
-}

vp = rget $ (procedure @'[ 'In, 'In, 'In ] vpIII) :& (procedure @'[ 'In, 'In, 'Out ] vpIIO) :& (procedure @'[ 'In, 'Out, 'In ] vpIOI) :& (procedure @'[ 'Out, 'In, 'In ] vpOII) :& (procedure @'[ 'Out, 'In, 'Out ] vpOIO) :& (procedure @'[ 'Out, 'Out, 'In ] vpOOI) :& RNil
  where
    vpIII = \arg1 z a -> Logic.once $ do
      -- solution: b[0,3] data0[0,4] data1[0,5] n[0,0] v[0,1] v0[0,0] v1[0,6] ~a[] ~a[0] ~a[0,3] ~arg1[] ~arg1[0] ~arg1[0,0] ~b[0,7] ~data0[0,5] ~data1[0,3] ~n[0,7] ~v[0,2] ~v[0,6] ~v0[0,1] ~v1[0,5] ~z[] ~z[0] ~z[0,7]
      -- cost: 4
      () <- (do
        (VP v0 n) <- pure arg1
        v <- pure v0
        v1 <- pure v
        data0 <- pure []
        data1 <- pure (v1:data0)
        () <- runProcedure @'[ 'In ] verb v
        (OneTuple (b)) <- runProcedure @'[ 'In, 'Out, 'In ] append data1 a
        () <- runProcedure @'[ 'In, 'In, 'In ] np n z b
        pure ()
       )
      pure ()
    
    vpIIO = \arg1 z -> do
      -- solution: a[] a[0] a[0,3] b[0,7] data0[0,4] data1[0,5] n[0,0] v[0,1] v0[0,0] v1[0,6] ~arg1[] ~arg1[0] ~arg1[0,0] ~b[0,3] ~data0[0,5] ~data1[0,3] ~n[0,7] ~v[0,2] ~v[0,6] ~v0[0,1] ~v1[0,5] ~z[] ~z[0] ~z[0,7]
      -- cost: 5
      (a) <- (do
        (VP v0 n) <- pure arg1
        v <- pure v0
        v1 <- pure v
        data0 <- pure []
        data1 <- pure (v1:data0)
        () <- runProcedure @'[ 'In ] verb v
        (OneTuple (b)) <- runProcedure @'[ 'In, 'In, 'Out ] np n z
        (OneTuple (a)) <- runProcedure @'[ 'In, 'In, 'Out ] append data1 b
        pure (a)
       )
      pure (OneTuple (a))
    
    vpIOI = \arg1 a -> do
      -- solution: b[0,3] data0[0,4] data1[0,5] n[0,0] v[0,1] v0[0,0] v1[0,6] z[] z[0] z[0,7] ~a[] ~a[0] ~a[0,3] ~arg1[] ~arg1[0] ~arg1[0,0] ~b[0,7] ~data0[0,5] ~data1[0,3] ~n[0,7] ~v[0,2] ~v[0,6] ~v0[0,1] ~v1[0,5]
      -- cost: 5
      (z) <- (do
        (VP v0 n) <- pure arg1
        v <- pure v0
        v1 <- pure v
        data0 <- pure []
        data1 <- pure (v1:data0)
        () <- runProcedure @'[ 'In ] verb v
        (OneTuple (b)) <- runProcedure @'[ 'In, 'Out, 'In ] append data1 a
        (OneTuple (z)) <- runProcedure @'[ 'In, 'Out, 'In ] np n b
        pure (z)
       )
      pure (OneTuple (z))
    
    vpOII = \z a -> do
      -- solution: arg1[] arg1[0] arg1[0,0] b[0,3] data0[0,4] data1[0,5] n[0,7] v[0,2] v0[0,1] v1[0,6] ~a[] ~a[0] ~a[0,3] ~b[0,7] ~data0[0,5] ~data1[0,3] ~n[0,0] ~v[0,1] ~v[0,6] ~v0[0,0] ~v1[0,5] ~z[] ~z[0] ~z[0,7]
      -- cost: 6
      (arg1) <- (do
        data0 <- pure []
        (OneTuple (v)) <- runProcedure @'[ 'Out ] verb 
        v0 <- pure v
        v1 <- pure v
        data1 <- pure (v1:data0)
        (OneTuple (b)) <- runProcedure @'[ 'In, 'Out, 'In ] append data1 a
        (OneTuple (n)) <- runProcedure @'[ 'Out, 'In, 'In ] np z b
        arg1 <- pure (VP v0 n)
        pure (arg1)
       )
      pure (OneTuple (arg1))
    
    vpOIO = \z -> do
      -- solution: a[] a[0] a[0,3] arg1[] arg1[0] arg1[0,0] b[0,7] data0[0,4] data1[0,5] n[0,7] v[0,2] v0[0,1] v1[0,6] ~b[0,3] ~data0[0,5] ~data1[0,3] ~n[0,0] ~v[0,1] ~v[0,6] ~v0[0,0] ~v1[0,5] ~z[] ~z[0] ~z[0,7]
      -- cost: 7
      (a,arg1) <- (do
        data0 <- pure []
        (OneTuple (v)) <- runProcedure @'[ 'Out ] verb 
        v0 <- pure v
        v1 <- pure v
        data1 <- pure (v1:data0)
        (n,b) <- runProcedure @'[ 'Out, 'In, 'Out ] np z
        arg1 <- pure (VP v0 n)
        (OneTuple (a)) <- runProcedure @'[ 'In, 'In, 'Out ] append data1 b
        pure (a,arg1)
       )
      pure (arg1,a)
    
    vpOOI = \a -> do
      -- solution: arg1[] arg1[0] arg1[0,0] b[0,3] data0[0,4] data1[0,5] n[0,7] v[0,2] v0[0,1] v1[0,6] z[] z[0] z[0,7] ~a[] ~a[0] ~a[0,3] ~b[0,7] ~data0[0,5] ~data1[0,3] ~n[0,0] ~v[0,1] ~v[0,6] ~v0[0,0] ~v1[0,5]
      -- cost: 7
      (arg1,z) <- (do
        data0 <- pure []
        (OneTuple (v)) <- runProcedure @'[ 'Out ] verb 
        v0 <- pure v
        v1 <- pure v
        data1 <- pure (v1:data0)
        (OneTuple (b)) <- runProcedure @'[ 'In, 'Out, 'In ] append data1 a
        (n,z) <- runProcedure @'[ 'Out, 'Out, 'In ] np b
        arg1 <- pure (VP v0 n)
        pure (arg1,z)
       )
      pure (arg1,z)
    
{- sentence/3
sentence arg1 z a :- ((arg1 = S n v, np n b a, vp v z b)).
constraints:
~(arg1[0,0] & n[0,0])
~(b[0,1] & b[0,2])
~(n[0,0] & n[0,1])
~(v[0,0] & v[0,2])
(b[0,1] | b[0,2])
(n[0,0] | n[0,1])
(v[0,0] | v[0,2])
((n[0,1] & (b[0,1] & ~a[0,1])) | ((n[0,1] & (~b[0,1] & a[0,1])) | ((n[0,1] & (~b[0,1] & ~a[0,1])) | ((~n[0,1] & (b[0,1] & ~a[0,1])) | ((~n[0,1] & (~b[0,1] & a[0,1])) | (~n[0,1] & (~b[0,1] & ~a[0,1])))))))
((v[0,2] & (z[0,2] & ~b[0,2])) | ((v[0,2] & (~z[0,2] & b[0,2])) | ((v[0,2] & (~z[0,2] & ~b[0,2])) | ((~v[0,2] & (z[0,2] & ~b[0,2])) | ((~v[0,2] & (~z[0,2] & b[0,2])) | (~v[0,2] & (~z[0,2] & ~b[0,2])))))))
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
    sentenceIII = \arg1 z a -> Logic.once $ do
      -- solution: b[0,1] n[0,0] v[0,0] ~a[] ~a[0] ~a[0,1] ~arg1[] ~arg1[0] ~arg1[0,0] ~b[0,2] ~n[0,1] ~v[0,2] ~z[] ~z[0] ~z[0,2]
      -- cost: 3
      () <- (do
        (S n v) <- pure arg1
        (OneTuple (b)) <- runProcedure @'[ 'In, 'Out, 'In ] np n a
        () <- runProcedure @'[ 'In, 'In, 'In ] vp v z b
        pure ()
       )
      pure ()
    
    sentenceIIO = \arg1 z -> do
      -- solution: a[] a[0] a[0,1] b[0,2] n[0,0] v[0,0] ~arg1[] ~arg1[0] ~arg1[0,0] ~b[0,1] ~n[0,1] ~v[0,2] ~z[] ~z[0] ~z[0,2]
      -- cost: 4
      (a) <- (do
        (S n v) <- pure arg1
        (OneTuple (b)) <- runProcedure @'[ 'In, 'In, 'Out ] vp v z
        (OneTuple (a)) <- runProcedure @'[ 'In, 'In, 'Out ] np n b
        pure (a)
       )
      pure (OneTuple (a))
    
    sentenceIOI = \arg1 a -> do
      -- solution: b[0,1] n[0,0] v[0,0] z[] z[0] z[0,2] ~a[] ~a[0] ~a[0,1] ~arg1[] ~arg1[0] ~arg1[0,0] ~b[0,2] ~n[0,1] ~v[0,2]
      -- cost: 4
      (z) <- (do
        (S n v) <- pure arg1
        (OneTuple (b)) <- runProcedure @'[ 'In, 'Out, 'In ] np n a
        (OneTuple (z)) <- runProcedure @'[ 'In, 'Out, 'In ] vp v b
        pure (z)
       )
      pure (OneTuple (z))
    
    sentenceOII = \z a -> do
      -- solution: arg1[] arg1[0] arg1[0,0] b[0,1] n[0,1] v[0,2] ~a[] ~a[0] ~a[0,1] ~b[0,2] ~n[0,0] ~v[0,0] ~z[] ~z[0] ~z[0,2]
      -- cost: 5
      (arg1) <- (do
        (n,b) <- runProcedure @'[ 'Out, 'Out, 'In ] np a
        (OneTuple (v)) <- runProcedure @'[ 'Out, 'In, 'In ] vp z b
        arg1 <- pure (S n v)
        pure (arg1)
       )
      pure (OneTuple (arg1))
    
    sentenceOIO = \z -> do
      -- solution: a[] a[0] a[0,1] arg1[] arg1[0] arg1[0,0] b[0,2] n[0,1] v[0,2] ~b[0,1] ~n[0,0] ~v[0,0] ~z[] ~z[0] ~z[0,2]
      -- cost: 6
      (a,arg1) <- (do
        (v,b) <- runProcedure @'[ 'Out, 'In, 'Out ] vp z
        (n,a) <- runProcedure @'[ 'Out, 'In, 'Out ] np b
        arg1 <- pure (S n v)
        pure (a,arg1)
       )
      pure (arg1,a)
    
    sentenceOOI = \a -> do
      -- solution: arg1[] arg1[0] arg1[0,0] b[0,1] n[0,1] v[0,2] z[] z[0] z[0,2] ~a[] ~a[0] ~a[0,1] ~b[0,2] ~n[0,0] ~v[0,0]
      -- cost: 6
      (arg1,z) <- (do
        (n,b) <- runProcedure @'[ 'Out, 'Out, 'In ] np a
        (v,z) <- runProcedure @'[ 'Out, 'Out, 'In ] vp b
        arg1 <- pure (S n v)
        pure (arg1,z)
       )
      pure (arg1,z)
    