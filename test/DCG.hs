{-# LANGUAGE DataKinds, FlexibleContexts, NoImplicitPrelude, NoMonomorphismRestriction, TypeApplications #-}
module DCG where

import qualified Control.Monad.Logic as Logic
import Control.Monad.Logic.Moded.Prelude

data Tree = S Tree Tree | NP String String | VP String Tree deriving (Eq, Ord, Read, Show)
{- append/3
append arg1 b arg3 :- ((arg1 = [], arg3 = b); (arg1 = h0:t, h0 = h, arg3 = h1:tb, h1 = h, append t b tb)).
constraints:
~append[1]
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
      -- solution: h[1,1] h0[1,0] h1[1,2] t[1,0] tb[1,2]
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
      -- solution: arg3[] arg3[0] arg3[0,1] arg3[1] arg3[1,2] h[1,1] h0[1,0] h1[1,3] t[1,0] tb[1,4]
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
      -- solution: b[] b[0] b[0,1] b[1] b[1,4] h[1,1] h0[1,0] h1[1,2] t[1,0] tb[1,2]
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
      -- solution: arg1[] arg1[0] arg1[0,0] arg1[1] arg1[1,0] h[1,3] h0[1,1] h1[1,2] t[1,4] tb[1,2]
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
      -- solution: arg1[] arg1[0] arg1[0,0] arg1[1] arg1[1,0] b[] b[0] b[0,1] b[1] b[1,4] h[1,3] h0[1,1] h1[1,2] t[1,4] tb[1,2]
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
      -- solution: 
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
      -- solution: 
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
      -- solution: 
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
np arg1 carg3 carg4 :- ((append n carg3 b_3, append data1_1_5 b_3 b_0, data1_1_5 = " ", append d b_0 carg4, arg1 = NP d n, det d, noun n)).
constraints:
~append[0]
~det[0]
~noun[0]
~(arg1[0,4] & d[0,4])
~(b_0[0,1] & b_0[0,3])
~(b_3[0,0] & b_3[0,1])
~(d[0,3] & d[0,4])
~(d[0,3] & d[0,5])
~(d[0,4] & d[0,5])
~(data1_1_5[0,1] & data1_1_5[0,2])
~(n[0,0] & n[0,4])
~(n[0,0] & n[0,6])
~(n[0,4] & n[0,6])
(b_0[0,1] | b_0[0,3])
(b_3[0,0] | b_3[0,1])
(d[0,3] | (d[0,4] | d[0,5]))
(d[0,5] | ~d[0,5])
(data1_1_5[0,1] | data1_1_5[0,2])
(n[0,0] | (n[0,4] | n[0,6]))
(n[0,6] | ~n[0,6])
((d[0,3] & (b_0[0,3] & ~carg4[0,3])) | ((d[0,3] & (~b_0[0,3] & ~carg4[0,3])) | ((~d[0,3] & (b_0[0,3] & ~carg4[0,3])) | ((~d[0,3] & (~b_0[0,3] & carg4[0,3])) | (~d[0,3] & (~b_0[0,3] & ~carg4[0,3]))))))
((data1_1_5[0,1] & (b_3[0,1] & ~b_0[0,1])) | ((data1_1_5[0,1] & (~b_3[0,1] & ~b_0[0,1])) | ((~data1_1_5[0,1] & (b_3[0,1] & ~b_0[0,1])) | ((~data1_1_5[0,1] & (~b_3[0,1] & b_0[0,1])) | (~data1_1_5[0,1] & (~b_3[0,1] & ~b_0[0,1]))))))
((n[0,0] & (carg3[0,0] & ~b_3[0,0])) | ((n[0,0] & (~carg3[0,0] & ~b_3[0,0])) | ((~n[0,0] & (carg3[0,0] & ~b_3[0,0])) | ((~n[0,0] & (~carg3[0,0] & b_3[0,0])) | (~n[0,0] & (~carg3[0,0] & ~b_3[0,0]))))))
(arg1[] <-> arg1[0])
(arg1[0] <-> arg1[0,4])
(carg3[] <-> carg3[0])
(carg3[0] <-> carg3[0,0])
(carg4[] <-> carg4[0])
(carg4[0] <-> carg4[0,3])
(d[0,4] <-> n[0,4])
1
-}

np = rget $ (procedure @'[ 'In, 'In, 'In ] npIII) :& (procedure @'[ 'In, 'In, 'Out ] npIIO) :& (procedure @'[ 'In, 'Out, 'In ] npIOI) :& (procedure @'[ 'Out, 'In, 'In ] npOII) :& (procedure @'[ 'Out, 'In, 'Out ] npOIO) :& (procedure @'[ 'Out, 'Out, 'In ] npOOI) :& RNil
  where
    npIII = \arg1 carg3 carg4 -> Logic.once $ do
      -- solution: b_0[0,1] b_3[0,0] d[0,4] data1_1_5[0,2] n[0,4]
      -- cost: 7
      () <- (do
        data1_1_5 <- pure " "
        (NP d n) <- pure arg1
        () <- runProcedure @'[ 'In ] det d
        () <- runProcedure @'[ 'In ] noun n
        (OneTuple (b_3)) <- runProcedure @'[ 'In, 'In, 'Out ] append n carg3
        (OneTuple (b_0)) <- runProcedure @'[ 'In, 'In, 'Out ] append data1_1_5 b_3
        () <- runProcedure @'[ 'In, 'In, 'In ] append d b_0 carg4
        pure ()
       )
      pure ()
    
    npIIO = \arg1 carg3 -> do
      -- solution: b_0[0,1] b_3[0,0] carg4[] carg4[0] carg4[0,3] d[0,4] data1_1_5[0,2] n[0,4]
      -- cost: 8
      (carg4) <- (do
        data1_1_5 <- pure " "
        (NP d n) <- pure arg1
        () <- runProcedure @'[ 'In ] det d
        () <- runProcedure @'[ 'In ] noun n
        (OneTuple (b_3)) <- runProcedure @'[ 'In, 'In, 'Out ] append n carg3
        (OneTuple (b_0)) <- runProcedure @'[ 'In, 'In, 'Out ] append data1_1_5 b_3
        (OneTuple (carg4)) <- runProcedure @'[ 'In, 'In, 'Out ] append d b_0
        pure (carg4)
       )
      pure (OneTuple (carg4))
    
    npIOI = \arg1 carg4 -> do
      -- solution: b_0[0,3] b_3[0,1] carg3[] carg3[0] carg3[0,0] d[0,4] data1_1_5[0,2] n[0,4]
      -- cost: 8
      (carg3) <- (do
        data1_1_5 <- pure " "
        (NP d n) <- pure arg1
        () <- runProcedure @'[ 'In ] det d
        () <- runProcedure @'[ 'In ] noun n
        (OneTuple (b_0)) <- runProcedure @'[ 'In, 'Out, 'In ] append d carg4
        (OneTuple (b_3)) <- runProcedure @'[ 'In, 'Out, 'In ] append data1_1_5 b_0
        (OneTuple (carg3)) <- runProcedure @'[ 'In, 'Out, 'In ] append n b_3
        pure (carg3)
       )
      pure (OneTuple (carg3))
    
    npOII = \carg3 carg4 -> do
      -- solution: arg1[] arg1[0] arg1[0,4] b_0[0,1] b_3[0,0] d[0,3] data1_1_5[0,2] n[0,6]
      -- cost: 9
      (arg1) <- (do
        data1_1_5 <- pure " "
        (OneTuple (n)) <- runProcedure @'[ 'Out ] noun 
        (OneTuple (b_3)) <- runProcedure @'[ 'In, 'In, 'Out ] append n carg3
        (OneTuple (b_0)) <- runProcedure @'[ 'In, 'In, 'Out ] append data1_1_5 b_3
        (OneTuple (d)) <- runProcedure @'[ 'Out, 'In, 'In ] append b_0 carg4
        arg1 <- pure (NP d n)
        () <- runProcedure @'[ 'In ] det d
        pure (arg1)
       )
      pure (OneTuple (arg1))
    
    npOIO = \carg3 -> do
      -- solution: arg1[] arg1[0] arg1[0,4] b_0[0,1] b_3[0,0] carg4[] carg4[0] carg4[0,3] d[0,5] data1_1_5[0,2] n[0,6]
      -- cost: 10
      (arg1,carg4) <- (do
        data1_1_5 <- pure " "
        (OneTuple (d)) <- runProcedure @'[ 'Out ] det 
        (OneTuple (n)) <- runProcedure @'[ 'Out ] noun 
        arg1 <- pure (NP d n)
        (OneTuple (b_3)) <- runProcedure @'[ 'In, 'In, 'Out ] append n carg3
        (OneTuple (b_0)) <- runProcedure @'[ 'In, 'In, 'Out ] append data1_1_5 b_3
        (OneTuple (carg4)) <- runProcedure @'[ 'In, 'In, 'Out ] append d b_0
        pure (arg1,carg4)
       )
      pure (arg1,carg4)
    
    npOOI = \carg4 -> do
      -- solution: arg1[] arg1[0] arg1[0,4] b_0[0,3] b_3[0,1] carg3[] carg3[0] carg3[0,0] d[0,3] data1_1_5[0,2] n[0,0]
      -- cost: 10
      (arg1,carg3) <- (do
        data1_1_5 <- pure " "
        (d,b_0) <- runProcedure @'[ 'Out, 'Out, 'In ] append carg4
        () <- runProcedure @'[ 'In ] det d
        (OneTuple (b_3)) <- runProcedure @'[ 'In, 'Out, 'In ] append data1_1_5 b_0
        (n,carg3) <- runProcedure @'[ 'Out, 'Out, 'In ] append b_3
        arg1 <- pure (NP d n)
        () <- runProcedure @'[ 'In ] noun n
        pure (arg1,carg3)
       )
      pure (arg1,carg3)
    
{- vp/3
vp arg1 carg3 carg4 :- ((np n carg3 b_3, append data1_1_5 b_3 b_0, data1_1_5 = " ", append v b_0 carg4, arg1 = VP v n, verb v)).
constraints:
~append[0]
~np[0]
~verb[0]
~(arg1[0,4] & v[0,4])
~(b_0[0,1] & b_0[0,3])
~(b_3[0,0] & b_3[0,1])
~(data1_1_5[0,1] & data1_1_5[0,2])
~(n[0,0] & n[0,4])
~(v[0,3] & v[0,4])
~(v[0,3] & v[0,5])
~(v[0,4] & v[0,5])
(b_0[0,1] | b_0[0,3])
(b_3[0,0] | b_3[0,1])
(data1_1_5[0,1] | data1_1_5[0,2])
(n[0,0] | n[0,4])
(v[0,3] | (v[0,4] | v[0,5]))
(v[0,5] | ~v[0,5])
((data1_1_5[0,1] & (b_3[0,1] & ~b_0[0,1])) | ((data1_1_5[0,1] & (~b_3[0,1] & ~b_0[0,1])) | ((~data1_1_5[0,1] & (b_3[0,1] & ~b_0[0,1])) | ((~data1_1_5[0,1] & (~b_3[0,1] & b_0[0,1])) | (~data1_1_5[0,1] & (~b_3[0,1] & ~b_0[0,1]))))))
((n[0,0] & (carg3[0,0] & ~b_3[0,0])) | ((n[0,0] & (~carg3[0,0] & b_3[0,0])) | ((n[0,0] & (~carg3[0,0] & ~b_3[0,0])) | ((~n[0,0] & (carg3[0,0] & ~b_3[0,0])) | ((~n[0,0] & (~carg3[0,0] & b_3[0,0])) | (~n[0,0] & (~carg3[0,0] & ~b_3[0,0])))))))
((v[0,3] & (b_0[0,3] & ~carg4[0,3])) | ((v[0,3] & (~b_0[0,3] & ~carg4[0,3])) | ((~v[0,3] & (b_0[0,3] & ~carg4[0,3])) | ((~v[0,3] & (~b_0[0,3] & carg4[0,3])) | (~v[0,3] & (~b_0[0,3] & ~carg4[0,3]))))))
(arg1[] <-> arg1[0])
(arg1[0] <-> arg1[0,4])
(carg3[] <-> carg3[0])
(carg3[0] <-> carg3[0,0])
(carg4[] <-> carg4[0])
(carg4[0] <-> carg4[0,3])
(v[0,4] <-> n[0,4])
1
-}

vp = rget $ (procedure @'[ 'In, 'In, 'In ] vpIII) :& (procedure @'[ 'In, 'In, 'Out ] vpIIO) :& (procedure @'[ 'In, 'Out, 'In ] vpIOI) :& (procedure @'[ 'Out, 'In, 'In ] vpOII) :& (procedure @'[ 'Out, 'In, 'Out ] vpOIO) :& (procedure @'[ 'Out, 'Out, 'In ] vpOOI) :& RNil
  where
    vpIII = \arg1 carg3 carg4 -> Logic.once $ do
      -- solution: b_0[0,1] b_3[0,0] data1_1_5[0,2] n[0,4] v[0,4]
      -- cost: 6
      () <- (do
        data1_1_5 <- pure " "
        (VP v n) <- pure arg1
        () <- runProcedure @'[ 'In ] verb v
        (OneTuple (b_3)) <- runProcedure @'[ 'In, 'In, 'Out ] np n carg3
        (OneTuple (b_0)) <- runProcedure @'[ 'In, 'In, 'Out ] append data1_1_5 b_3
        () <- runProcedure @'[ 'In, 'In, 'In ] append v b_0 carg4
        pure ()
       )
      pure ()
    
    vpIIO = \arg1 carg3 -> do
      -- solution: b_0[0,1] b_3[0,0] carg4[] carg4[0] carg4[0,3] data1_1_5[0,2] n[0,4] v[0,4]
      -- cost: 7
      (carg4) <- (do
        data1_1_5 <- pure " "
        (VP v n) <- pure arg1
        () <- runProcedure @'[ 'In ] verb v
        (OneTuple (b_3)) <- runProcedure @'[ 'In, 'In, 'Out ] np n carg3
        (OneTuple (b_0)) <- runProcedure @'[ 'In, 'In, 'Out ] append data1_1_5 b_3
        (OneTuple (carg4)) <- runProcedure @'[ 'In, 'In, 'Out ] append v b_0
        pure (carg4)
       )
      pure (OneTuple (carg4))
    
    vpIOI = \arg1 carg4 -> do
      -- solution: b_0[0,3] b_3[0,1] carg3[] carg3[0] carg3[0,0] data1_1_5[0,2] n[0,4] v[0,4]
      -- cost: 7
      (carg3) <- (do
        data1_1_5 <- pure " "
        (VP v n) <- pure arg1
        () <- runProcedure @'[ 'In ] verb v
        (OneTuple (b_0)) <- runProcedure @'[ 'In, 'Out, 'In ] append v carg4
        (OneTuple (b_3)) <- runProcedure @'[ 'In, 'Out, 'In ] append data1_1_5 b_0
        (OneTuple (carg3)) <- runProcedure @'[ 'In, 'Out, 'In ] np n b_3
        pure (carg3)
       )
      pure (OneTuple (carg3))
    
    vpOII = \carg3 carg4 -> do
      -- solution: arg1[] arg1[0] arg1[0,4] b_0[0,1] b_3[0,0] data1_1_5[0,2] n[0,0] v[0,3]
      -- cost: 8
      (arg1) <- (do
        data1_1_5 <- pure " "
        (n,b_3) <- runProcedure @'[ 'Out, 'In, 'Out ] np carg3
        (OneTuple (b_0)) <- runProcedure @'[ 'In, 'In, 'Out ] append data1_1_5 b_3
        (OneTuple (v)) <- runProcedure @'[ 'Out, 'In, 'In ] append b_0 carg4
        arg1 <- pure (VP v n)
        () <- runProcedure @'[ 'In ] verb v
        pure (arg1)
       )
      pure (OneTuple (arg1))
    
    vpOIO = \carg3 -> do
      -- solution: arg1[] arg1[0] arg1[0,4] b_0[0,1] b_3[0,0] carg4[] carg4[0] carg4[0,3] data1_1_5[0,2] n[0,0] v[0,5]
      -- cost: 9
      (arg1,carg4) <- (do
        data1_1_5 <- pure " "
        (OneTuple (v)) <- runProcedure @'[ 'Out ] verb 
        (n,b_3) <- runProcedure @'[ 'Out, 'In, 'Out ] np carg3
        arg1 <- pure (VP v n)
        (OneTuple (b_0)) <- runProcedure @'[ 'In, 'In, 'Out ] append data1_1_5 b_3
        (OneTuple (carg4)) <- runProcedure @'[ 'In, 'In, 'Out ] append v b_0
        pure (arg1,carg4)
       )
      pure (arg1,carg4)
    
    vpOOI = \carg4 -> do
      -- solution: arg1[] arg1[0] arg1[0,4] b_0[0,3] b_3[0,1] carg3[] carg3[0] carg3[0,0] data1_1_5[0,2] n[0,0] v[0,3]
      -- cost: 9
      (arg1,carg3) <- (do
        data1_1_5 <- pure " "
        (v,b_0) <- runProcedure @'[ 'Out, 'Out, 'In ] append carg4
        () <- runProcedure @'[ 'In ] verb v
        (OneTuple (b_3)) <- runProcedure @'[ 'In, 'Out, 'In ] append data1_1_5 b_0
        (n,carg3) <- runProcedure @'[ 'Out, 'Out, 'In ] np b_3
        arg1 <- pure (VP v n)
        pure (arg1,carg3)
       )
      pure (arg1,carg3)
    
{- sentence/3
sentence arg1 carg3 carg4 :- ((vp v carg3 b_3, append data1_1_5 b_3 b_0, data1_1_5 = " ", np n b_0 carg4, arg1 = S n v)).
constraints:
~append[0]
~np[0]
~vp[0]
~(arg1[0,4] & n[0,4])
~(b_0[0,1] & b_0[0,3])
~(b_3[0,0] & b_3[0,1])
~(data1_1_5[0,1] & data1_1_5[0,2])
~(n[0,3] & n[0,4])
~(v[0,0] & v[0,4])
(b_0[0,1] | b_0[0,3])
(b_3[0,0] | b_3[0,1])
(data1_1_5[0,1] | data1_1_5[0,2])
(n[0,3] | n[0,4])
(v[0,0] | v[0,4])
((data1_1_5[0,1] & (b_3[0,1] & ~b_0[0,1])) | ((data1_1_5[0,1] & (~b_3[0,1] & ~b_0[0,1])) | ((~data1_1_5[0,1] & (b_3[0,1] & ~b_0[0,1])) | ((~data1_1_5[0,1] & (~b_3[0,1] & b_0[0,1])) | (~data1_1_5[0,1] & (~b_3[0,1] & ~b_0[0,1]))))))
((n[0,3] & (b_0[0,3] & ~carg4[0,3])) | ((n[0,3] & (~b_0[0,3] & carg4[0,3])) | ((n[0,3] & (~b_0[0,3] & ~carg4[0,3])) | ((~n[0,3] & (b_0[0,3] & ~carg4[0,3])) | ((~n[0,3] & (~b_0[0,3] & carg4[0,3])) | (~n[0,3] & (~b_0[0,3] & ~carg4[0,3])))))))
((v[0,0] & (carg3[0,0] & ~b_3[0,0])) | ((v[0,0] & (~carg3[0,0] & b_3[0,0])) | ((v[0,0] & (~carg3[0,0] & ~b_3[0,0])) | ((~v[0,0] & (carg3[0,0] & ~b_3[0,0])) | ((~v[0,0] & (~carg3[0,0] & b_3[0,0])) | (~v[0,0] & (~carg3[0,0] & ~b_3[0,0])))))))
(arg1[] <-> arg1[0])
(arg1[0] <-> arg1[0,4])
(carg3[] <-> carg3[0])
(carg3[0] <-> carg3[0,0])
(carg4[] <-> carg4[0])
(carg4[0] <-> carg4[0,3])
(n[0,4] <-> v[0,4])
1
-}

sentence = rget $ (procedure @'[ 'In, 'In, 'In ] sentenceIII) :& (procedure @'[ 'In, 'In, 'Out ] sentenceIIO) :& (procedure @'[ 'In, 'Out, 'In ] sentenceIOI) :& (procedure @'[ 'Out, 'In, 'In ] sentenceOII) :& (procedure @'[ 'Out, 'In, 'Out ] sentenceOIO) :& (procedure @'[ 'Out, 'Out, 'In ] sentenceOOI) :& RNil
  where
    sentenceIII = \arg1 carg3 carg4 -> Logic.once $ do
      -- solution: b_0[0,1] b_3[0,0] data1_1_5[0,2] n[0,4] v[0,4]
      -- cost: 5
      () <- (do
        data1_1_5 <- pure " "
        (S n v) <- pure arg1
        (OneTuple (b_3)) <- runProcedure @'[ 'In, 'In, 'Out ] vp v carg3
        (OneTuple (b_0)) <- runProcedure @'[ 'In, 'In, 'Out ] append data1_1_5 b_3
        () <- runProcedure @'[ 'In, 'In, 'In ] np n b_0 carg4
        pure ()
       )
      pure ()
    
    sentenceIIO = \arg1 carg3 -> do
      -- solution: b_0[0,1] b_3[0,0] carg4[] carg4[0] carg4[0,3] data1_1_5[0,2] n[0,4] v[0,4]
      -- cost: 6
      (carg4) <- (do
        data1_1_5 <- pure " "
        (S n v) <- pure arg1
        (OneTuple (b_3)) <- runProcedure @'[ 'In, 'In, 'Out ] vp v carg3
        (OneTuple (b_0)) <- runProcedure @'[ 'In, 'In, 'Out ] append data1_1_5 b_3
        (OneTuple (carg4)) <- runProcedure @'[ 'In, 'In, 'Out ] np n b_0
        pure (carg4)
       )
      pure (OneTuple (carg4))
    
    sentenceIOI = \arg1 carg4 -> do
      -- solution: b_0[0,3] b_3[0,1] carg3[] carg3[0] carg3[0,0] data1_1_5[0,2] n[0,4] v[0,4]
      -- cost: 6
      (carg3) <- (do
        data1_1_5 <- pure " "
        (S n v) <- pure arg1
        (OneTuple (b_0)) <- runProcedure @'[ 'In, 'Out, 'In ] np n carg4
        (OneTuple (b_3)) <- runProcedure @'[ 'In, 'Out, 'In ] append data1_1_5 b_0
        (OneTuple (carg3)) <- runProcedure @'[ 'In, 'Out, 'In ] vp v b_3
        pure (carg3)
       )
      pure (OneTuple (carg3))
    
    sentenceOII = \carg3 carg4 -> do
      -- solution: arg1[] arg1[0] arg1[0,4] b_0[0,1] b_3[0,0] data1_1_5[0,2] n[0,3] v[0,0]
      -- cost: 7
      (arg1) <- (do
        data1_1_5 <- pure " "
        (v,b_3) <- runProcedure @'[ 'Out, 'In, 'Out ] vp carg3
        (OneTuple (b_0)) <- runProcedure @'[ 'In, 'In, 'Out ] append data1_1_5 b_3
        (OneTuple (n)) <- runProcedure @'[ 'Out, 'In, 'In ] np b_0 carg4
        arg1 <- pure (S n v)
        pure (arg1)
       )
      pure (OneTuple (arg1))
    
    sentenceOIO = \carg3 -> do
      -- solution: arg1[] arg1[0] arg1[0,4] b_0[0,1] b_3[0,0] carg4[] carg4[0] carg4[0,3] data1_1_5[0,2] n[0,3] v[0,0]
      -- cost: 8
      (arg1,carg4) <- (do
        data1_1_5 <- pure " "
        (v,b_3) <- runProcedure @'[ 'Out, 'In, 'Out ] vp carg3
        (OneTuple (b_0)) <- runProcedure @'[ 'In, 'In, 'Out ] append data1_1_5 b_3
        (n,carg4) <- runProcedure @'[ 'Out, 'In, 'Out ] np b_0
        arg1 <- pure (S n v)
        pure (arg1,carg4)
       )
      pure (arg1,carg4)
    
    sentenceOOI = \carg4 -> do
      -- solution: arg1[] arg1[0] arg1[0,4] b_0[0,3] b_3[0,1] carg3[] carg3[0] carg3[0,0] data1_1_5[0,2] n[0,3] v[0,0]
      -- cost: 8
      (arg1,carg3) <- (do
        data1_1_5 <- pure " "
        (n,b_0) <- runProcedure @'[ 'Out, 'Out, 'In ] np carg4
        (OneTuple (b_3)) <- runProcedure @'[ 'In, 'Out, 'In ] append data1_1_5 b_0
        (v,carg3) <- runProcedure @'[ 'Out, 'Out, 'In ] vp b_3
        arg1 <- pure (S n v)
        pure (arg1,carg3)
       )
      pure (arg1,carg3)
    