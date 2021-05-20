{-# LANGUAGE DataKinds, FlexibleContexts, NoImplicitPrelude, NoMonomorphismRestriction, TypeApplications #-}
module Kiselyov where

import qualified Control.Monad.Logic as Logic
import Control.Monad.Logic.Moded.Prelude

{- nat/1
nat arg1 :- ((arg1 = 0); (nat n, succ n n', arg1 = n')).
constraints:
~nat[1]
~succ[1]
~(arg1[1,2] & n'[1,2])
~(n[1,0] & n[1,1])
~(n'[1,1] & n'[1,2])
(n[1,0] | n[1,1])
(n'[1,1] | n'[1,2])
((n[1,1] & ~n'[1,1]) | ((~n[1,1] & n'[1,1]) | (~n[1,1] & ~n'[1,1])))
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg1[0] <-> arg1[0,0])
(arg1[1] <-> arg1[1,2])
(n[1,0] <-> arg1[])
1
-}

nat = rget $ (procedure @'[ 'In ] natI) :& (procedure @'[ 'Out ] natO) :& RNil
  where
    natI = \arg1 -> Logic.once $ do
      -- solution: n[1,1] n'[1,2]
      -- cost: 3
      () <- (do
        guard $ arg1 == 0
        pure ()
       ) <|> (do
        n' <- pure arg1
        (OneTuple (n)) <- runProcedure @'[ 'Out, 'In ] succ n'
        () <- natI n
        pure ()
       )
      pure ()
    
    natO = do
      -- solution: arg1[] arg1[0] arg1[0,0] arg1[1] arg1[1,2] n[1,0] n'[1,1]
      -- cost: 4
      (arg1) <- (do
        arg1 <- pure 0
        pure (arg1)
       ) <|> (do
        (OneTuple (n)) <- natO 
        (OneTuple (n')) <- runProcedure @'[ 'In, 'Out ] succ n
        arg1 <- pure n'
        pure (arg1)
       )
      pure (OneTuple (arg1))
    
{- elem/2
elem arg1 arg2 :- ((arg2 = x:_, arg1 = x); (arg2 = _:xs, elem x xs, arg1 = x)).
constraints:
x[0,0]
xs[1,0]
~arg2[1,0]
~elem[1]
~(arg1[0,1] & x[0,1])
~(arg1[1,2] & x[1,2])
~(arg2[0,0] & x[0,0])
~(x[0,0] & x[0,1])
~(x[1,1] & x[1,2])
~(xs[1,0] & xs[1,1])
(x[0,0] | x[0,1])
(x[1,1] | x[1,2])
(xs[1,0] | xs[1,1])
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg1[0] <-> arg1[0,1])
(arg1[1] <-> arg1[1,2])
(arg2[] <-> arg2[0])
(arg2[] <-> arg2[1])
(arg2[0] <-> arg2[0,0])
(arg2[1] <-> arg2[1,0])
(x[1,1] <-> arg1[])
(xs[1,1] <-> arg2[])
1
-}

elem = rget $ (procedure @'[ 'In, 'In ] elemII) :& (procedure @'[ 'Out, 'In ] elemOI) :& RNil
  where
    elemII = \arg1 arg2 -> Logic.once $ do
      -- solution: x[0,0] x[1,2] xs[1,0]
      -- cost: 1
      () <- (do
        (x:_) <- pure arg2
        guard $ arg1 == x
        pure ()
       ) <|> (do
        x <- pure arg1
        (_:xs) <- pure arg2
        () <- elemII x xs
        pure ()
       )
      pure ()
    
    elemOI = \arg2 -> do
      -- solution: arg1[] arg1[0] arg1[0,1] arg1[1] arg1[1,2] x[0,0] x[1,1] xs[1,0]
      -- cost: 2
      (arg1) <- (do
        (x:_) <- pure arg2
        arg1 <- pure x
        pure (arg1)
       ) <|> (do
        (_:xs) <- pure arg2
        (OneTuple (x)) <- elemOI xs
        arg1 <- pure x
        pure (arg1)
       )
      pure (OneTuple (arg1))
    
{- insert/3
insert arg1 arg2 arg3 :- ((arg3 = e:l, arg1 = e, arg2 = l); (arg2 = h:t, arg3 = h0:t', h0 = h, insert e t t', arg1 = e)).
constraints:
~insert[1]
~(arg1[0,1] & e[0,1])
~(arg1[1,4] & e[1,4])
~(arg2[0,2] & l[0,2])
~(arg2[1,0] & h[1,0])
~(arg3[0,0] & e[0,0])
~(arg3[1,1] & h0[1,1])
~(e[0,0] & e[0,1])
~(e[1,3] & e[1,4])
~(h[1,0] & h[1,2])
~(h0[1,1] & h0[1,2])
~(h0[1,2] & h[1,2])
~(l[0,0] & l[0,2])
~(t[1,0] & t[1,3])
~(t'[1,1] & t'[1,3])
(e[0,0] | e[0,1])
(e[1,3] | e[1,4])
(h[1,0] | h[1,2])
(h0[1,1] | h0[1,2])
(l[0,0] | l[0,2])
(t[1,0] | t[1,3])
(t'[1,1] | t'[1,3])
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg1[0] <-> arg1[0,1])
(arg1[1] <-> arg1[1,4])
(arg2[] <-> arg2[0])
(arg2[] <-> arg2[1])
(arg2[0] <-> arg2[0,2])
(arg2[1] <-> arg2[1,0])
(arg3[] <-> arg3[0])
(arg3[] <-> arg3[1])
(arg3[0] <-> arg3[0,0])
(arg3[1] <-> arg3[1,1])
(e[0,0] <-> l[0,0])
(e[1,3] <-> arg1[])
(h[1,0] <-> t[1,0])
(h0[1,1] <-> t'[1,1])
(t[1,3] <-> arg2[])
(t'[1,3] <-> arg3[])
1
-}

insert = rget $ (procedure @'[ 'In, 'In, 'In ] insertIII) :& (procedure @'[ 'In, 'In, 'Out ] insertIIO) :& (procedure @'[ 'In, 'Out, 'In ] insertIOI) :& (procedure @'[ 'Out, 'In, 'In ] insertOII) :& (procedure @'[ 'Out, 'Out, 'In ] insertOOI) :& RNil
  where
    insertIII = \arg1 arg2 arg3 -> Logic.once $ do
      -- solution: e[0,0] e[1,4] h[1,0] h0[1,1] l[0,0] t[1,0] t'[1,1]
      -- cost: 1
      () <- (do
        (e:l) <- pure arg3
        guard $ arg1 == e
        guard $ arg2 == l
        pure ()
       ) <|> (do
        e <- pure arg1
        (h:t) <- pure arg2
        (h0:t') <- pure arg3
        guard $ h0 == h
        () <- insertIII e t t'
        pure ()
       )
      pure ()
    
    insertIIO = \arg1 arg2 -> do
      -- solution: arg3[] arg3[0] arg3[0,0] arg3[1] arg3[1,1] e[0,1] e[1,4] h[1,0] h0[1,2] l[0,2] t[1,0] t'[1,3]
      -- cost: 2
      (arg3) <- (do
        e <- pure arg1
        l <- pure arg2
        arg3 <- pure (e:l)
        pure (arg3)
       ) <|> (do
        e <- pure arg1
        (h:t) <- pure arg2
        h0 <- pure h
        (OneTuple (t')) <- insertIIO e t
        arg3 <- pure (h0:t')
        pure (arg3)
       )
      pure (OneTuple (arg3))
    
    insertIOI = \arg1 arg3 -> do
      -- solution: arg2[] arg2[0] arg2[0,2] arg2[1] arg2[1,0] e[0,0] e[1,4] h[1,2] h0[1,1] l[0,0] t[1,3] t'[1,1]
      -- cost: 2
      (arg2) <- (do
        (e:l) <- pure arg3
        guard $ arg1 == e
        arg2 <- pure l
        pure (arg2)
       ) <|> (do
        e <- pure arg1
        (h0:t') <- pure arg3
        h <- pure h0
        (OneTuple (t)) <- insertIOI e t'
        arg2 <- pure (h:t)
        pure (arg2)
       )
      pure (OneTuple (arg2))
    
    insertOII = \arg2 arg3 -> do
      -- solution: arg1[] arg1[0] arg1[0,1] arg1[1] arg1[1,4] e[0,0] e[1,3] h[1,0] h0[1,1] l[0,0] t[1,0] t'[1,1]
      -- cost: 2
      (arg1) <- (do
        (e:l) <- pure arg3
        arg1 <- pure e
        guard $ arg2 == l
        pure (arg1)
       ) <|> (do
        (h:t) <- pure arg2
        (h0:t') <- pure arg3
        guard $ h0 == h
        (OneTuple (e)) <- insertOII t t'
        arg1 <- pure e
        pure (arg1)
       )
      pure (OneTuple (arg1))
    
    insertOOI = \arg3 -> do
      -- solution: arg1[] arg1[0] arg1[0,1] arg1[1] arg1[1,4] arg2[] arg2[0] arg2[0,2] arg2[1] arg2[1,0] e[0,0] e[1,3] h[1,2] h0[1,1] l[0,0] t[1,3] t'[1,1]
      -- cost: 3
      (arg1,arg2) <- (do
        (e:l) <- pure arg3
        arg1 <- pure e
        arg2 <- pure l
        pure (arg1,arg2)
       ) <|> (do
        (h0:t') <- pure arg3
        h <- pure h0
        (e,t) <- insertOOI t'
        arg1 <- pure e
        arg2 <- pure (h:t)
        pure (arg1,arg2)
       )
      pure (arg1,arg2)
    
{- permute/2
permute arg1 arg2 :- ((arg1 = [], arg2 = []); (arg1 = h:t, permute t t', insert h t' r, arg2 = r)).
constraints:
~insert[1]
~permute[1]
~(arg1[1,0] & h[1,0])
~(arg2[1,3] & r[1,3])
~(h[1,0] & h[1,2])
~(r[1,2] & r[1,3])
~(t[1,0] & t[1,1])
~(t'[1,1] & t'[1,2])
(h[1,0] | h[1,2])
(r[1,2] | r[1,3])
(t[1,0] | t[1,1])
(t'[1,1] | t'[1,2])
((h[1,2] & (t'[1,2] & ~r[1,2])) | ((h[1,2] & (~t'[1,2] & ~r[1,2])) | ((~h[1,2] & (t'[1,2] & ~r[1,2])) | ((~h[1,2] & (~t'[1,2] & r[1,2])) | (~h[1,2] & (~t'[1,2] & ~r[1,2]))))))
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg1[0] <-> arg1[0,0])
(arg1[1] <-> arg1[1,0])
(arg2[] <-> arg2[0])
(arg2[] <-> arg2[1])
(arg2[0] <-> arg2[0,1])
(arg2[1] <-> arg2[1,3])
(h[1,0] <-> t[1,0])
(t[1,1] <-> arg1[])
(t'[1,1] <-> arg2[])
1
-}

permute = rget $ (procedure @'[ 'In, 'In ] permuteII) :& (procedure @'[ 'In, 'Out ] permuteIO) :& (procedure @'[ 'Out, 'In ] permuteOI) :& RNil
  where
    permuteII = \arg1 arg2 -> Logic.once $ do
      -- solution: h[1,0] r[1,3] t[1,0] t'[1,2]
      -- cost: 3
      () <- (do
        guard $ arg1 == []
        guard $ arg2 == []
        pure ()
       ) <|> (do
        (h:t) <- pure arg1
        r <- pure arg2
        (OneTuple (t')) <- runProcedure @'[ 'In, 'Out, 'In ] insert h r
        () <- permuteII t t'
        pure ()
       )
      pure ()
    
    permuteIO = \arg1 -> do
      -- solution: arg2[] arg2[0] arg2[0,1] arg2[1] arg2[1,3] h[1,0] r[1,2] t[1,0] t'[1,1]
      -- cost: 4
      (arg2) <- (do
        guard $ arg1 == []
        arg2 <- pure []
        pure (arg2)
       ) <|> (do
        (h:t) <- pure arg1
        (OneTuple (t')) <- permuteIO t
        (OneTuple (r)) <- runProcedure @'[ 'In, 'In, 'Out ] insert h t'
        arg2 <- pure r
        pure (arg2)
       )
      pure (OneTuple (arg2))
    
    permuteOI = \arg2 -> do
      -- solution: arg1[] arg1[0] arg1[0,0] arg1[1] arg1[1,0] h[1,2] r[1,3] t[1,1] t'[1,2]
      -- cost: 5
      (arg1) <- (do
        arg1 <- pure []
        guard $ arg2 == []
        pure (arg1)
       ) <|> (do
        r <- pure arg2
        (h,t') <- runProcedure @'[ 'Out, 'Out, 'In ] insert r
        (OneTuple (t)) <- permuteOI t'
        arg1 <- pure (h:t)
        pure (arg1)
       )
      pure (OneTuple (arg1))
    
{- sorted/1
sorted arg1 :- ((arg1 = []); (arg1 = _:[]); (arg1 = a:b:r, (<=) a b, sorted data0, data0 = b0:r0, b0 = b, r0 = r)).
constraints:
~(<=)[2]
~arg1[1,0]
~sorted[2]
~(a[2,0] & a[2,1])
~(arg1[2,0] & a[2,0])
~(b[2,0] & b[2,1])
~(b[2,0] & b[2,4])
~(b[2,1] & b[2,4])
~(b0[2,3] & b0[2,4])
~(b0[2,4] & b[2,4])
~(data0[2,2] & data0[2,3])
~(data0[2,3] & b0[2,3])
~(r[2,0] & r[2,5])
~(r0[2,3] & r0[2,5])
~(r0[2,5] & r[2,5])
(~a[2,1] & ~b[2,1])
(a[2,0] | a[2,1])
(b[2,0] | (b[2,1] | b[2,4]))
(b0[2,3] | b0[2,4])
(data0[2,2] | data0[2,3])
(r[2,0] | r[2,5])
(r0[2,3] | r0[2,5])
(a[2,0] <-> b[2,0])
(a[2,0] <-> r[2,0])
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg1[] <-> arg1[2])
(arg1[0] <-> arg1[0,0])
(arg1[1] <-> arg1[1,0])
(arg1[2] <-> arg1[2,0])
(b0[2,3] <-> r0[2,3])
(data0[2,2] <-> arg1[])
1
-}

sorted = rget $ (procedure @'[ 'In ] sortedI) :& RNil
  where
    sortedI = \arg1 -> Logic.once $ do
      -- solution: a[2,0] b[2,0] b0[2,4] data0[2,3] r[2,0] r0[2,5]
      -- cost: 2
      () <- (do
        guard $ arg1 == []
        pure ()
       ) <|> (do
        (_:[]) <- pure arg1
        pure ()
       ) <|> (do
        (a:b:r) <- pure arg1
        b0 <- pure b
        r0 <- pure r
        data0 <- pure (b0:r0)
        guard $ (<=) a b
        () <- sortedI data0
        pure ()
       )
      pure ()
    
{- suffix/2
suffix arg1 arg2 :- ((arg1 = l, arg2 = l); (arg1 = _:t, suffix t r, arg2 = r)).
constraints:
t[1,0]
~arg1[1,0]
~suffix[1]
~(arg1[0,0] & l[0,0])
~(arg2[0,1] & l[0,1])
~(arg2[1,2] & r[1,2])
~(l[0,0] & l[0,1])
~(r[1,1] & r[1,2])
~(t[1,0] & t[1,1])
(l[0,0] | l[0,1])
(r[1,1] | r[1,2])
(t[1,0] | t[1,1])
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg1[0] <-> arg1[0,0])
(arg1[1] <-> arg1[1,0])
(arg2[] <-> arg2[0])
(arg2[] <-> arg2[1])
(arg2[0] <-> arg2[0,1])
(arg2[1] <-> arg2[1,2])
(r[1,1] <-> arg2[])
(t[1,1] <-> arg1[])
1
-}

suffix = rget $ (procedure @'[ 'In, 'In ] suffixII) :& (procedure @'[ 'In, 'Out ] suffixIO) :& RNil
  where
    suffixII = \arg1 arg2 -> Logic.once $ do
      -- solution: l[0,0] r[1,2] t[1,0]
      -- cost: 1
      () <- (do
        l <- pure arg1
        guard $ arg2 == l
        pure ()
       ) <|> (do
        (_:t) <- pure arg1
        r <- pure arg2
        () <- suffixII t r
        pure ()
       )
      pure ()
    
    suffixIO = \arg1 -> do
      -- solution: arg2[] arg2[0] arg2[0,1] arg2[1] arg2[1,2] l[0,0] r[1,1] t[1,0]
      -- cost: 2
      (arg2) <- (do
        l <- pure arg1
        arg2 <- pure l
        pure (arg2)
       ) <|> (do
        (_:t) <- pure arg1
        (OneTuple (r)) <- suffixIO t
        arg2 <- pure r
        pure (arg2)
       )
      pure (OneTuple (arg2))
    
{- prefix/2
prefix arg1 arg2 :- ((arg2 = []); (arg1 = h:t, arg2 = h0:t', h0 = h, prefix t t')).
constraints:
~arg1[]
~prefix[1]
~(arg1[1,0] & h[1,0])
~(arg2[1,1] & h0[1,1])
~(h[1,0] & h[1,2])
~(h0[1,1] & h0[1,2])
~(h0[1,2] & h[1,2])
~(t[1,0] & t[1,3])
~(t'[1,1] & t'[1,3])
(h[1,0] | h[1,2])
(h0[1,1] | h0[1,2])
(t[1,0] | t[1,3])
(t'[1,1] | t'[1,3])
(arg1[] <-> arg1[1])
(arg1[1] <-> arg1[1,0])
(arg2[] <-> arg2[0])
(arg2[] <-> arg2[1])
(arg2[0] <-> arg2[0,0])
(arg2[1] <-> arg2[1,1])
(h[1,0] <-> t[1,0])
(h0[1,1] <-> t'[1,1])
(t[1,3] <-> arg1[])
(t'[1,3] <-> arg2[])
1
-}

prefix = rget $ (procedure @'[ 'In, 'In ] prefixII) :& (procedure @'[ 'In, 'Out ] prefixIO) :& RNil
  where
    prefixII = \arg1 arg2 -> Logic.once $ do
      -- solution: h[1,0] h0[1,1] t[1,0] t'[1,1]
      -- cost: 1
      () <- (do
        guard $ arg2 == []
        pure ()
       ) <|> (do
        (h:t) <- pure arg1
        (h0:t') <- pure arg2
        guard $ h0 == h
        () <- prefixII t t'
        pure ()
       )
      pure ()
    
    prefixIO = \arg1 -> do
      -- solution: arg2[] arg2[0] arg2[0,0] arg2[1] arg2[1,1] h[1,0] h0[1,2] t[1,0] t'[1,3]
      -- cost: 2
      (arg2) <- (do
        arg2 <- pure []
        pure (arg2)
       ) <|> (do
        (h:t) <- pure arg1
        h0 <- pure h
        (OneTuple (t')) <- prefixIO t
        arg2 <- pure (h0:t')
        pure (arg2)
       )
      pure (OneTuple (arg2))
    
{- length/2
length arg1 arg2 :- ((arg1 = [], arg2 = 0); (arg1 = _:t, length t n, succ n n', arg2 = n')).
constraints:
t[1,0]
~arg1[1,0]
~length[1]
~succ[1]
~(arg2[1,3] & n'[1,3])
~(n[1,1] & n[1,2])
~(n'[1,2] & n'[1,3])
~(t[1,0] & t[1,1])
(n[1,1] | n[1,2])
(n'[1,2] | n'[1,3])
(t[1,0] | t[1,1])
((n[1,2] & ~n'[1,2]) | ((~n[1,2] & n'[1,2]) | (~n[1,2] & ~n'[1,2])))
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg1[0] <-> arg1[0,0])
(arg1[1] <-> arg1[1,0])
(arg2[] <-> arg2[0])
(arg2[] <-> arg2[1])
(arg2[0] <-> arg2[0,1])
(arg2[1] <-> arg2[1,3])
(n[1,1] <-> arg2[])
(t[1,1] <-> arg1[])
1
-}

length = rget $ (procedure @'[ 'In, 'In ] lengthII) :& (procedure @'[ 'In, 'Out ] lengthIO) :& RNil
  where
    lengthII = \arg1 arg2 -> Logic.once $ do
      -- solution: n[1,2] n'[1,3] t[1,0]
      -- cost: 3
      () <- (do
        guard $ arg1 == []
        guard $ arg2 == 0
        pure ()
       ) <|> (do
        (_:t) <- pure arg1
        n' <- pure arg2
        (OneTuple (n)) <- runProcedure @'[ 'Out, 'In ] succ n'
        () <- lengthII t n
        pure ()
       )
      pure ()
    
    lengthIO = \arg1 -> do
      -- solution: arg2[] arg2[0] arg2[0,1] arg2[1] arg2[1,3] n[1,1] n'[1,2] t[1,0]
      -- cost: 4
      (arg2) <- (do
        guard $ arg1 == []
        arg2 <- pure 0
        pure (arg2)
       ) <|> (do
        (_:t) <- pure arg1
        (OneTuple (n)) <- lengthIO t
        (OneTuple (n')) <- runProcedure @'[ 'In, 'Out ] succ n
        arg2 <- pure n'
        pure (arg2)
       )
      pure (OneTuple (arg2))
    
{- id/2
id arg1 arg2 :- ((arg1 = x, arg2 = x)).
constraints:
~(arg1[0,0] & x[0,0])
~(arg2[0,1] & x[0,1])
~(x[0,0] & x[0,1])
(x[0,0] | x[0,1])
(arg1[] <-> arg1[0])
(arg1[0] <-> arg1[0,0])
(arg2[] <-> arg2[0])
(arg2[0] <-> arg2[0,1])
1
-}

id = rget $ (procedure @'[ 'In, 'In ] idII) :& (procedure @'[ 'In, 'Out ] idIO) :& (procedure @'[ 'Out, 'In ] idOI) :& RNil
  where
    idII = \arg1 arg2 -> Logic.once $ do
      -- solution: x[0,0]
      -- cost: 0
      () <- (do
        x <- pure arg1
        guard $ arg2 == x
        pure ()
       )
      pure ()
    
    idIO = \arg1 -> do
      -- solution: arg2[] arg2[0] arg2[0,1] x[0,0]
      -- cost: 0
      (arg2) <- (do
        x <- pure arg1
        arg2 <- pure x
        pure (arg2)
       )
      pure (OneTuple (arg2))
    
    idOI = \arg2 -> do
      -- solution: arg1[] arg1[0] arg1[0,0] x[0,1]
      -- cost: 0
      (arg1) <- (do
        x <- pure arg2
        arg1 <- pure x
        pure (arg1)
       )
      pure (OneTuple (arg1))
    
{- pythag/3
pythag i j k :- ((nat i, (>) i data0, data0 = 0, nat j, (>) j data1, data1 = 0, nat k, (>) k data2, data2 = 0, (<) i j, timesInt i i0 ii, i0 = i, timesInt j j0 jj, j0 = j, timesInt k k0 kk, k0 = k, plus ii jj kk)).
constraints:
~(<)[0]
~(>)[0]
~nat[0]
~plus[0]
~timesInt[0]
~(data0[0,1] & data0[0,2])
~(data1[0,4] & data1[0,5])
~(data2[0,7] & data2[0,8])
~(i[0,0] & i[0,1])
~(i[0,0] & i[0,9])
~(i[0,0] & i[0,10])
~(i[0,0] & i[0,11])
~(i[0,1] & i[0,9])
~(i[0,1] & i[0,10])
~(i[0,1] & i[0,11])
~(i[0,9] & i[0,10])
~(i[0,9] & i[0,11])
~(i[0,10] & i[0,11])
~(i0[0,10] & i0[0,11])
~(i0[0,11] & i[0,11])
~(ii[0,10] & ii[0,16])
~(j[0,3] & j[0,4])
~(j[0,3] & j[0,9])
~(j[0,3] & j[0,12])
~(j[0,3] & j[0,13])
~(j[0,4] & j[0,9])
~(j[0,4] & j[0,12])
~(j[0,4] & j[0,13])
~(j[0,9] & j[0,12])
~(j[0,9] & j[0,13])
~(j[0,12] & j[0,13])
~(j0[0,12] & j0[0,13])
~(j0[0,13] & j[0,13])
~(jj[0,12] & jj[0,16])
~(k[0,6] & k[0,7])
~(k[0,6] & k[0,14])
~(k[0,6] & k[0,15])
~(k[0,7] & k[0,14])
~(k[0,7] & k[0,15])
~(k[0,14] & k[0,15])
~(k0[0,14] & k0[0,15])
~(k0[0,15] & k[0,15])
~(kk[0,14] & kk[0,16])
(~i[0,1] & ~data0[0,1])
(~i[0,9] & ~j[0,9])
(~j[0,4] & ~data1[0,4])
(~k[0,7] & ~data2[0,7])
(data0[0,1] | data0[0,2])
(data1[0,4] | data1[0,5])
(data2[0,7] | data2[0,8])
(i[0,0] | ~i[0,0])
(i0[0,10] | i0[0,11])
(ii[0,10] | ii[0,16])
(j[0,3] | ~j[0,3])
(j0[0,12] | j0[0,13])
(jj[0,12] | jj[0,16])
(k[0,6] | ~k[0,6])
(k0[0,14] | k0[0,15])
(kk[0,14] | kk[0,16])
((i[0,10] & (~i0[0,10] & ~ii[0,10])) | ((~i[0,10] & (i0[0,10] & ~ii[0,10])) | ((~i[0,10] & (~i0[0,10] & ii[0,10])) | (~i[0,10] & (~i0[0,10] & ~ii[0,10])))))
((ii[0,16] & (~jj[0,16] & ~kk[0,16])) | ((~ii[0,16] & (jj[0,16] & ~kk[0,16])) | ((~ii[0,16] & (~jj[0,16] & kk[0,16])) | (~ii[0,16] & (~jj[0,16] & ~kk[0,16])))))
((j[0,12] & (~j0[0,12] & ~jj[0,12])) | ((~j[0,12] & (j0[0,12] & ~jj[0,12])) | ((~j[0,12] & (~j0[0,12] & jj[0,12])) | (~j[0,12] & (~j0[0,12] & ~jj[0,12])))))
((k[0,14] & (~k0[0,14] & ~kk[0,14])) | ((~k[0,14] & (k0[0,14] & ~kk[0,14])) | ((~k[0,14] & (~k0[0,14] & kk[0,14])) | (~k[0,14] & (~k0[0,14] & ~kk[0,14])))))
(i[] <-> i[0])
(i[0] <-> (i[0,0] | (i[0,1] | (i[0,9] | (i[0,10] | i[0,11])))))
(j[] <-> j[0])
(j[0] <-> (j[0,3] | (j[0,4] | (j[0,9] | (j[0,12] | j[0,13])))))
(k[] <-> k[0])
(k[0] <-> (k[0,6] | (k[0,7] | (k[0,14] | k[0,15]))))
1
-}
--mode ordering failure, cyclic dependency: [12] timesInt::I j::I j0::O jj::I -> [13] j0::I = j::O
--mode ordering failure, cyclic dependency: [12] timesInt::I j::O j0::I jj::I -> [13] j0::O = j::I
--mode ordering failure, cyclic dependency: [10] timesInt::I i::O i0::I ii::I -> [11] i0::O = i::I
--mode ordering failure, cyclic dependency: [10] timesInt::I i::I i0::O ii::I -> [11] i0::I = i::O
--mode ordering failure, cyclic dependency: [14] timesInt::I k::I k0::O kk::I -> [15] k0::I = k::O
--mode ordering failure, cyclic dependency: [14] timesInt::I k::O k0::I kk::I -> [15] k0::O = k::I
--mode ordering failure, cyclic dependency: [10] timesInt::I i::O i0::I ii::I -> [11] i0::O = i::I
--mode ordering failure, cyclic dependency: [10] timesInt::I i::I i0::O ii::I -> [11] i0::I = i::O
--mode ordering failure, cyclic dependency: [10] timesInt::I i::O i0::I ii::I -> [11] i0::O = i::I
--mode ordering failure, cyclic dependency: [10] timesInt::I i::I i0::O ii::I -> [11] i0::I = i::O
--mode ordering failure, cyclic dependency: [14] timesInt::I k::I k0::O kk::I -> [15] k0::I = k::O
--mode ordering failure, cyclic dependency: [14] timesInt::I k::O k0::I kk::I -> [15] k0::O = k::I
--mode ordering failure, cyclic dependency: [12] timesInt::I j::I j0::O jj::I -> [13] j0::I = j::O
--mode ordering failure, cyclic dependency: [12] timesInt::I j::O j0::I jj::I -> [13] j0::O = j::I
--mode ordering failure, cyclic dependency: [10] timesInt::I i::O i0::I ii::I -> [11] i0::O = i::I
--mode ordering failure, cyclic dependency: [10] timesInt::I i::I i0::O ii::I -> [11] i0::I = i::O
--mode ordering failure, cyclic dependency: [14] timesInt::I k::I k0::O kk::I -> [15] k0::I = k::O
--mode ordering failure, cyclic dependency: [14] timesInt::I k::O k0::I kk::I -> [15] k0::O = k::I
--mode ordering failure, cyclic dependency: [12] timesInt::I j::I j0::O jj::I -> [13] j0::I = j::O
--mode ordering failure, cyclic dependency: [12] timesInt::I j::O j0::I jj::I -> [13] j0::O = j::I
--mode ordering failure, cyclic dependency: [12] timesInt::I j::I j0::O jj::I -> [13] j0::I = j::O
--mode ordering failure, cyclic dependency: [12] timesInt::I j::O j0::I jj::I -> [13] j0::O = j::I
--mode ordering failure, cyclic dependency: [14] timesInt::I k::I k0::O kk::I -> [15] k0::I = k::O
--mode ordering failure, cyclic dependency: [14] timesInt::I k::O k0::I kk::I -> [15] k0::O = k::I
pythag = rget $ (procedure @'[ 'In, 'In, 'In ] pythagIII) :& (procedure @'[ 'In, 'In, 'Out ] pythagIIO) :& (procedure @'[ 'In, 'Out, 'In ] pythagIOI) :& (procedure @'[ 'In, 'Out, 'Out ] pythagIOO) :& (procedure @'[ 'Out, 'In, 'In ] pythagOII) :& (procedure @'[ 'Out, 'In, 'Out ] pythagOIO) :& (procedure @'[ 'Out, 'Out, 'In ] pythagOOI) :& (procedure @'[ 'Out, 'Out, 'Out ] pythagOOO) :& RNil
  where
    pythagIII = \i j k -> Logic.once $ do
      -- solution: data0[0,2] data1[0,5] data2[0,8] i0[0,11] ii[0,16] j0[0,13] jj[0,12] k0[0,15] kk[0,14]
      -- cost: 14
      () <- (do
        data0 <- pure 0
        data1 <- pure 0
        data2 <- pure 0
        i0 <- pure i
        j0 <- pure j
        k0 <- pure k
        guard $ (<) i j
        guard $ (>) i data0
        guard $ (>) j data1
        guard $ (>) k data2
        () <- runProcedure @'[ 'In ] nat i
        () <- runProcedure @'[ 'In ] nat j
        () <- runProcedure @'[ 'In ] nat k
        (OneTuple (jj)) <- runProcedure @'[ 'In, 'In, 'Out ] timesInt j j0
        (OneTuple (kk)) <- runProcedure @'[ 'In, 'In, 'Out ] timesInt k k0
        (OneTuple (ii)) <- runProcedure @'[ 'Out, 'In, 'In ] plus jj kk
        () <- runProcedure @'[ 'In, 'In, 'In ] timesInt i i0 ii
        pure ()
       )
      pure ()
    
    pythagIIO = \i j -> do
      -- solution: data0[0,2] data1[0,5] data2[0,8] i0[0,11] ii[0,16] j0[0,13] jj[0,12] k[] k[0] k[0,6] k0[0,15] kk[0,14]
      -- cost: 15
      (k) <- (do
        data0 <- pure 0
        data1 <- pure 0
        data2 <- pure 0
        i0 <- pure i
        j0 <- pure j
        guard $ (<) i j
        guard $ (>) i data0
        guard $ (>) j data1
        () <- runProcedure @'[ 'In ] nat i
        () <- runProcedure @'[ 'In ] nat j
        (OneTuple (k)) <- runProcedure @'[ 'Out ] nat 
        k0 <- pure k
        guard $ (>) k data2
        (OneTuple (jj)) <- runProcedure @'[ 'In, 'In, 'Out ] timesInt j j0
        (OneTuple (kk)) <- runProcedure @'[ 'In, 'In, 'Out ] timesInt k k0
        (OneTuple (ii)) <- runProcedure @'[ 'Out, 'In, 'In ] plus jj kk
        () <- runProcedure @'[ 'In, 'In, 'In ] timesInt i i0 ii
        pure (k)
       )
      pure (OneTuple (k))
    
    pythagIOI = \i k -> do
      -- solution: data0[0,2] data1[0,5] data2[0,8] i0[0,11] ii[0,16] j[] j[0] j[0,3] j0[0,13] jj[0,12] k0[0,15] kk[0,14]
      -- cost: 15
      (j) <- (do
        data0 <- pure 0
        data1 <- pure 0
        data2 <- pure 0
        i0 <- pure i
        k0 <- pure k
        guard $ (>) i data0
        guard $ (>) k data2
        () <- runProcedure @'[ 'In ] nat i
        () <- runProcedure @'[ 'In ] nat k
        (OneTuple (j)) <- runProcedure @'[ 'Out ] nat 
        j0 <- pure j
        guard $ (<) i j
        guard $ (>) j data1
        (OneTuple (jj)) <- runProcedure @'[ 'In, 'In, 'Out ] timesInt j j0
        (OneTuple (kk)) <- runProcedure @'[ 'In, 'In, 'Out ] timesInt k k0
        (OneTuple (ii)) <- runProcedure @'[ 'Out, 'In, 'In ] plus jj kk
        () <- runProcedure @'[ 'In, 'In, 'In ] timesInt i i0 ii
        pure (j)
       )
      pure (OneTuple (j))
    
    pythagIOO = \i -> do
      -- solution: data0[0,2] data1[0,5] data2[0,8] i0[0,11] ii[0,16] j[] j[0] j[0,3] j0[0,13] jj[0,12] k[] k[0] k[0,6] k0[0,15] kk[0,14]
      -- cost: 16
      (j,k) <- (do
        data0 <- pure 0
        data1 <- pure 0
        data2 <- pure 0
        i0 <- pure i
        guard $ (>) i data0
        () <- runProcedure @'[ 'In ] nat i
        (OneTuple (j)) <- runProcedure @'[ 'Out ] nat 
        j0 <- pure j
        guard $ (<) i j
        guard $ (>) j data1
        (OneTuple (k)) <- runProcedure @'[ 'Out ] nat 
        k0 <- pure k
        guard $ (>) k data2
        (OneTuple (jj)) <- runProcedure @'[ 'In, 'In, 'Out ] timesInt j j0
        (OneTuple (kk)) <- runProcedure @'[ 'In, 'In, 'Out ] timesInt k k0
        (OneTuple (ii)) <- runProcedure @'[ 'Out, 'In, 'In ] plus jj kk
        () <- runProcedure @'[ 'In, 'In, 'In ] timesInt i i0 ii
        pure (j,k)
       )
      pure (j,k)
    
    pythagOII = \j k -> do
      -- solution: data0[0,2] data1[0,5] data2[0,8] i[] i[0] i[0,0] i0[0,11] ii[0,16] j0[0,13] jj[0,12] k0[0,15] kk[0,14]
      -- cost: 15
      (i) <- (do
        data0 <- pure 0
        data1 <- pure 0
        data2 <- pure 0
        j0 <- pure j
        k0 <- pure k
        guard $ (>) j data1
        guard $ (>) k data2
        () <- runProcedure @'[ 'In ] nat j
        () <- runProcedure @'[ 'In ] nat k
        (OneTuple (i)) <- runProcedure @'[ 'Out ] nat 
        i0 <- pure i
        guard $ (<) i j
        guard $ (>) i data0
        (OneTuple (jj)) <- runProcedure @'[ 'In, 'In, 'Out ] timesInt j j0
        (OneTuple (kk)) <- runProcedure @'[ 'In, 'In, 'Out ] timesInt k k0
        (OneTuple (ii)) <- runProcedure @'[ 'Out, 'In, 'In ] plus jj kk
        () <- runProcedure @'[ 'In, 'In, 'In ] timesInt i i0 ii
        pure (i)
       )
      pure (OneTuple (i))
    
    pythagOIO = \j -> do
      -- solution: data0[0,2] data1[0,5] data2[0,8] i[] i[0] i[0,0] i0[0,11] ii[0,16] j0[0,13] jj[0,12] k[] k[0] k[0,6] k0[0,15] kk[0,14]
      -- cost: 16
      (i,k) <- (do
        data0 <- pure 0
        data1 <- pure 0
        data2 <- pure 0
        j0 <- pure j
        guard $ (>) j data1
        () <- runProcedure @'[ 'In ] nat j
        (OneTuple (i)) <- runProcedure @'[ 'Out ] nat 
        i0 <- pure i
        guard $ (<) i j
        guard $ (>) i data0
        (OneTuple (k)) <- runProcedure @'[ 'Out ] nat 
        k0 <- pure k
        guard $ (>) k data2
        (OneTuple (jj)) <- runProcedure @'[ 'In, 'In, 'Out ] timesInt j j0
        (OneTuple (kk)) <- runProcedure @'[ 'In, 'In, 'Out ] timesInt k k0
        (OneTuple (ii)) <- runProcedure @'[ 'Out, 'In, 'In ] plus jj kk
        () <- runProcedure @'[ 'In, 'In, 'In ] timesInt i i0 ii
        pure (i,k)
       )
      pure (i,k)
    
    pythagOOI = \k -> do
      -- solution: data0[0,2] data1[0,5] data2[0,8] i[] i[0] i[0,0] i0[0,11] ii[0,16] j[] j[0] j[0,3] j0[0,13] jj[0,12] k0[0,15] kk[0,14]
      -- cost: 16
      (i,j) <- (do
        data0 <- pure 0
        data1 <- pure 0
        data2 <- pure 0
        k0 <- pure k
        guard $ (>) k data2
        () <- runProcedure @'[ 'In ] nat k
        (OneTuple (i)) <- runProcedure @'[ 'Out ] nat 
        i0 <- pure i
        guard $ (>) i data0
        (OneTuple (j)) <- runProcedure @'[ 'Out ] nat 
        j0 <- pure j
        guard $ (<) i j
        guard $ (>) j data1
        (OneTuple (jj)) <- runProcedure @'[ 'In, 'In, 'Out ] timesInt j j0
        (OneTuple (kk)) <- runProcedure @'[ 'In, 'In, 'Out ] timesInt k k0
        (OneTuple (ii)) <- runProcedure @'[ 'Out, 'In, 'In ] plus jj kk
        () <- runProcedure @'[ 'In, 'In, 'In ] timesInt i i0 ii
        pure (i,j)
       )
      pure (i,j)
    
    pythagOOO = do
      -- solution: data0[0,2] data1[0,5] data2[0,8] i[] i[0] i[0,0] i0[0,11] ii[0,16] j[] j[0] j[0,3] j0[0,13] jj[0,12] k[] k[0] k[0,6] k0[0,15] kk[0,14]
      -- cost: 17
      (i,j,k) <- (do
        data0 <- pure 0
        data1 <- pure 0
        data2 <- pure 0
        (OneTuple (i)) <- runProcedure @'[ 'Out ] nat 
        i0 <- pure i
        guard $ (>) i data0
        (OneTuple (j)) <- runProcedure @'[ 'Out ] nat 
        j0 <- pure j
        guard $ (<) i j
        guard $ (>) j data1
        (OneTuple (k)) <- runProcedure @'[ 'Out ] nat 
        k0 <- pure k
        guard $ (>) k data2
        (OneTuple (jj)) <- runProcedure @'[ 'In, 'In, 'Out ] timesInt j j0
        (OneTuple (kk)) <- runProcedure @'[ 'In, 'In, 'Out ] timesInt k k0
        (OneTuple (ii)) <- runProcedure @'[ 'Out, 'In, 'In ] plus jj kk
        () <- runProcedure @'[ 'In, 'In, 'In ] timesInt i i0 ii
        pure (i,j,k)
       )
      pure (i,j,k)
    
{- triang/2
triang n r :- ((succ n n', timesInt n n' nn', div nn' data0 r, data0 = 2)).
constraints:
~div[0]
~succ[0]
~timesInt[0]
~(data0[0,2] & data0[0,3])
~(n[0,0] & n[0,1])
~(n'[0,0] & n'[0,1])
~(nn'[0,1] & nn'[0,2])
(data0[0,2] | data0[0,3])
(n'[0,0] | n'[0,1])
(nn'[0,1] | nn'[0,2])
((n[0,0] & ~n'[0,0]) | ((~n[0,0] & n'[0,0]) | (~n[0,0] & ~n'[0,0])))
((n[0,1] & (~n'[0,1] & ~nn'[0,1])) | ((~n[0,1] & (n'[0,1] & ~nn'[0,1])) | ((~n[0,1] & (~n'[0,1] & nn'[0,1])) | (~n[0,1] & (~n'[0,1] & ~nn'[0,1])))))
((~nn'[0,2] & (~data0[0,2] & r[0,2])) | (~nn'[0,2] & (~data0[0,2] & ~r[0,2])))
(n[] <-> n[0])
(n[0] <-> (n[0,0] | n[0,1]))
(r[] <-> r[0])
(r[0] <-> r[0,2])
1
-}

triang = rget $ (procedure @'[ 'In, 'In ] triangII) :& (procedure @'[ 'In, 'Out ] triangIO) :& RNil
  where
    triangII = \n r -> Logic.once $ do
      -- solution: data0[0,3] n'[0,0] nn'[0,1]
      -- cost: 5
      () <- (do
        data0 <- pure 2
        (OneTuple (n')) <- runProcedure @'[ 'In, 'Out ] succ n
        (OneTuple (nn')) <- runProcedure @'[ 'In, 'In, 'Out ] timesInt n n'
        () <- runProcedure @'[ 'In, 'In, 'In ] div nn' data0 r
        pure ()
       )
      pure ()
    
    triangIO = \n -> do
      -- solution: data0[0,3] n'[0,0] nn'[0,1] r[] r[0] r[0,2]
      -- cost: 6
      (r) <- (do
        data0 <- pure 2
        (OneTuple (n')) <- runProcedure @'[ 'In, 'Out ] succ n
        (OneTuple (nn')) <- runProcedure @'[ 'In, 'In, 'Out ] timesInt n n'
        (OneTuple (r)) <- runProcedure @'[ 'In, 'In, 'Out ] div nn' data0
        pure (r)
       )
      pure (OneTuple (r))
    
{- ptriang/1
ptriang k :- ((elem k data2, data0 = 1, data1 = 30, data2 = .. data0 data1, elem i data4, data3 = 1, data4 = .. data3 k, elem j data6, data5 = 1, data6 = .. data5 i, triang i ti, triang j tj, triang k tk, plus ti tj tk)).
constraints:
~elem[0]
~plus[0]
~triang[0]
~(data0[0,1] & data0[0,3])
~(data1[0,2] & data1[0,3])
~(data2[0,0] & data2[0,3])
~(data2[0,3] & data0[0,3])
~(data3[0,5] & data3[0,6])
~(data4[0,4] & data4[0,6])
~(data4[0,6] & data3[0,6])
~(data5[0,8] & data5[0,9])
~(data6[0,7] & data6[0,9])
~(data6[0,9] & data5[0,9])
~(i[0,4] & i[0,9])
~(i[0,4] & i[0,10])
~(i[0,9] & i[0,10])
~(j[0,7] & j[0,11])
~(k[0,0] & k[0,6])
~(k[0,0] & k[0,12])
~(k[0,6] & k[0,12])
~(ti[0,10] & ti[0,13])
~(tj[0,11] & tj[0,13])
~(tk[0,12] & tk[0,13])
(data0[0,1] | data0[0,3])
(data1[0,2] | data1[0,3])
(data2[0,0] | data2[0,3])
(data3[0,5] | data3[0,6])
(data4[0,4] | data4[0,6])
(data5[0,8] | data5[0,9])
(data6[0,7] | data6[0,9])
(i[0,4] | (i[0,9] | i[0,10]))
(j[0,7] | j[0,11])
(ti[0,10] | ti[0,13])
(tj[0,11] | tj[0,13])
(tk[0,12] | tk[0,13])
((i[0,4] & ~data4[0,4]) | (~i[0,4] & ~data4[0,4]))
((j[0,7] & ~data6[0,7]) | (~j[0,7] & ~data6[0,7]))
((k[0,0] & ~data2[0,0]) | (~k[0,0] & ~data2[0,0]))
((ti[0,13] & (~tj[0,13] & ~tk[0,13])) | ((~ti[0,13] & (tj[0,13] & ~tk[0,13])) | ((~ti[0,13] & (~tj[0,13] & tk[0,13])) | (~ti[0,13] & (~tj[0,13] & ~tk[0,13])))))
((~i[0,10] & ti[0,10]) | (~i[0,10] & ~ti[0,10]))
((~j[0,11] & tj[0,11]) | (~j[0,11] & ~tj[0,11]))
((~k[0,12] & tk[0,12]) | (~k[0,12] & ~tk[0,12]))
(data0[0,3] <-> data1[0,3])
(data3[0,6] <-> k[0,6])
(data5[0,9] <-> i[0,9])
(k[] <-> k[0])
(k[0] <-> (k[0,0] | (k[0,6] | k[0,12])))
1
-}

ptriang = rget $ (procedure @'[ 'In ] ptriangI) :& (procedure @'[ 'Out ] ptriangO) :& RNil
  where
    ptriangI = \k -> choose . nub . Logic.observeAll $ do
      -- solution: data0[0,1] data1[0,2] data2[0,3] data3[0,5] data4[0,6] data5[0,8] data6[0,9] i[0,4] j[0,7] ti[0,13] tj[0,11] tk[0,12]
      -- cost: 12
      () <- (do
        data0 <- pure 1
        data1 <- pure 30
        data2 <- pure [data0..data1]
        data3 <- pure 1
        data4 <- pure [data3..k]
        data5 <- pure 1
        () <- runProcedure @'[ 'In, 'In ] elem k data2
        (OneTuple (i)) <- runProcedure @'[ 'Out, 'In ] elem data4
        data6 <- pure [data5..i]
        (OneTuple (j)) <- runProcedure @'[ 'Out, 'In ] elem data6
        (OneTuple (tj)) <- runProcedure @'[ 'In, 'Out ] triang j
        (OneTuple (tk)) <- runProcedure @'[ 'In, 'Out ] triang k
        (OneTuple (ti)) <- runProcedure @'[ 'Out, 'In, 'In ] plus tj tk
        () <- runProcedure @'[ 'In, 'In ] triang i ti
        pure ()
       )
      pure ()
    
    ptriangO = choose . nub . Logic.observeAll $ do
      -- solution: data0[0,1] data1[0,2] data2[0,3] data3[0,5] data4[0,6] data5[0,8] data6[0,9] i[0,4] j[0,7] k[] k[0] k[0,0] ti[0,13] tj[0,11] tk[0,12]
      -- cost: 13
      (k) <- (do
        data0 <- pure 1
        data1 <- pure 30
        data2 <- pure [data0..data1]
        data3 <- pure 1
        data5 <- pure 1
        (OneTuple (k)) <- runProcedure @'[ 'Out, 'In ] elem data2
        data4 <- pure [data3..k]
        (OneTuple (i)) <- runProcedure @'[ 'Out, 'In ] elem data4
        data6 <- pure [data5..i]
        (OneTuple (j)) <- runProcedure @'[ 'Out, 'In ] elem data6
        (OneTuple (tj)) <- runProcedure @'[ 'In, 'Out ] triang j
        (OneTuple (tk)) <- runProcedure @'[ 'In, 'Out ] triang k
        (OneTuple (ti)) <- runProcedure @'[ 'Out, 'In, 'In ] plus tj tk
        () <- runProcedure @'[ 'In, 'In ] triang i ti
        pure (k)
       )
      pure (OneTuple (k))
    
{- stepN/2
stepN arg1 arg2 :- ((arg1 = 0, arg2 = 0); ((>) n' data0, data0 = 0, succ n n', stepN n i, succ i i', elem r data2, data1 = [], data2 = i:i':data1, arg1 = n', arg2 = r)).
constraints:
~(>)[1]
~elem[1]
~stepN[1]
~succ[1]
~(arg1[1,8] & n'[1,8])
~(arg2[1,9] & r[1,9])
~(data0[1,0] & data0[1,1])
~(data1[1,6] & data1[1,7])
~(data2[1,5] & data2[1,7])
~(data2[1,7] & i[1,7])
~(i[1,3] & i[1,4])
~(i[1,3] & i[1,7])
~(i[1,4] & i[1,7])
~(i'[1,4] & i'[1,7])
~(n[1,2] & n[1,3])
~(n'[1,0] & n'[1,2])
~(n'[1,0] & n'[1,8])
~(n'[1,2] & n'[1,8])
~(r[1,5] & r[1,9])
(~n'[1,0] & ~data0[1,0])
(data0[1,0] | data0[1,1])
(data1[1,6] | data1[1,7])
(data2[1,5] | data2[1,7])
(i[1,3] | (i[1,4] | i[1,7]))
(i'[1,4] | i'[1,7])
(n[1,2] | n[1,3])
(n'[1,0] | (n'[1,2] | n'[1,8]))
(r[1,5] | r[1,9])
((i[1,4] & ~i'[1,4]) | ((~i[1,4] & i'[1,4]) | (~i[1,4] & ~i'[1,4])))
((n[1,2] & ~n'[1,2]) | ((~n[1,2] & n'[1,2]) | (~n[1,2] & ~n'[1,2])))
((r[1,5] & ~data2[1,5]) | (~r[1,5] & ~data2[1,5]))
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg1[0] <-> arg1[0,0])
(arg1[1] <-> arg1[1,8])
(arg2[] <-> arg2[0])
(arg2[] <-> arg2[1])
(arg2[0] <-> arg2[0,1])
(arg2[1] <-> arg2[1,9])
(i[1,3] <-> arg2[])
(i[1,7] <-> data1[1,7])
(i[1,7] <-> i'[1,7])
(n[1,3] <-> arg1[])
1
-}

stepN = rget $ (procedure @'[ 'In, 'Out ] stepNIO) :& (procedure @'[ 'Out, 'Out ] stepNOO) :& RNil
  where
    stepNIO = \arg1 -> choose . nub . Logic.observeAll $ do
      -- solution: arg2[] arg2[0] arg2[0,1] arg2[1] arg2[1,9] data0[1,1] data1[1,6] data2[1,7] i[1,3] i'[1,4] n[1,2] n'[1,8] r[1,5]
      -- cost: 9
      (arg2) <- (do
        guard $ arg1 == 0
        arg2 <- pure 0
        pure (arg2)
       ) <|> (do
        n' <- pure arg1
        data0 <- pure 0
        data1 <- pure []
        guard $ (>) n' data0
        (OneTuple (n)) <- runProcedure @'[ 'Out, 'In ] succ n'
        (OneTuple (i)) <- stepNIO n
        (OneTuple (i')) <- runProcedure @'[ 'In, 'Out ] succ i
        data2 <- pure (i:i':data1)
        (OneTuple (r)) <- runProcedure @'[ 'Out, 'In ] elem data2
        arg2 <- pure r
        pure (arg2)
       )
      pure (OneTuple (arg2))
    
    stepNOO = choose . nub . Logic.observeAll $ do
      -- solution: arg1[] arg1[0] arg1[0,0] arg1[1] arg1[1,8] arg2[] arg2[0] arg2[0,1] arg2[1] arg2[1,9] data0[1,1] data1[1,6] data2[1,7] i[1,3] i'[1,4] n[1,3] n'[1,2] r[1,5]
      -- cost: 10
      (arg1,arg2) <- (do
        arg1 <- pure 0
        arg2 <- pure 0
        pure (arg1,arg2)
       ) <|> (do
        data0 <- pure 0
        data1 <- pure []
        (n,i) <- stepNOO 
        (OneTuple (i')) <- runProcedure @'[ 'In, 'Out ] succ i
        data2 <- pure (i:i':data1)
        (OneTuple (r)) <- runProcedure @'[ 'Out, 'In ] elem data2
        arg2 <- pure r
        (OneTuple (n')) <- runProcedure @'[ 'In, 'Out ] succ n
        arg1 <- pure n'
        guard $ (>) n' data0
        pure (arg1,arg2)
       )
      pure (arg1,arg2)
    
{- test/1
test arg1 :- ((arg1 = 10); (arg1 = 20); (arg1 = 30)).
constraints:
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg1[] <-> arg1[2])
(arg1[0] <-> arg1[0,0])
(arg1[1] <-> arg1[1,0])
(arg1[2] <-> arg1[2,0])
-}

test = rget $ (procedure @'[ 'In ] testI) :& (procedure @'[ 'Out ] testO) :& RNil
  where
    testI = \arg1 -> Logic.once $ do
      -- solution: 
      -- cost: 0
      () <- (do
        guard $ arg1 == 10
        pure ()
       ) <|> (do
        guard $ arg1 == 20
        pure ()
       ) <|> (do
        guard $ arg1 == 30
        pure ()
       )
      pure ()
    
    testO = do
      -- solution: arg1[] arg1[0] arg1[0,0] arg1[1] arg1[1,0] arg1[2] arg1[2,0]
      -- cost: 0
      (arg1) <- (do
        arg1 <- pure 10
        pure (arg1)
       ) <|> (do
        arg1 <- pure 20
        pure (arg1)
       ) <|> (do
        arg1 <- pure 30
        pure (arg1)
       )
      pure (OneTuple (arg1))
    
{- odds/1
odds arg1 :- ((arg1 = 1); (odds m, plus data0 m n, data0 = 2, arg1 = n)).
constraints:
~odds[1]
~plus[1]
~(arg1[1,3] & n[1,3])
~(data0[1,1] & data0[1,2])
~(m[1,0] & m[1,1])
~(n[1,1] & n[1,3])
(data0[1,1] | data0[1,2])
(m[1,0] | m[1,1])
(n[1,1] | n[1,3])
((data0[1,1] & (~m[1,1] & ~n[1,1])) | ((~data0[1,1] & (m[1,1] & ~n[1,1])) | ((~data0[1,1] & (~m[1,1] & n[1,1])) | (~data0[1,1] & (~m[1,1] & ~n[1,1])))))
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg1[0] <-> arg1[0,0])
(arg1[1] <-> arg1[1,3])
(m[1,0] <-> arg1[])
1
-}

odds = rget $ (procedure @'[ 'In ] oddsI) :& (procedure @'[ 'Out ] oddsO) :& RNil
  where
    oddsI = \arg1 -> Logic.once $ do
      -- solution: data0[1,2] m[1,1] n[1,3]
      -- cost: 3
      () <- (do
        guard $ arg1 == 1
        pure ()
       ) <|> (do
        n <- pure arg1
        data0 <- pure 2
        (OneTuple (m)) <- runProcedure @'[ 'In, 'Out, 'In ] plus data0 n
        () <- oddsI m
        pure ()
       )
      pure ()
    
    oddsO = do
      -- solution: arg1[] arg1[0] arg1[0,0] arg1[1] arg1[1,3] data0[1,2] m[1,0] n[1,1]
      -- cost: 4
      (arg1) <- (do
        arg1 <- pure 1
        pure (arg1)
       ) <|> (do
        data0 <- pure 2
        (OneTuple (m)) <- oddsO 
        (OneTuple (n)) <- runProcedure @'[ 'In, 'In, 'Out ] plus data0 m
        arg1 <- pure n
        pure (arg1)
       )
      pure (OneTuple (arg1))
    
{- even/1
even n :- ((mod n data0 data1, data0 = 2, data1 = 0)).
constraints:
~mod[0]
~(data0[0,0] & data0[0,1])
~(data1[0,0] & data1[0,2])
(data0[0,0] | data0[0,1])
(data1[0,0] | data1[0,2])
((~n[0,0] & (~data0[0,0] & data1[0,0])) | (~n[0,0] & (~data0[0,0] & ~data1[0,0])))
(n[] <-> n[0])
(n[0] <-> n[0,0])
1
-}

even = rget $ (procedure @'[ 'In ] evenI) :& RNil
  where
    evenI = \n -> Logic.once $ do
      -- solution: data0[0,1] data1[0,2]
      -- cost: 1
      () <- (do
        data0 <- pure 2
        data1 <- pure 0
        () <- runProcedure @'[ 'In, 'In, 'In ] mod n data0 data1
        pure ()
       )
      pure ()
    
{- oddsTest/1
oddsTest fresh1 :- ((fresh1 = fresh2, ((odds fresh2); (test fresh2)), even fresh1)).
constraints:
~even[0]
~fresh1[0,2]
~odds[0,1,0]
~test[0,1,1]
~(fresh1[0,0] & fresh1[0,2])
~(fresh1[0,0] & fresh2[0,0])
~(fresh2[0,0] & fresh2[0,1])
(fresh2[0,0] | fresh2[0,1])
(fresh2[0,1,0,0] | ~fresh2[0,1,0,0])
(fresh2[0,1,1,0] | ~fresh2[0,1,1,0])
(fresh1[] <-> fresh1[0])
(fresh1[0] <-> (fresh1[0,0] | fresh1[0,2]))
(fresh2[0,1] <-> fresh2[0,1,0])
(fresh2[0,1] <-> fresh2[0,1,1])
(fresh2[0,1,0] <-> fresh2[0,1,0,0])
(fresh2[0,1,1] <-> fresh2[0,1,1,0])
(odds[0] <-> odds[0,1])
(test[0] <-> test[0,1])
1
-}

oddsTest = rget $ (procedure @'[ 'In ] oddsTestI) :& (procedure @'[ 'Out ] oddsTestO) :& RNil
  where
    oddsTestI = \fresh1 -> Logic.once $ do
      -- solution: fresh2[0,0]
      -- cost: 3
      () <- (do
        fresh2 <- pure fresh1
        () <- runProcedure @'[ 'In ] even fresh1
        () <- (do
          () <- runProcedure @'[ 'In ] odds fresh2
          pure ()
         ) <|> (do
          () <- runProcedure @'[ 'In ] test fresh2
          pure ()
         )
        pure ()
       )
      pure ()
    
    oddsTestO = do
      -- solution: fresh1[] fresh1[0] fresh1[0,0] fresh2[0,1] fresh2[0,1,0] fresh2[0,1,0,0] fresh2[0,1,1] fresh2[0,1,1,0]
      -- cost: 5
      (fresh1) <- (do
        (fresh2) <- (do
          (OneTuple (fresh2)) <- runProcedure @'[ 'Out ] odds 
          pure (fresh2)
         ) <|> (do
          (OneTuple (fresh2)) <- runProcedure @'[ 'Out ] test 
          pure (fresh2)
         )
        fresh1 <- pure fresh2
        () <- runProcedure @'[ 'In ] even fresh1
        pure (fresh1)
       )
      pure (OneTuple (fresh1))
    
{- oddsPlus/2
oddsPlus n x :- ((odds a, plus a n x)).
constraints:
~odds[0]
~plus[0]
~(a[0,0] & a[0,1])
(a[0,0] | a[0,1])
(a[0,0] | ~a[0,0])
((a[0,1] & (~n[0,1] & ~x[0,1])) | ((~a[0,1] & (n[0,1] & ~x[0,1])) | ((~a[0,1] & (~n[0,1] & x[0,1])) | (~a[0,1] & (~n[0,1] & ~x[0,1])))))
(n[] <-> n[0])
(n[0] <-> n[0,1])
(x[] <-> x[0])
(x[0] <-> x[0,1])
1
-}

oddsPlus = rget $ (procedure @'[ 'In, 'In ] oddsPlusII) :& (procedure @'[ 'In, 'Out ] oddsPlusIO) :& (procedure @'[ 'Out, 'In ] oddsPlusOI) :& RNil
  where
    oddsPlusII = \n x -> Logic.once $ do
      -- solution: a[0,1]
      -- cost: 3
      () <- (do
        (OneTuple (a)) <- runProcedure @'[ 'Out, 'In, 'In ] plus n x
        () <- runProcedure @'[ 'In ] odds a
        pure ()
       )
      pure ()
    
    oddsPlusIO = \n -> do
      -- solution: a[0,0] x[] x[0] x[0,1]
      -- cost: 4
      (x) <- (do
        (OneTuple (a)) <- runProcedure @'[ 'Out ] odds 
        (OneTuple (x)) <- runProcedure @'[ 'In, 'In, 'Out ] plus a n
        pure (x)
       )
      pure (OneTuple (x))
    
    oddsPlusOI = \x -> do
      -- solution: a[0,0] n[] n[0] n[0,1]
      -- cost: 4
      (n) <- (do
        (OneTuple (a)) <- runProcedure @'[ 'Out ] odds 
        (OneTuple (n)) <- runProcedure @'[ 'In, 'Out, 'In ] plus a x
        pure (n)
       )
      pure (OneTuple (n))
    
{- oddsPlusTest/1
oddsPlusTest fresh1 :- ((oddsPlus x_0 fresh1, ((x_0 = 0); (x_0 = 1)), even fresh1)).
constraints:
~even[0]
~fresh1[0,2]
~oddsPlus[0]
~(fresh1[0,0] & fresh1[0,2])
~(x_0[0,0] & x_0[0,1])
(x_0[0,0] | x_0[0,1])
((x_0[0,0] & ~fresh1[0,0]) | ((~x_0[0,0] & fresh1[0,0]) | (~x_0[0,0] & ~fresh1[0,0])))
(fresh1[] <-> fresh1[0])
(fresh1[0] <-> (fresh1[0,0] | fresh1[0,2]))
(x_0[0,1] <-> x_0[0,1,0])
(x_0[0,1] <-> x_0[0,1,1])
(x_0[0,1,0] <-> x_0[0,1,0,0])
(x_0[0,1,1] <-> x_0[0,1,1,0])
1
-}

oddsPlusTest = rget $ (procedure @'[ 'In ] oddsPlusTestI) :& (procedure @'[ 'Out ] oddsPlusTestO) :& RNil
  where
    oddsPlusTestI = \fresh1 -> Logic.once $ do
      -- solution: x_0[0,1] x_0[0,1,0] x_0[0,1,0,0] x_0[0,1,1] x_0[0,1,1,0]
      -- cost: 2
      () <- (do
        (x_0) <- (do
          x_0 <- pure 0
          pure (x_0)
         ) <|> (do
          x_0 <- pure 1
          pure (x_0)
         )
        () <- runProcedure @'[ 'In ] even fresh1
        () <- runProcedure @'[ 'In, 'In ] oddsPlus x_0 fresh1
        pure ()
       )
      pure ()
    
    oddsPlusTestO = do
      -- solution: fresh1[] fresh1[0] fresh1[0,0] x_0[0,1] x_0[0,1,0] x_0[0,1,0,0] x_0[0,1,1] x_0[0,1,1,0]
      -- cost: 3
      (fresh1) <- (do
        (x_0) <- (do
          x_0 <- pure 0
          pure (x_0)
         ) <|> (do
          x_0 <- pure 1
          pure (x_0)
         )
        (OneTuple (fresh1)) <- runProcedure @'[ 'In, 'Out ] oddsPlus x_0
        () <- runProcedure @'[ 'In ] even fresh1
        pure (fresh1)
       )
      pure (OneTuple (fresh1))
    
{- oddsPrime/1
oddsPrime n :- ((odds n, (>) n data0, data0 = 1, succ n' n, if (elem d data2, data1 = 1, data2 = .. data1 n', (>) d data3, data3 = 1, mod n d data4, data4 = 0) then (empty) else ())).
constraints:
d[0,4]
data1[0,4]
data2[0,4]
data3[0,4]
data4[0,4]
~(>)[0,4]
~elem[0,4,0]
~empty[0,4,1]
~mod[0,4,0]
~n[0,4]
~n[0,4,0,5]
~n'[0,4]
~n'[0,4,0,2]
~odds[0]
~succ[0]
~(d[0,4,0,0] & d[0,4,0,3])
~(d[0,4,0,0] & d[0,4,0,5])
~(d[0,4,0,3] & d[0,4,0,5])
~(data0[0,1] & data0[0,2])
~(data1[0,4,0,1] & data1[0,4,0,2])
~(data2[0,4,0,0] & data2[0,4,0,2])
~(data2[0,4,0,2] & data1[0,4,0,2])
~(data3[0,4,0,3] & data3[0,4,0,4])
~(data4[0,4,0,5] & data4[0,4,0,6])
~(n[0,0] & n[0,1])
~(n[0,0] & n[0,3])
~(n[0,0] & n[0,4])
~(n[0,1] & n[0,3])
~(n[0,1] & n[0,4])
~(n[0,3] & n[0,4])
~(n'[0,3] & n'[0,4])
(~d[0,4,0,3] & ~data3[0,4,0,3])
(~n[0,1] & ~data0[0,1])
(d[0,4,0,0] | (d[0,4,0,3] | d[0,4,0,5]))
(data0[0,1] | data0[0,2])
(data1[0,4,0,1] | data1[0,4,0,2])
(data2[0,4,0,0] | data2[0,4,0,2])
(data3[0,4,0,3] | data3[0,4,0,4])
(data4[0,4,0,5] | data4[0,4,0,6])
(n[0,0] | ~n[0,0])
(n'[0,3] | n'[0,4])
((d[0,4,0,0] & ~data2[0,4,0,0]) | (~d[0,4,0,0] & ~data2[0,4,0,0]))
((n'[0,3] & ~n[0,3]) | ((~n'[0,3] & n[0,3]) | (~n'[0,3] & ~n[0,3])))
((~n[0,4,0,5] & (~d[0,4,0,5] & data4[0,4,0,5])) | (~n[0,4,0,5] & (~d[0,4,0,5] & ~data4[0,4,0,5])))
((>)[0] <-> (>)[0,4])
(d[0] <-> d[0,4])
(data1[0] <-> data1[0,4])
(data1[0,4,0,2] <-> n'[0,4,0,2])
(data2[0] <-> data2[0,4])
(data3[0] <-> data3[0,4])
(data4[0] <-> data4[0,4])
(elem[0] <-> elem[0,4])
(elem[0,4] <-> elem[0,4,0])
(empty[0] <-> empty[0,4])
(empty[0,4] <-> empty[0,4,1])
(mod[0] <-> mod[0,4])
(mod[0,4] <-> mod[0,4,0])
(n[] <-> n[0])
(n[0] <-> (n[0,0] | (n[0,1] | (n[0,3] | n[0,4]))))
1
-}

oddsPrime = rget $ (procedure @'[ 'In ] oddsPrimeI) :& (procedure @'[ 'Out ] oddsPrimeO) :& RNil
  where
    oddsPrimeI = \n -> Logic.once $ do
      -- solution: d[0] d[0,4] d[0,4,0,0] data0[0,2] data1[0] data1[0,4] data1[0,4,0,1] data2[0] data2[0,4] data2[0,4,0,2] data3[0] data3[0,4] data3[0,4,0,4] data4[0] data4[0,4] data4[0,4,0,6] n'[0,3]
      -- cost: 9
      () <- (do
        data0 <- pure 1
        guard $ (>) n data0
        () <- runProcedure @'[ 'In ] odds n
        (OneTuple (n')) <- runProcedure @'[ 'Out, 'In ] succ n
        () <- Logic.ifte ((do
          data1 <- pure 1
          data2 <- pure [data1..n']
          data3 <- pure 1
          data4 <- pure 0
          (OneTuple (d)) <- runProcedure @'[ 'Out, 'In ] elem data2
          guard $ (>) d data3
          () <- runProcedure @'[ 'In, 'In, 'In ] mod n d data4
          pure ()
         )) (\() -> (do
          () <- empty 
          pure ()
         )) ((do
          
          pure ()
         ))
        pure ()
       )
      pure ()
    
    oddsPrimeO = do
      -- solution: d[0] d[0,4] d[0,4,0,0] data0[0,2] data1[0] data1[0,4] data1[0,4,0,1] data2[0] data2[0,4] data2[0,4,0,2] data3[0] data3[0,4] data3[0,4,0,4] data4[0] data4[0,4] data4[0,4,0,6] n[] n[0] n[0,0] n'[0,3]
      -- cost: 10
      (n) <- (do
        data0 <- pure 1
        (OneTuple (n)) <- runProcedure @'[ 'Out ] odds 
        guard $ (>) n data0
        (OneTuple (n')) <- runProcedure @'[ 'Out, 'In ] succ n
        () <- Logic.ifte ((do
          data1 <- pure 1
          data2 <- pure [data1..n']
          data3 <- pure 1
          data4 <- pure 0
          (OneTuple (d)) <- runProcedure @'[ 'Out, 'In ] elem data2
          guard $ (>) d data3
          () <- runProcedure @'[ 'In, 'In, 'In ] mod n d data4
          pure ()
         )) (\() -> (do
          () <- empty 
          pure ()
         )) ((do
          
          pure ()
         ))
        pure (n)
       )
      pure (OneTuple (n))
    
{- nontrivialDivisor/2
nontrivialDivisor n d :- ((succ n' n, elem d data1, data0 = 2, data1 = .. data0 n', mod n d data2, data2 = 0)).
constraints:
~elem[0]
~mod[0]
~succ[0]
~(d[0,1] & d[0,4])
~(data0[0,2] & data0[0,3])
~(data1[0,1] & data1[0,3])
~(data1[0,3] & data0[0,3])
~(data2[0,4] & data2[0,5])
~(n[0,0] & n[0,4])
~(n'[0,0] & n'[0,3])
(data0[0,2] | data0[0,3])
(data1[0,1] | data1[0,3])
(data2[0,4] | data2[0,5])
(n'[0,0] | n'[0,3])
((d[0,1] & ~data1[0,1]) | (~d[0,1] & ~data1[0,1]))
((n'[0,0] & ~n[0,0]) | ((~n'[0,0] & n[0,0]) | (~n'[0,0] & ~n[0,0])))
((~n[0,4] & (~d[0,4] & data2[0,4])) | (~n[0,4] & (~d[0,4] & ~data2[0,4])))
(d[] <-> d[0])
(d[0] <-> (d[0,1] | d[0,4]))
(data0[0,3] <-> n'[0,3])
(n[] <-> n[0])
(n[0] <-> (n[0,0] | n[0,4]))
1
-}

nontrivialDivisor = rget $ (procedure @'[ 'In, 'In ] nontrivialDivisorII) :& (procedure @'[ 'In, 'Out ] nontrivialDivisorIO) :& RNil
  where
    nontrivialDivisorII = \n d -> Logic.once $ do
      -- solution: data0[0,2] data1[0,3] data2[0,5] n'[0,0]
      -- cost: 4
      () <- (do
        data0 <- pure 2
        data2 <- pure 0
        () <- runProcedure @'[ 'In, 'In, 'In ] mod n d data2
        (OneTuple (n')) <- runProcedure @'[ 'Out, 'In ] succ n
        data1 <- pure [data0..n']
        () <- runProcedure @'[ 'In, 'In ] elem d data1
        pure ()
       )
      pure ()
    
    nontrivialDivisorIO = \n -> do
      -- solution: d[] d[0] d[0,1] data0[0,2] data1[0,3] data2[0,5] n'[0,0]
      -- cost: 5
      (d) <- (do
        data0 <- pure 2
        data2 <- pure 0
        (OneTuple (n')) <- runProcedure @'[ 'Out, 'In ] succ n
        data1 <- pure [data0..n']
        (OneTuple (d)) <- runProcedure @'[ 'Out, 'In ] elem data1
        () <- runProcedure @'[ 'In, 'In, 'In ] mod n d data2
        pure (d)
       )
      pure (OneTuple (d))
    
{- oddsPrimeIO/1
oddsPrimeIO n :- ((odds n, (>) n data0, data0 = 1, if (nontrivialDivisor n d, print d) then (empty) else ())).
constraints:
d[0,3]
~(>)[0]
~d[0,3,0,1]
~empty[0,3,1]
~n[0,3]
~n[0,3,0,0]
~nontrivialDivisor[0,3,0]
~odds[0]
~print[0,3,0]
~(d[0,3,0,0] & d[0,3,0,1])
~(data0[0,1] & data0[0,2])
~(n[0,0] & n[0,1])
~(n[0,0] & n[0,3])
~(n[0,1] & n[0,3])
(~n[0,1] & ~data0[0,1])
(d[0,3,0,0] | d[0,3,0,1])
(data0[0,1] | data0[0,2])
(n[0,0] | ~n[0,0])
((~n[0,3,0,0] & d[0,3,0,0]) | (~n[0,3,0,0] & ~d[0,3,0,0]))
(d[0] <-> d[0,3])
(empty[0] <-> empty[0,3])
(empty[0,3] <-> empty[0,3,1])
(n[] <-> n[0])
(n[0] <-> (n[0,0] | (n[0,1] | n[0,3])))
(nontrivialDivisor[0] <-> nontrivialDivisor[0,3])
(nontrivialDivisor[0,3] <-> nontrivialDivisor[0,3,0])
(print[0] <-> print[0,3])
(print[0,3] <-> print[0,3,0])
1
-}

oddsPrimeIO = rget $ (procedure @'[ 'In ] oddsPrimeIOI) :& (procedure @'[ 'Out ] oddsPrimeIOO) :& RNil
  where
    oddsPrimeIOI = \n -> Logic.once $ do
      -- solution: d[0] d[0,3] d[0,3,0,0] data0[0,2]
      -- cost: 6
      () <- (do
        data0 <- pure 1
        guard $ (>) n data0
        () <- runProcedure @'[ 'In ] odds n
        () <- Logic.ifte ((do
          (OneTuple (d)) <- runProcedure @'[ 'In, 'Out ] nontrivialDivisor n
          () <- runProcedure @'[ 'In ] print d
          pure ()
         )) (\() -> (do
          () <- empty 
          pure ()
         )) ((do
          
          pure ()
         ))
        pure ()
       )
      pure ()
    
    oddsPrimeIOO = do
      -- solution: d[0] d[0,3] d[0,3,0,0] data0[0,2] n[] n[0] n[0,0]
      -- cost: 7
      (n) <- (do
        data0 <- pure 1
        (OneTuple (n)) <- runProcedure @'[ 'Out ] odds 
        guard $ (>) n data0
        () <- Logic.ifte ((do
          (OneTuple (d)) <- runProcedure @'[ 'In, 'Out ] nontrivialDivisor n
          () <- runProcedure @'[ 'In ] print d
          pure ()
         )) (\() -> (do
          () <- empty 
          pure ()
         )) ((do
          
          pure ()
         ))
        pure (n)
       )
      pure (OneTuple (n))
    
{- bogosort/2
bogosort l p :- ((permute l p, sorted p)).
constraints:
~p[0,1]
~permute[0]
~sorted[0]
~(p[0,0] & p[0,1])
((l[0,0] & ~p[0,0]) | ((~l[0,0] & p[0,0]) | (~l[0,0] & ~p[0,0])))
(l[] <-> l[0])
(l[0] <-> l[0,0])
(p[] <-> p[0])
(p[0] <-> (p[0,0] | p[0,1]))
1
-}

bogosort = rget $ (procedure @'[ 'In, 'In ] bogosortII) :& (procedure @'[ 'In, 'Out ] bogosortIO) :& (procedure @'[ 'Out, 'In ] bogosortOI) :& RNil
  where
    bogosortII = \l p -> Logic.once $ do
      -- solution: 
      -- cost: 2
      () <- (do
        () <- runProcedure @'[ 'In, 'In ] permute l p
        () <- runProcedure @'[ 'In ] sorted p
        pure ()
       )
      pure ()
    
    bogosortIO = \l -> do
      -- solution: p[] p[0] p[0,0]
      -- cost: 3
      (p) <- (do
        (OneTuple (p)) <- runProcedure @'[ 'In, 'Out ] permute l
        () <- runProcedure @'[ 'In ] sorted p
        pure (p)
       )
      pure (OneTuple (p))
    
    bogosortOI = \p -> do
      -- solution: l[] l[0] l[0,0]
      -- cost: 3
      (l) <- (do
        () <- runProcedure @'[ 'In ] sorted p
        (OneTuple (l)) <- runProcedure @'[ 'Out, 'In ] permute p
        pure (l)
       )
      pure (OneTuple (l))
    
{- equal/3
equal p q fresh1 :- ((p fresh1, q fresh1)).
constraints:
~p[0]
~q[0]
~(fresh1[0,0] & fresh1[0,1])
(fresh1[] <-> fresh1[0])
(fresh1[0] <-> (fresh1[0,0] | fresh1[0,1]))
(fresh1[0,0] <-> p(1))
(fresh1[0,1] <-> q(1))
(p[] <-> p[0])
(q[] <-> q[0])
1
-}

equal = rget $ (procedure @'[ 'PredMode '[ 'In ], 'PredMode '[ 'In ], 'In ] equalP1IP1II) :& (procedure @'[ 'PredMode '[ 'In ], 'PredMode '[ 'Out ], 'Out ] equalP1IP1OO) :& (procedure @'[ 'PredMode '[ 'Out ], 'PredMode '[ 'In ], 'Out ] equalP1OP1IO) :& RNil
  where
    equalP1IP1II = \p q fresh1 -> Logic.once $ do
      -- solution: 
      -- cost: 2
      () <- (do
        () <- runProcedure p fresh1
        () <- runProcedure q fresh1
        pure ()
       )
      pure ()
    
    equalP1IP1OO = \p q -> do
      -- solution: fresh1[] fresh1[0] fresh1[0,1]
      -- cost: 3
      (fresh1) <- (do
        (OneTuple (fresh1)) <- runProcedure q 
        () <- runProcedure p fresh1
        pure (fresh1)
       )
      pure (OneTuple (fresh1))
    
    equalP1OP1IO = \p q -> do
      -- solution: fresh1[] fresh1[0] fresh1[0,0]
      -- cost: 3
      (fresh1) <- (do
        (OneTuple (fresh1)) <- runProcedure p 
        () <- runProcedure q fresh1
        pure (fresh1)
       )
      pure (OneTuple (fresh1))
    
{- tcomp/4
tcomp i j k carg3 :- ((equal pred0 pred1 carg3, (pred0 fresh1 :- ((i fresh1); (j fresh1); (k fresh1))), (pred1 fresh2 :- ((fresh2 = 0); (fresh2 = 1))))).
constraints:
~equal[0]
~fresh1[0]
~fresh2[0]
~i[0]
~i[0,1,0]
~i[0,1,0,0]
~j[0]
~j[0,1,0]
~j[0,1,0,1]
~k[0]
~k[0,1,0]
~k[0,1,0,2]
~pred0[0,0]
~pred1[0,0]
((~pred0[0,0] & (pred0(1) & (~pred1[0,0] & (~pred1(1) & carg3[0,0])))) | ((~pred0[0,0] & (~pred0(1) & (~pred1[0,0] & (pred1(1) & carg3[0,0])))) | (~pred0[0,0] & (~pred0(1) & (~pred1[0,0] & (~pred1(1) & ~carg3[0,0]))))))
(carg3[] <-> carg3[0])
(carg3[0] <-> carg3[0,0])
(fresh1[0,1,0] <-> fresh1[0,1,0,0])
(fresh1[0,1,0] <-> fresh1[0,1,0,1])
(fresh1[0,1,0] <-> fresh1[0,1,0,2])
(fresh1[0,1,0,0] <-> fresh1[0,1,0,0,0])
(fresh1[0,1,0,0,0] <-> i(1))
(fresh1[0,1,0,1] <-> fresh1[0,1,0,1,0])
(fresh1[0,1,0,1,0] <-> j(1))
(fresh1[0,1,0,2] <-> fresh1[0,1,0,2,0])
(fresh1[0,1,0,2,0] <-> k(1))
(fresh2[0,2,0] <-> fresh2[0,2,0,0])
(fresh2[0,2,0] <-> fresh2[0,2,0,1])
(fresh2[0,2,0,0] <-> fresh2[0,2,0,0,0])
(fresh2[0,2,0,1] <-> fresh2[0,2,0,1,0])
(i[] <-> i[0])
(i[0,1,0] <-> i[0,1,0,0])
(j[] <-> j[0])
(j[0,1,0] <-> j[0,1,0,1])
(k[] <-> k[0])
(k[0,1,0] <-> k[0,1,0,2])
(pred0(1) <-> fresh1[0,1,0])
(pred1(1) <-> fresh2[0,2,0])
1
-}

tcomp = rget $ (procedure @'[ 'PredMode '[ 'In ], 'PredMode '[ 'In ], 'PredMode '[ 'In ], 'In ] tcompP1IP1IP1II) :& (procedure @'[ 'PredMode '[ 'In ], 'PredMode '[ 'In ], 'PredMode '[ 'In ], 'Out ] tcompP1IP1IP1IO) :& (procedure @'[ 'PredMode '[ 'Out ], 'PredMode '[ 'Out ], 'PredMode '[ 'Out ], 'Out ] tcompP1OP1OP1OO) :& RNil
  where
    tcompP1IP1IP1II = \i j k carg3 -> Logic.once $ do
      -- solution: 
      -- cost: 4
      () <- (do
        let pred1 = procedure @'[ 'In ] $
              \fresh2 -> do
                () <- (do
                  guard $ fresh2 == 0
                  pure ()
                 ) <|> (do
                  guard $ fresh2 == 1
                  pure ()
                 )
                pure ()
        let pred0 = procedure @'[ 'In ] $
              \fresh1 -> do
                () <- (do
                  () <- runProcedure i fresh1
                  pure ()
                 ) <|> (do
                  () <- runProcedure j fresh1
                  pure ()
                 ) <|> (do
                  () <- runProcedure k fresh1
                  pure ()
                 )
                pure ()
        () <- runProcedure @'[ 'PredMode '[ 'In ], 'PredMode '[ 'In ], 'In ] equal pred0 pred1 carg3
        pure ()
       )
      pure ()
    
    tcompP1IP1IP1IO = \i j k -> do
      -- solution: carg3[] carg3[0] carg3[0,0] fresh2[0,2,0] fresh2[0,2,0,0] fresh2[0,2,0,0,0] fresh2[0,2,0,1] fresh2[0,2,0,1,0]
      -- cost: 5
      (carg3) <- (do
        let pred1 = procedure @'[ 'Out ] $
              do
                (fresh2) <- (do
                  fresh2 <- pure 0
                  pure (fresh2)
                 ) <|> (do
                  fresh2 <- pure 1
                  pure (fresh2)
                 )
                pure (OneTuple (fresh2))
        let pred0 = procedure @'[ 'In ] $
              \fresh1 -> do
                () <- (do
                  () <- runProcedure i fresh1
                  pure ()
                 ) <|> (do
                  () <- runProcedure j fresh1
                  pure ()
                 ) <|> (do
                  () <- runProcedure k fresh1
                  pure ()
                 )
                pure ()
        (OneTuple (carg3)) <- runProcedure @'[ 'PredMode '[ 'In ], 'PredMode '[ 'Out ], 'Out ] equal pred0 pred1
        pure (carg3)
       )
      pure (OneTuple (carg3))
    
    tcompP1OP1OP1OO = \i j k -> do
      -- solution: carg3[] carg3[0] carg3[0,0] fresh1[0,1,0] fresh1[0,1,0,0] fresh1[0,1,0,0,0] fresh1[0,1,0,1] fresh1[0,1,0,1,0] fresh1[0,1,0,2] fresh1[0,1,0,2,0]
      -- cost: 8
      (carg3) <- (do
        let pred1 = procedure @'[ 'In ] $
              \fresh2 -> do
                () <- (do
                  guard $ fresh2 == 0
                  pure ()
                 ) <|> (do
                  guard $ fresh2 == 1
                  pure ()
                 )
                pure ()
        let pred0 = procedure @'[ 'Out ] $
              do
                (fresh1) <- (do
                  (OneTuple (fresh1)) <- runProcedure i 
                  pure (fresh1)
                 ) <|> (do
                  (OneTuple (fresh1)) <- runProcedure j 
                  pure (fresh1)
                 ) <|> (do
                  (OneTuple (fresh1)) <- runProcedure k 
                  pure (fresh1)
                 )
                pure (OneTuple (fresh1))
        (OneTuple (carg3)) <- runProcedure @'[ 'PredMode '[ 'Out ], 'PredMode '[ 'In ], 'Out ] equal pred0 pred1
        pure (carg3)
       )
      pure (OneTuple (carg3))
    
{- tcomp_ex1/1
tcomp_ex1 r :- ((if (tcomp pred1 pred3 pred5 i, (pred1 curry1 :- (id data0 curry1, data0 = 2)), (pred3 curry1 :- (id data2 curry1, data2 = 1)), (pred5 curry1 :- (id data4 curry1, data4 = 3))) then (r = Just i) else (r = Nothing))).
constraints:
i[0,0,0]
pred1[0,0]
pred3[0,0]
pred5[0,0]
~curry1[0,0,0]
~i[0,0,1,0]
~id[0,0,0]
~id[0,0,0,1,0]
~id[0,0,0,2,0]
~id[0,0,0,3,0]
~pred1[0,0,0,0]
~pred3[0,0,0,0]
~pred5[0,0,0,0]
~tcomp[0,0,0]
~(data0[0,0,0,1,0,0] & data0[0,0,0,1,0,1])
~(data2[0,0,0,2,0,0] & data2[0,0,0,2,0,1])
~(data4[0,0,0,3,0,0] & data4[0,0,0,3,0,1])
~(r[0,0,1,0] & i[0,0,1,0])
(data0[0,0,0,1,0,0] | data0[0,0,0,1,0,1])
(data2[0,0,0,2,0,0] | data2[0,0,0,2,0,1])
(data4[0,0,0,3,0,0] | data4[0,0,0,3,0,1])
((data0[0,0,0,1,0,0] & ~curry1[0,0,0,1,0,0]) | ((~data0[0,0,0,1,0,0] & curry1[0,0,0,1,0,0]) | (~data0[0,0,0,1,0,0] & ~curry1[0,0,0,1,0,0])))
((data2[0,0,0,2,0,0] & ~curry1[0,0,0,2,0,0]) | ((~data2[0,0,0,2,0,0] & curry1[0,0,0,2,0,0]) | (~data2[0,0,0,2,0,0] & ~curry1[0,0,0,2,0,0])))
((data4[0,0,0,3,0,0] & ~curry1[0,0,0,3,0,0]) | ((~data4[0,0,0,3,0,0] & curry1[0,0,0,3,0,0]) | (~data4[0,0,0,3,0,0] & ~curry1[0,0,0,3,0,0])))
((~pred1[0,0,0,0] & (pred1(1) & (~pred3[0,0,0,0] & (pred3(1) & (~pred5[0,0,0,0] & (pred5(1) & i[0,0,0,0])))))) | ((~pred1[0,0,0,0] & (~pred1(1) & (~pred3[0,0,0,0] & (~pred3(1) & (~pred5[0,0,0,0] & (~pred5(1) & i[0,0,0,0])))))) | (~pred1[0,0,0,0] & (~pred1(1) & (~pred3[0,0,0,0] & (~pred3(1) & (~pred5[0,0,0,0] & (~pred5(1) & ~i[0,0,0,0]))))))))
(curry1[0] <-> curry1[0,0])
(curry1[0,0] <-> curry1[0,0,0])
(curry1[0,0,0,1,0] <-> curry1[0,0,0,1,0,0])
(curry1[0,0,0,2,0] <-> curry1[0,0,0,2,0,0])
(curry1[0,0,0,3,0] <-> curry1[0,0,0,3,0,0])
(data0[0] <-> data0[0,0])
(data0[0,0] <-> data0[0,0,0])
(data0[0,0,0] <-> data0[0,0,0,1])
(data2[0] <-> data2[0,0])
(data2[0,0] <-> data2[0,0,0])
(data2[0,0,0] <-> data2[0,0,0,2])
(data4[0] <-> data4[0,0])
(data4[0,0] <-> data4[0,0,0])
(data4[0,0,0] <-> data4[0,0,0,3])
(i[0,0,0] <-> i[0,0,0,0])
(id[0] <-> id[0,0])
(id[0,0] <-> id[0,0,0])
(pred1[0] <-> pred1[0,0])
(pred3[0] <-> pred3[0,0])
(pred5[0] <-> pred5[0,0])
(r[] <-> r[0])
(r[0] <-> r[0,0])
(r[0,0] <-> (r[0,0,1] | r[0,0,2]))
(r[0,0,1] <-> r[0,0,1,0])
(r[0,0,1] <-> r[0,0,2])
(r[0,0,2] <-> r[0,0,2,0])
(tcomp[0] <-> tcomp[0,0])
(tcomp[0,0] <-> tcomp[0,0,0])
(pred1(1) <-> curry1[0,0,0,1,0])
(pred3(1) <-> curry1[0,0,0,2,0])
(pred5(1) <-> curry1[0,0,0,3,0])
1
-}

tcomp_ex1 = rget $ (procedure @'[ 'In ] tcomp_ex1I) :& (procedure @'[ 'Out ] tcomp_ex1O) :& RNil
  where
    tcomp_ex1I = \r -> Logic.once $ do
      -- solution: data0[0,0,0,1,0,1] data2[0,0,0,2,0,1] data4[0,0,0,3,0,1] i[0,0,0] i[0,0,0,0] pred1[0] pred1[0,0] pred3[0] pred3[0,0] pred5[0] pred5[0,0]
      -- cost: 5
      () <- (do
        () <- Logic.ifte ((do
          let pred1 = procedure @'[ 'In ] $
                \curry1 -> do
                  () <- (do
                    data0 <- pure 2
                    () <- runProcedure @'[ 'In, 'In ] id data0 curry1
                    pure ()
                   )
                  pure ()
          let pred3 = procedure @'[ 'In ] $
                \curry1 -> do
                  () <- (do
                    data2 <- pure 1
                    () <- runProcedure @'[ 'In, 'In ] id data2 curry1
                    pure ()
                   )
                  pure ()
          let pred5 = procedure @'[ 'In ] $
                \curry1 -> do
                  () <- (do
                    data4 <- pure 3
                    () <- runProcedure @'[ 'In, 'In ] id data4 curry1
                    pure ()
                   )
                  pure ()
          (OneTuple (i)) <- runProcedure @'[ 'PredMode '[ 'In ], 'PredMode '[ 'In ], 'PredMode '[ 'In ], 'Out ] tcomp pred1 pred3 pred5
          pure (i)
         )) (\(i) -> (do
          guard $ r == (Just i)
          pure ()
         )) ((do
          guard $ r == Nothing
          pure ()
         ))
        pure ()
       )
      pure ()
    
    tcomp_ex1O = do
      -- solution: data0[0,0,0,1,0,1] data2[0,0,0,2,0,1] data4[0,0,0,3,0,1] i[0,0,0] i[0,0,0,0] pred1[0] pred1[0,0] pred3[0] pred3[0,0] pred5[0] pred5[0,0] r[] r[0] r[0,0] r[0,0,1] r[0,0,1,0] r[0,0,2] r[0,0,2,0]
      -- cost: 5
      (r) <- (do
        (r) <- Logic.ifte ((do
          let pred1 = procedure @'[ 'In ] $
                \curry1 -> do
                  () <- (do
                    data0 <- pure 2
                    () <- runProcedure @'[ 'In, 'In ] id data0 curry1
                    pure ()
                   )
                  pure ()
          let pred3 = procedure @'[ 'In ] $
                \curry1 -> do
                  () <- (do
                    data2 <- pure 1
                    () <- runProcedure @'[ 'In, 'In ] id data2 curry1
                    pure ()
                   )
                  pure ()
          let pred5 = procedure @'[ 'In ] $
                \curry1 -> do
                  () <- (do
                    data4 <- pure 3
                    () <- runProcedure @'[ 'In, 'In ] id data4 curry1
                    pure ()
                   )
                  pure ()
          (OneTuple (i)) <- runProcedure @'[ 'PredMode '[ 'In ], 'PredMode '[ 'In ], 'PredMode '[ 'In ], 'Out ] tcomp pred1 pred3 pred5
          pure (i)
         )) (\(i) -> (do
          r <- pure (Just i)
          pure (r)
         )) ((do
          r <- pure Nothing
          pure (r)
         ))
        pure (r)
       )
      pure (OneTuple (r))
    
{- findI/3
findI pat str i :- ((suffix str t, prefix t pat, length t m, length str n, plus i m n)).
constraints:
~length[0]
~plus[0]
~prefix[0]
~suffix[0]
~(m[0,2] & m[0,4])
~(n[0,3] & n[0,4])
~(str[0,0] & str[0,3])
~(t[0,0] & t[0,1])
~(t[0,0] & t[0,2])
~(t[0,1] & t[0,2])
(m[0,2] | m[0,4])
(n[0,3] | n[0,4])
(t[0,0] | (t[0,1] | t[0,2]))
((i[0,4] & (~m[0,4] & ~n[0,4])) | ((~i[0,4] & (m[0,4] & ~n[0,4])) | ((~i[0,4] & (~m[0,4] & n[0,4])) | (~i[0,4] & (~m[0,4] & ~n[0,4])))))
((~str[0,0] & t[0,0]) | (~str[0,0] & ~t[0,0]))
((~str[0,3] & n[0,3]) | (~str[0,3] & ~n[0,3]))
((~t[0,1] & pat[0,1]) | (~t[0,1] & ~pat[0,1]))
((~t[0,2] & m[0,2]) | (~t[0,2] & ~m[0,2]))
(i[] <-> i[0])
(i[0] <-> i[0,4])
(pat[] <-> pat[0])
(pat[0] <-> pat[0,1])
(str[] <-> str[0])
(str[0] <-> (str[0,0] | str[0,3]))
1
-}

findI = rget $ (procedure @'[ 'In, 'In, 'In ] findIIII) :& (procedure @'[ 'In, 'In, 'Out ] findIIIO) :& (procedure @'[ 'Out, 'In, 'In ] findIOII) :& (procedure @'[ 'Out, 'In, 'Out ] findIOIO) :& RNil
  where
    findIIII = \pat str i -> Logic.once $ do
      -- solution: m[0,4] n[0,3] t[0,0]
      -- cost: 8
      () <- (do
        (OneTuple (n)) <- runProcedure @'[ 'In, 'Out ] length str
        (OneTuple (m)) <- runProcedure @'[ 'In, 'Out, 'In ] plus i n
        (OneTuple (t)) <- runProcedure @'[ 'In, 'Out ] suffix str
        () <- runProcedure @'[ 'In, 'In ] length t m
        () <- runProcedure @'[ 'In, 'In ] prefix t pat
        pure ()
       )
      pure ()
    
    findIIIO = \pat str -> do
      -- solution: i[] i[0] i[0,4] m[0,2] n[0,3] t[0,0]
      -- cost: 9
      (i) <- (do
        (OneTuple (n)) <- runProcedure @'[ 'In, 'Out ] length str
        (OneTuple (t)) <- runProcedure @'[ 'In, 'Out ] suffix str
        () <- runProcedure @'[ 'In, 'In ] prefix t pat
        (OneTuple (m)) <- runProcedure @'[ 'In, 'Out ] length t
        (OneTuple (i)) <- runProcedure @'[ 'Out, 'In, 'In ] plus m n
        pure (i)
       )
      pure (OneTuple (i))
    
    findIOII = \str i -> do
      -- solution: m[0,4] n[0,3] pat[] pat[0] pat[0,1] t[0,0]
      -- cost: 9
      (pat) <- (do
        (OneTuple (n)) <- runProcedure @'[ 'In, 'Out ] length str
        (OneTuple (m)) <- runProcedure @'[ 'In, 'Out, 'In ] plus i n
        (OneTuple (t)) <- runProcedure @'[ 'In, 'Out ] suffix str
        () <- runProcedure @'[ 'In, 'In ] length t m
        (OneTuple (pat)) <- runProcedure @'[ 'In, 'Out ] prefix t
        pure (pat)
       )
      pure (OneTuple (pat))
    
    findIOIO = \str -> do
      -- solution: i[] i[0] i[0,4] m[0,2] n[0,3] pat[] pat[0] pat[0,1] t[0,0]
      -- cost: 10
      (i,pat) <- (do
        (OneTuple (n)) <- runProcedure @'[ 'In, 'Out ] length str
        (OneTuple (t)) <- runProcedure @'[ 'In, 'Out ] suffix str
        (OneTuple (m)) <- runProcedure @'[ 'In, 'Out ] length t
        (OneTuple (i)) <- runProcedure @'[ 'Out, 'In, 'In ] plus m n
        (OneTuple (pat)) <- runProcedure @'[ 'In, 'Out ] prefix t
        pure (i,pat)
       )
      pure (pat,i)
    