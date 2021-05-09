{-# LANGUAGE DataKinds, FlexibleContexts, NoImplicitPrelude, NoMonomorphismRestriction, TypeApplications #-}
module Sort where

import qualified Control.Monad.Logic as Logic
import Control.Monad.Logic.Moded.Prelude

{- partition/4
partition arg1 arg2 arg3 arg4 :- ((arg1 = [], arg3 = [], arg4 = []); (arg1 = h0:t, h0 = h, arg2 = p, arg3 = lo, arg4 = hi, if ((<=) h p) then (partition t p lo1 hi, lo = h1:lo1, h1 = h) else (partition t p lo hi1, hi = h2:hi1, h2 = h))).
constraints:
~(<=)[1,5,0]
~arg2[]
~h[1,5,0,0]
~h[1,5,1,2]
~h[1,5,2]
~p[1,5,0,0]
~p[1,5,1,0]
~p[1,5,2]
~partition[1,5,1]
~partition[1,5,2]
~(arg1[1,0] & h0[1,0])
~(arg2[1,2] & p[1,2])
~(arg3[1,3] & lo[1,3])
~(arg4[1,4] & hi[1,4])
~(h[1,1] & h[1,5])
~(h0[1,0] & h0[1,1])
~(h0[1,1] & h[1,1])
~(h1[1,5,1,1] & h1[1,5,1,2])
~(h1[1,5,1,2] & h[1,5,1,2])
~(h2[1,5,2,1] & h2[1,5,2,2])
~(h2[1,5,2,2] & h[1,5,2,2])
~(hi[1,4] & hi[1,5])
~(hi[1,5,2,1] & h2[1,5,2,1])
~(hi1[1,5,2,0] & hi1[1,5,2,1])
~(lo[1,3] & lo[1,5])
~(lo[1,5,1,1] & h1[1,5,1,1])
~(lo1[1,5,1,0] & lo1[1,5,1,1])
~(p[1,2] & p[1,5])
~(t[1,0] & t[1,5])
(~h[1,5,0,0] & ~p[1,5,0,0])
(h[1,1] | h[1,5])
(h0[1,0] | h0[1,1])
(h1[1,5,1,1] | h1[1,5,1,2])
(h2[1,5,2,1] | h2[1,5,2,2])
(hi[1,4] | hi[1,5])
(hi1[1,5,2,0] | hi1[1,5,2,1])
(lo[1,3] | lo[1,5])
(lo1[1,5,1,0] | lo1[1,5,1,1])
(p[1,2] | p[1,5])
(t[1,0] | t[1,5])
((<=)[1] <-> (<=)[1,5])
((<=)[1,5] <-> (<=)[1,5,0])
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg1[0] <-> arg1[0,0])
(arg1[1] <-> arg1[1,0])
(arg2[] <-> arg2[1])
(arg2[1] <-> arg2[1,2])
(arg3[] <-> arg3[0])
(arg3[] <-> arg3[1])
(arg3[0] <-> arg3[0,1])
(arg3[1] <-> arg3[1,3])
(arg4[] <-> arg4[0])
(arg4[] <-> arg4[1])
(arg4[0] <-> arg4[0,2])
(arg4[1] <-> arg4[1,4])
(h[1,5] <-> h[1,5,2])
(h[1,5,2] <-> h[1,5,2,2])
(h0[1,0] <-> t[1,0])
(h1[1,5,1,1] <-> lo1[1,5,1,1])
(h2[1,5,2,1] <-> hi1[1,5,2,1])
(hi[1,5] <-> (hi[1,5,1] | hi[1,5,2]))
(hi[1,5,1] <-> hi[1,5,1,0])
(hi[1,5,1] <-> hi[1,5,2])
(hi[1,5,1,0] <-> arg4[])
(hi[1,5,2] <-> hi[1,5,2,1])
(hi1[1,5,2,0] <-> arg4[])
(lo[1,5] <-> (lo[1,5,1] | lo[1,5,2]))
(lo[1,5,1] <-> lo[1,5,1,1])
(lo[1,5,1] <-> lo[1,5,2])
(lo[1,5,2] <-> lo[1,5,2,0])
(lo[1,5,2,0] <-> arg3[])
(lo1[1,5,1,0] <-> arg3[])
(p[1,5] <-> p[1,5,2])
(p[1,5,1,0] <-> arg2[])
(p[1,5,2] <-> p[1,5,2,0])
(p[1,5,2,0] <-> arg2[])
(partition[1] <-> partition[1,5])
(partition[1,5] <-> (partition[1,5,1] | partition[1,5,2]))
(t[1,5] <-> (t[1,5,1] | t[1,5,2]))
(t[1,5,1] <-> t[1,5,1,0])
(t[1,5,1] <-> t[1,5,2])
(t[1,5,1,0] <-> arg1[])
(t[1,5,2] <-> t[1,5,2,0])
(t[1,5,2,0] <-> arg1[])
1
-}

partition = rget $ (procedure @'[ 'In, 'In, 'In, 'In ] partitionIIII) :& (procedure @'[ 'In, 'In, 'In, 'Out ] partitionIIIO) :& (procedure @'[ 'In, 'In, 'Out, 'In ] partitionIIOI) :& (procedure @'[ 'In, 'In, 'Out, 'Out ] partitionIIOO) :& RNil
  where
    partitionIIII = \arg1 arg2 arg3 arg4 -> Logic.once $ do
      -- solution: h[1,1] h0[1,0] h1[1,5,1,1] h2[1,5,2,1] hi[1,4] hi1[1,5,2,1] lo[1,3] lo1[1,5,1,1] p[1,2] t[1,0]
      -- cost: 3
      () <- (do
        guard $ arg1 == []
        guard $ arg3 == []
        guard $ arg4 == []
        pure ()
       ) <|> (do
        (h0:t) <- pure arg1
        p <- pure arg2
        lo <- pure arg3
        hi <- pure arg4
        h <- pure h0
        () <- Logic.ifte ((do
          guard $ (<=) h p
          pure ()
         )) (\() -> (do
          (h1:lo1) <- pure lo
          guard $ h1 == h
          () <- partitionIIII t p lo1 hi
          pure ()
         )) ((do
          (h2:hi1) <- pure hi
          guard $ h2 == h
          () <- partitionIIII t p lo hi1
          pure ()
         ))
        pure ()
       )
      pure ()
    
    partitionIIIO = \arg1 arg2 arg3 -> do
      -- solution: arg4[] arg4[0] arg4[0,2] arg4[1] arg4[1,4] h[1,1] h0[1,0] h1[1,5,1,1] h2[1,5,2,2] hi[1,5] hi[1,5,1] hi[1,5,1,0] hi[1,5,2] hi[1,5,2,1] hi1[1,5,2,0] lo[1,3] lo1[1,5,1,1] p[1,2] t[1,0]
      -- cost: 5
      (arg4) <- (do
        guard $ arg1 == []
        guard $ arg3 == []
        arg4 <- pure []
        pure (arg4)
       ) <|> (do
        (h0:t) <- pure arg1
        p <- pure arg2
        lo <- pure arg3
        h <- pure h0
        (hi) <- Logic.ifte ((do
          guard $ (<=) h p
          pure ()
         )) (\() -> (do
          (h1:lo1) <- pure lo
          guard $ h1 == h
          (OneTuple (hi)) <- partitionIIIO t p lo1
          pure (hi)
         )) ((do
          h2 <- pure h
          (OneTuple (hi1)) <- partitionIIIO t p lo
          hi <- pure (h2:hi1)
          pure (hi)
         ))
        arg4 <- pure hi
        pure (arg4)
       )
      pure (OneTuple (arg4))
    
    partitionIIOI = \arg1 arg2 arg4 -> do
      -- solution: arg3[] arg3[0] arg3[0,1] arg3[1] arg3[1,3] h[1,1] h0[1,0] h1[1,5,1,2] h2[1,5,2,1] hi[1,4] hi1[1,5,2,1] lo[1,5] lo[1,5,1] lo[1,5,1,1] lo[1,5,2] lo[1,5,2,0] lo1[1,5,1,0] p[1,2] t[1,0]
      -- cost: 5
      (arg3) <- (do
        guard $ arg1 == []
        arg3 <- pure []
        guard $ arg4 == []
        pure (arg3)
       ) <|> (do
        (h0:t) <- pure arg1
        p <- pure arg2
        hi <- pure arg4
        h <- pure h0
        (lo) <- Logic.ifte ((do
          guard $ (<=) h p
          pure ()
         )) (\() -> (do
          h1 <- pure h
          (OneTuple (lo1)) <- partitionIIOI t p hi
          lo <- pure (h1:lo1)
          pure (lo)
         )) ((do
          (h2:hi1) <- pure hi
          guard $ h2 == h
          (OneTuple (lo)) <- partitionIIOI t p hi1
          pure (lo)
         ))
        arg3 <- pure lo
        pure (arg3)
       )
      pure (OneTuple (arg3))
    
    partitionIIOO = \arg1 arg2 -> do
      -- solution: arg3[] arg3[0] arg3[0,1] arg3[1] arg3[1,3] arg4[] arg4[0] arg4[0,2] arg4[1] arg4[1,4] h[1,1] h0[1,0] h1[1,5,1,2] h2[1,5,2,2] hi[1,5] hi[1,5,1] hi[1,5,1,0] hi[1,5,2] hi[1,5,2,1] hi1[1,5,2,0] lo[1,5] lo[1,5,1] lo[1,5,1,1] lo[1,5,2] lo[1,5,2,0] lo1[1,5,1,0] p[1,2] t[1,0]
      -- cost: 7
      (arg3,arg4) <- (do
        guard $ arg1 == []
        arg3 <- pure []
        arg4 <- pure []
        pure (arg3,arg4)
       ) <|> (do
        (h0:t) <- pure arg1
        p <- pure arg2
        h <- pure h0
        (hi,lo) <- Logic.ifte ((do
          guard $ (<=) h p
          pure ()
         )) (\() -> (do
          h1 <- pure h
          (lo1,hi) <- partitionIIOO t p
          lo <- pure (h1:lo1)
          pure (hi,lo)
         )) ((do
          h2 <- pure h
          (lo,hi1) <- partitionIIOO t p
          hi <- pure (h2:hi1)
          pure (hi,lo)
         ))
        arg3 <- pure lo
        arg4 <- pure hi
        pure (arg3,arg4)
       )
      pure (arg3,arg4)
    
{- qsort/3
qsort arg1 arg2 arg3 :- ((arg1 = [], arg2 = r0, r0 = r, arg3 = r1, r1 = r); (arg1 = x2:xs, x2 = x, arg2 = r, arg3 = r0, partition xs x ys zs, qsort zs r1 r0, qsort ys r data0, data0 = x3:r1, x3 = x)).
constraints:
~partition[1]
~qsort[1]
~(arg1[1,0] & x2[1,0])
~(arg2[0,1] & r0[0,1])
~(arg2[1,2] & r[1,2])
~(arg3[0,3] & r1[0,3])
~(arg3[1,3] & r0[1,3])
~(data0[1,6] & data0[1,7])
~(data0[1,7] & x3[1,7])
~(r[0,2] & r[0,4])
~(r[1,2] & r[1,6])
~(r0[0,1] & r0[0,2])
~(r0[0,2] & r[0,2])
~(r0[1,3] & r0[1,5])
~(r1[0,3] & r1[0,4])
~(r1[0,4] & r[0,4])
~(r1[1,5] & r1[1,7])
~(x[1,1] & x[1,4])
~(x[1,1] & x[1,8])
~(x[1,4] & x[1,8])
~(x2[1,0] & x2[1,1])
~(x2[1,1] & x[1,1])
~(x3[1,7] & x3[1,8])
~(x3[1,8] & x[1,8])
~(xs[1,0] & xs[1,4])
~(ys[1,4] & ys[1,6])
~(zs[1,4] & zs[1,5])
(data0[1,6] | data0[1,7])
(r[0,2] | r[0,4])
(r[1,2] | r[1,6])
(r0[0,1] | r0[0,2])
(r0[1,3] | r0[1,5])
(r1[0,3] | r1[0,4])
(r1[1,5] | r1[1,7])
(x[1,1] | (x[1,4] | x[1,8]))
(x2[1,0] | x2[1,1])
(x3[1,7] | x3[1,8])
(xs[1,0] | xs[1,4])
(ys[1,4] | ys[1,6])
(zs[1,4] | zs[1,5])
((~xs[1,4] & (~x[1,4] & (ys[1,4] & zs[1,4]))) | ((~xs[1,4] & (~x[1,4] & (ys[1,4] & ~zs[1,4]))) | ((~xs[1,4] & (~x[1,4] & (~ys[1,4] & zs[1,4]))) | (~xs[1,4] & (~x[1,4] & (~ys[1,4] & ~zs[1,4]))))))
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg1[0] <-> arg1[0,0])
(arg1[1] <-> arg1[1,0])
(arg2[] <-> arg2[0])
(arg2[] <-> arg2[1])
(arg2[0] <-> arg2[0,1])
(arg2[1] <-> arg2[1,2])
(arg3[] <-> arg3[0])
(arg3[] <-> arg3[1])
(arg3[0] <-> arg3[0,3])
(arg3[1] <-> arg3[1,3])
(data0[1,6] <-> arg3[])
(r[1,6] <-> arg2[])
(r0[1,5] <-> arg3[])
(r1[1,5] <-> arg2[])
(x2[1,0] <-> xs[1,0])
(x3[1,7] <-> r1[1,7])
(ys[1,6] <-> arg1[])
(zs[1,5] <-> arg1[])
1
-}
--mode ordering failure, cyclic dependency: [4] partition::I xs::I x::I ys::O zs::O -> [6] qsort::I ys::I r::I data0::O -> [7] data0::I = x3::O:r1::O -> [8] x3::I = x::O
qsort = rget $ (procedure @'[ 'In, 'In, 'Out ] qsortIIO) :& (procedure @'[ 'In, 'Out, 'In ] qsortIOI) :& RNil
  where
    qsortIIO = \arg1 arg2 -> do
      -- solution: arg3[] arg3[0] arg3[0,3] arg3[1] arg3[1,3] data0[1,6] r[0,2] r[1,2] r0[0,1] r0[1,5] r1[0,4] r1[1,7] x[1,1] x2[1,0] x3[1,7] xs[1,0] ys[1,4] zs[1,4]
      -- cost: 7
      (arg3) <- (do
        guard $ arg1 == []
        r0 <- pure arg2
        r <- pure r0
        r1 <- pure r
        arg3 <- pure r1
        pure (arg3)
       ) <|> (do
        (x2:xs) <- pure arg1
        r <- pure arg2
        x <- pure x2
        (ys,zs) <- runProcedure @'[ 'In, 'In, 'Out, 'Out ] partition xs x
        (OneTuple (data0)) <- qsortIIO ys r
        (x3:r1) <- pure data0
        guard $ x3 == x
        (OneTuple (r0)) <- qsortIIO zs r1
        arg3 <- pure r0
        pure (arg3)
       )
      pure (OneTuple (arg3))
    
    qsortIOI = \arg1 arg3 -> do
      -- solution: arg2[] arg2[0] arg2[0,1] arg2[1] arg2[1,2] data0[1,7] r[0,4] r[1,6] r0[0,2] r0[1,3] r1[0,3] r1[1,5] x[1,1] x2[1,0] x3[1,8] xs[1,0] ys[1,4] zs[1,4]
      -- cost: 7
      (arg2) <- (do
        guard $ arg1 == []
        r1 <- pure arg3
        r <- pure r1
        r0 <- pure r
        arg2 <- pure r0
        pure (arg2)
       ) <|> (do
        (x2:xs) <- pure arg1
        r0 <- pure arg3
        x <- pure x2
        x3 <- pure x
        (ys,zs) <- runProcedure @'[ 'In, 'In, 'Out, 'Out ] partition xs x
        (OneTuple (r1)) <- qsortIOI zs r0
        data0 <- pure (x3:r1)
        (OneTuple (r)) <- qsortIOI ys data0
        arg2 <- pure r
        pure (arg2)
       )
      pure (OneTuple (arg2))
    
{- sort/2
sort list sorted :- ((qsort list sorted data0, data0 = [])).
constraints:
~qsort[0]
~(data0[0,0] & data0[0,1])
(data0[0,0] | data0[0,1])
((~list[0,0] & (sorted[0,0] & ~data0[0,0])) | (~list[0,0] & (~sorted[0,0] & data0[0,0])))
(list[] <-> list[0])
(list[0] <-> list[0,0])
(sorted[] <-> sorted[0])
(sorted[0] <-> sorted[0,0])
1
-}

sort = rget $ (procedure @'[ 'In, 'In ] sortII) :& (procedure @'[ 'In, 'Out ] sortIO) :& RNil
  where
    sortII = \list sorted -> Logic.once $ do
      -- solution: data0[0,0]
      -- cost: 2
      () <- (do
        (OneTuple (data0)) <- runProcedure @'[ 'In, 'In, 'Out ] qsort list sorted
        guard $ data0 == []
        pure ()
       )
      pure ()
    
    sortIO = \list -> do
      -- solution: data0[0,1] sorted[] sorted[0] sorted[0,0]
      -- cost: 2
      (sorted) <- (do
        data0 <- pure []
        (OneTuple (sorted)) <- runProcedure @'[ 'In, 'Out, 'In ] qsort list data0
        pure (sorted)
       )
      pure (OneTuple (sorted))
    