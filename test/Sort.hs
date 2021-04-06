module Sort where
import Control.Applicative
import Control.Monad.Logic
import Control.Monad.Logic.Moded.Prelude

{- partition/4
partition arg1 arg2 arg3 arg4 :- ((arg1 = [], arg3 = [], arg4 = []); (arg1 = h0 : t, h0 = h, if ((<=) h p) then (partition t p lo1 hi, lo = h1 : lo1, h1 = h) else (partition t p lo hi1, hi = h2 : hi1, h2 = h), arg2 = p, arg3 = lo, arg4 = hi)).
constraints:
~arg2[]
~h[1,2,0,0]
~h[1,2,1,2]
~h[1,2,2]
~p[1,2,0,0]
~p[1,2,1,0]
~p[1,2,2]
~(arg1[1,0] & h0[1,0])
~(arg2[1,3] & p[1,3])
~(arg3[1,4] & lo[1,4])
~(arg4[1,5] & hi[1,5])
~(h0[1,0] & h0[1,1])
~(h0[1,1] & h[1,1])
~(h1[1,2,1,1] & h1[1,2,1,2])
~(h1[1,2,1,2] & h[1,2,1,2])
~(h2[1,2,2,1] & h2[1,2,2,2])
~(h2[1,2,2,2] & h[1,2,2,2])
~(h[1,1] & h[1,2])
~(hi1[1,2,2,0] & hi1[1,2,2,1])
~(hi[1,2,2,1] & h2[1,2,2,1])
~(hi[1,2] & hi[1,5])
~(lo1[1,2,1,0] & lo1[1,2,1,1])
~(lo[1,2,1,1] & h1[1,2,1,1])
~(lo[1,2] & lo[1,4])
~(p[1,2] & p[1,3])
~(t[1,0] & t[1,2])
(~h[1,2,0,0] & ~p[1,2,0,0])
(h0[1,0] | h0[1,1])
(h1[1,2,1,1] | h1[1,2,1,2])
(h2[1,2,2,1] | h2[1,2,2,2])
(h[1,1] | h[1,2])
(hi1[1,2,2,0] | hi1[1,2,2,1])
(hi[1,2] | hi[1,5])
(lo1[1,2,1,0] | lo1[1,2,1,1])
(lo[1,2] | lo[1,4])
(p[1,2] | p[1,3])
(t[1,0] | t[1,2])
(arg1[0] <-> arg1[0,0])
(arg1[1] <-> arg1[1,0])
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg2[1] <-> arg2[1,3])
(arg2[] <-> arg2[1])
(arg3[0] <-> arg3[0,1])
(arg3[1] <-> arg3[1,4])
(arg3[] <-> arg3[0])
(arg3[] <-> arg3[1])
(arg4[0] <-> arg4[0,2])
(arg4[1] <-> arg4[1,5])
(arg4[] <-> arg4[0])
(arg4[] <-> arg4[1])
(h0[1,0] <-> t[1,0])
(h1[1,2,1,1] <-> lo1[1,2,1,1])
(h2[1,2,2,1] <-> hi1[1,2,2,1])
(h[1,2,2] <-> h[1,2,2,2])
(h[1,2] <-> h[1,2,2])
(hi1[1,2,2,0] <-> arg4[])
(hi[1,2,1,0] <-> arg4[])
(hi[1,2,1] <-> hi[1,2,1,0])
(hi[1,2,1] <-> hi[1,2,2])
(hi[1,2,2] <-> hi[1,2,2,1])
(hi[1,2] <-> (hi[1,2,1] | hi[1,2,2]))
(lo1[1,2,1,0] <-> arg3[])
(lo[1,2,1] <-> lo[1,2,1,1])
(lo[1,2,1] <-> lo[1,2,2])
(lo[1,2,2,0] <-> arg3[])
(lo[1,2,2] <-> lo[1,2,2,0])
(lo[1,2] <-> (lo[1,2,1] | lo[1,2,2]))
(p[1,2,1,0] <-> arg2[])
(p[1,2,2,0] <-> arg2[])
(p[1,2,2] <-> p[1,2,2,0])
(p[1,2] <-> p[1,2,2])
(t[1,2,1,0] <-> arg1[])
(t[1,2,1] <-> t[1,2,1,0])
(t[1,2,1] <-> t[1,2,2])
(t[1,2,2,0] <-> arg1[])
(t[1,2,2] <-> t[1,2,2,0])
(t[1,2] <-> (t[1,2,1] | t[1,2,2]))
1
-}
partition_iiii arg1 arg2 arg3 arg4 = do
  -- solution: h0[1,0] h1[1,2,1,1] h2[1,2,2,1] h[1,1] hi1[1,2,2,1] hi[1,5] lo1[1,2,1,1] lo[1,4] p[1,3] t[1,0] ~arg1[0,0] ~arg1[0] ~arg1[1,0] ~arg1[1] ~arg1[] ~arg2[1,3] ~arg2[1] ~arg2[] ~arg3[0,1] ~arg3[0] ~arg3[1,4] ~arg3[1] ~arg3[] ~arg4[0,2] ~arg4[0] ~arg4[1,5] ~arg4[1] ~arg4[] ~h0[1,1] ~h1[1,2,1,2] ~h2[1,2,2,2] ~h[1,2,0,0] ~h[1,2,1,2] ~h[1,2,2,2] ~h[1,2,2] ~h[1,2] ~hi1[1,2,2,0] ~hi[1,2,1,0] ~hi[1,2,1] ~hi[1,2,2,1] ~hi[1,2,2] ~hi[1,2] ~lo1[1,2,1,0] ~lo[1,2,1,1] ~lo[1,2,1] ~lo[1,2,2,0] ~lo[1,2,2] ~lo[1,2] ~p[1,2,0,0] ~p[1,2,1,0] ~p[1,2,2,0] ~p[1,2,2] ~p[1,2] ~t[1,2,1,0] ~t[1,2,1] ~t[1,2,2,0] ~t[1,2,2] ~t[1,2]
  () <- (do
    guard $ arg1 == []
    guard $ arg3 == []
    guard $ arg4 == []
    pure ()
   ) <|> (do
    p <- pure arg2
    lo <- pure arg3
    hi <- pure arg4
    (h0:t) <- pure arg1
    h <- pure h0
    () <- ifte ((do
      () <- if (<=) h p then pure () else empty
      pure ()
     )) (\() -> (do
      (h1:lo1) <- pure lo
      guard $ h1 == h
      () <- partition_iiii t p lo1 hi
      pure ()
     )) ((do
      (h2:hi1) <- pure hi
      guard $ h2 == h
      () <- partition_iiii t p lo hi1
      pure ()
     ))
    pure ()
   )
  pure ()

partition_iiio arg1 arg2 arg3 = do
  -- solution: arg4[0,2] arg4[0] arg4[1,5] arg4[1] arg4[] h0[1,0] h1[1,2,1,1] h2[1,2,2,2] h[1,1] hi1[1,2,2,0] hi[1,2,1,0] hi[1,2,1] hi[1,2,2,1] hi[1,2,2] hi[1,2] lo1[1,2,1,1] lo[1,4] p[1,3] t[1,0] ~arg1[0,0] ~arg1[0] ~arg1[1,0] ~arg1[1] ~arg1[] ~arg2[1,3] ~arg2[1] ~arg2[] ~arg3[0,1] ~arg3[0] ~arg3[1,4] ~arg3[1] ~arg3[] ~h0[1,1] ~h1[1,2,1,2] ~h2[1,2,2,1] ~h[1,2,0,0] ~h[1,2,1,2] ~h[1,2,2,2] ~h[1,2,2] ~h[1,2] ~hi1[1,2,2,1] ~hi[1,5] ~lo1[1,2,1,0] ~lo[1,2,1,1] ~lo[1,2,1] ~lo[1,2,2,0] ~lo[1,2,2] ~lo[1,2] ~p[1,2,0,0] ~p[1,2,1,0] ~p[1,2,2,0] ~p[1,2,2] ~p[1,2] ~t[1,2,1,0] ~t[1,2,1] ~t[1,2,2,0] ~t[1,2,2] ~t[1,2]
  (arg4) <- (do
    guard $ arg1 == []
    guard $ arg3 == []
    arg4 <- pure []
    pure (arg4)
   ) <|> (do
    p <- pure arg2
    lo <- pure arg3
    (h0:t) <- pure arg1
    h <- pure h0
    (hi) <- ifte ((do
      () <- if (<=) h p then pure () else empty
      pure ()
     )) (\() -> (do
      (h1:lo1) <- pure lo
      guard $ h1 == h
      (hi) <- partition_iiio t p lo1
      pure (hi)
     )) ((do
      h2 <- pure h
      (hi1) <- partition_iiio t p lo
      hi <- pure (h2:hi1)
      pure (hi)
     ))
    arg4 <- pure hi
    pure (arg4)
   )
  pure (arg4)

partition_iioi arg1 arg2 arg4 = do
  -- solution: arg3[0,1] arg3[0] arg3[1,4] arg3[1] arg3[] h0[1,0] h1[1,2,1,2] h2[1,2,2,1] h[1,1] hi1[1,2,2,1] hi[1,5] lo1[1,2,1,0] lo[1,2,1,1] lo[1,2,1] lo[1,2,2,0] lo[1,2,2] lo[1,2] p[1,3] t[1,0] ~arg1[0,0] ~arg1[0] ~arg1[1,0] ~arg1[1] ~arg1[] ~arg2[1,3] ~arg2[1] ~arg2[] ~arg4[0,2] ~arg4[0] ~arg4[1,5] ~arg4[1] ~arg4[] ~h0[1,1] ~h1[1,2,1,1] ~h2[1,2,2,2] ~h[1,2,0,0] ~h[1,2,1,2] ~h[1,2,2,2] ~h[1,2,2] ~h[1,2] ~hi1[1,2,2,0] ~hi[1,2,1,0] ~hi[1,2,1] ~hi[1,2,2,1] ~hi[1,2,2] ~hi[1,2] ~lo1[1,2,1,1] ~lo[1,4] ~p[1,2,0,0] ~p[1,2,1,0] ~p[1,2,2,0] ~p[1,2,2] ~p[1,2] ~t[1,2,1,0] ~t[1,2,1] ~t[1,2,2,0] ~t[1,2,2] ~t[1,2]
  (arg3) <- (do
    guard $ arg1 == []
    guard $ arg4 == []
    arg3 <- pure []
    pure (arg3)
   ) <|> (do
    p <- pure arg2
    hi <- pure arg4
    (h0:t) <- pure arg1
    h <- pure h0
    (lo) <- ifte ((do
      () <- if (<=) h p then pure () else empty
      pure ()
     )) (\() -> (do
      h1 <- pure h
      (lo1) <- partition_iioi t p hi
      lo <- pure (h1:lo1)
      pure (lo)
     )) ((do
      (h2:hi1) <- pure hi
      guard $ h2 == h
      (lo) <- partition_iioi t p hi1
      pure (lo)
     ))
    arg3 <- pure lo
    pure (arg3)
   )
  pure (arg3)

partition_iioo arg1 arg2 = do
  -- solution: arg3[0,1] arg3[0] arg3[1,4] arg3[1] arg3[] arg4[0,2] arg4[0] arg4[1,5] arg4[1] arg4[] h0[1,0] h1[1,2,1,2] h2[1,2,2,2] h[1,1] hi1[1,2,2,0] hi[1,2,1,0] hi[1,2,1] hi[1,2,2,1] hi[1,2,2] hi[1,2] lo1[1,2,1,0] lo[1,2,1,1] lo[1,2,1] lo[1,2,2,0] lo[1,2,2] lo[1,2] p[1,3] t[1,0] ~arg1[0,0] ~arg1[0] ~arg1[1,0] ~arg1[1] ~arg1[] ~arg2[1,3] ~arg2[1] ~arg2[] ~h0[1,1] ~h1[1,2,1,1] ~h2[1,2,2,1] ~h[1,2,0,0] ~h[1,2,1,2] ~h[1,2,2,2] ~h[1,2,2] ~h[1,2] ~hi1[1,2,2,1] ~hi[1,5] ~lo1[1,2,1,1] ~lo[1,4] ~p[1,2,0,0] ~p[1,2,1,0] ~p[1,2,2,0] ~p[1,2,2] ~p[1,2] ~t[1,2,1,0] ~t[1,2,1] ~t[1,2,2,0] ~t[1,2,2] ~t[1,2]
  (arg3,arg4) <- (do
    guard $ arg1 == []
    arg3 <- pure []
    arg4 <- pure []
    pure (arg3,arg4)
   ) <|> (do
    p <- pure arg2
    (h0:t) <- pure arg1
    h <- pure h0
    (hi,lo) <- ifte ((do
      () <- if (<=) h p then pure () else empty
      pure ()
     )) (\() -> (do
      h1 <- pure h
      (lo1,hi) <- partition_iioo t p
      lo <- pure (h1:lo1)
      pure (hi,lo)
     )) ((do
      h2 <- pure h
      (lo,hi1) <- partition_iioo t p
      hi <- pure (h2:hi1)
      pure (hi,lo)
     ))
    arg3 <- pure lo
    arg4 <- pure hi
    pure (arg3,arg4)
   )
  pure (arg3,arg4)

{- qsort/3
qsort arg1 arg2 arg3 :- ((arg1 = [], arg2 = r, arg3 = r); (arg1 = x0 : xs, x0 = x, partition xs x ys zs, qsort zs r1 r0, qsort ys r data0, data0 = x1 : r1, x1 = x, arg2 = r, arg3 = r0)).
constraints:
~(arg1[1,0] & x0[1,0])
~(arg2[0,1] & r[0,1])
~(arg2[1,7] & r[1,7])
~(arg3[0,2] & r[0,2])
~(arg3[1,8] & r0[1,8])
~(data0[1,4] & data0[1,5])
~(data0[1,5] & x1[1,5])
~(r0[1,3] & r0[1,8])
~(r1[1,3] & r1[1,5])
~(r[0,1] & r[0,2])
~(r[1,4] & r[1,7])
~(x0[1,0] & x0[1,1])
~(x0[1,1] & x[1,1])
~(x1[1,5] & x1[1,6])
~(x1[1,6] & x[1,6])
~(x[1,1] & x[1,2])
~(x[1,1] & x[1,6])
~(x[1,2] & x[1,6])
~(xs[1,0] & xs[1,2])
~(ys[1,2] & ys[1,4])
~(zs[1,2] & zs[1,3])
(data0[1,4] | data0[1,5])
(r0[1,3] | r0[1,8])
(r1[1,3] | r1[1,5])
(r[0,1] | r[0,2])
(r[1,4] | r[1,7])
(x0[1,0] | x0[1,1])
(x1[1,5] | x1[1,6])
(x[1,1] | (x[1,2] | x[1,6]))
(xs[1,0] | xs[1,2])
(ys[1,2] | ys[1,4])
(zs[1,2] | zs[1,3])
((~xs[1,2] & (~x[1,2] & (ys[1,2] & zs[1,2]))) | ((~xs[1,2] & (~x[1,2] & (ys[1,2] & ~zs[1,2]))) | ((~xs[1,2] & (~x[1,2] & (~ys[1,2] & zs[1,2]))) | (~xs[1,2] & (~x[1,2] & (~ys[1,2] & ~zs[1,2]))))))
(arg1[0] <-> arg1[0,0])
(arg1[1] <-> arg1[1,0])
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg2[0] <-> arg2[0,1])
(arg2[1] <-> arg2[1,7])
(arg2[] <-> arg2[0])
(arg2[] <-> arg2[1])
(arg3[0] <-> arg3[0,2])
(arg3[1] <-> arg3[1,8])
(arg3[] <-> arg3[0])
(arg3[] <-> arg3[1])
(data0[1,4] <-> arg3[])
(r0[1,3] <-> arg3[])
(r1[1,3] <-> arg2[])
(r[1,4] <-> arg2[])
(x0[1,0] <-> xs[1,0])
(x1[1,5] <-> r1[1,5])
(ys[1,4] <-> arg1[])
(zs[1,3] <-> arg1[])
1
-}
-- mode ordering failure, cyclic dependency: [2] partition xs::in x::in ys::out zs::out -> [4] qsort ys::in r::in data0::out -> [5] data0::in = x1::out : r1::out -> [6] x1::in = x::out
qsort_iio arg1 arg2 = do
  -- solution: arg3[0,2] arg3[0] arg3[1,8] arg3[1] arg3[] data0[1,4] r0[1,3] r1[1,5] r[0,1] r[1,7] x0[1,0] x1[1,5] x[1,1] xs[1,0] ys[1,2] zs[1,2] ~arg1[0,0] ~arg1[0] ~arg1[1,0] ~arg1[1] ~arg1[] ~arg2[0,1] ~arg2[0] ~arg2[1,7] ~arg2[1] ~arg2[] ~data0[1,5] ~r0[1,8] ~r1[1,3] ~r[0,2] ~r[1,4] ~x0[1,1] ~x1[1,6] ~x[1,2] ~x[1,6] ~xs[1,2] ~ys[1,4] ~zs[1,3]
  (arg3) <- (do
    r <- pure arg2
    arg3 <- pure r
    guard $ arg1 == []
    pure (arg3)
   ) <|> (do
    r <- pure arg2
    (x0:xs) <- pure arg1
    x <- pure x0
    (ys,zs) <- partition_iioo xs x
    (data0) <- qsort_iio ys r
    (x1:r1) <- pure data0
    guard $ x1 == x
    (r0) <- qsort_iio zs r1
    arg3 <- pure r0
    pure (arg3)
   )
  pure (arg3)

qsort_ioi arg1 arg3 = do
  -- solution: arg2[0,1] arg2[0] arg2[1,7] arg2[1] arg2[] data0[1,5] r0[1,8] r1[1,3] r[0,2] r[1,4] x0[1,0] x1[1,6] x[1,1] xs[1,0] ys[1,2] zs[1,2] ~arg1[0,0] ~arg1[0] ~arg1[1,0] ~arg1[1] ~arg1[] ~arg3[0,2] ~arg3[0] ~arg3[1,8] ~arg3[1] ~arg3[] ~data0[1,4] ~r0[1,3] ~r1[1,5] ~r[0,1] ~r[1,7] ~x0[1,1] ~x1[1,5] ~x[1,2] ~x[1,6] ~xs[1,2] ~ys[1,4] ~zs[1,3]
  (arg2) <- (do
    r <- pure arg3
    arg2 <- pure r
    guard $ arg1 == []
    pure (arg2)
   ) <|> (do
    r0 <- pure arg3
    (x0:xs) <- pure arg1
    x <- pure x0
    x1 <- pure x
    (ys,zs) <- partition_iioo xs x
    (r1) <- qsort_ioi zs r0
    data0 <- pure (x1:r1)
    (r) <- qsort_ioi ys data0
    arg2 <- pure r
    pure (arg2)
   )
  pure (arg2)

{- sort/2
sort arg1 arg2 :- ((qsort list sorted data0, data0 = [], arg1 = list, arg2 = sorted)).
constraints:
~(arg1[0,2] & list[0,2])
~(arg2[0,3] & sorted[0,3])
~(data0[0,0] & data0[0,1])
~(list[0,0] & list[0,2])
~(sorted[0,0] & sorted[0,3])
(data0[0,0] | data0[0,1])
(list[0,0] | list[0,2])
(sorted[0,0] | sorted[0,3])
((~list[0,0] & (sorted[0,0] & ~data0[0,0])) | (~list[0,0] & (~sorted[0,0] & data0[0,0])))
(arg1[0] <-> arg1[0,2])
(arg1[] <-> arg1[0])
(arg2[0] <-> arg2[0,3])
(arg2[] <-> arg2[0])
1
-}
sort_ii arg1 arg2 = do
  -- solution: data0[0,0] list[0,2] sorted[0,3] ~arg1[0,2] ~arg1[0] ~arg1[] ~arg2[0,3] ~arg2[0] ~arg2[] ~data0[0,1] ~list[0,0] ~sorted[0,0]
  () <- (do
    list <- pure arg1
    sorted <- pure arg2
    (data0) <- qsort_iio list sorted
    guard $ data0 == []
    pure ()
   )
  pure ()

sort_io arg1 = do
  -- solution: arg2[0,3] arg2[0] arg2[] data0[0,1] list[0,2] sorted[0,0] ~arg1[0,2] ~arg1[0] ~arg1[] ~data0[0,0] ~list[0,0] ~sorted[0,3]
  (arg2) <- (do
    list <- pure arg1
    data0 <- pure []
    (sorted) <- qsort_ioi list data0
    arg2 <- pure sorted
    pure (arg2)
   )
  pure (arg2)
