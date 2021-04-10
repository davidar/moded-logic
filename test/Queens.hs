{-# LANGUAGE NoMonomorphismRestriction #-}
module Queens where

import Control.Applicative
import Control.Monad.Logic
import Control.Monad.Logic.Moded.Prelude
import Data.List
import Data.MemoTrie

{- qdelete/3
qdelete arg1 arg2 arg3 :- ((arg2 = h0:t1, h0 = h, t1 = t, arg1 = h, arg3 = t); (arg2 = h2:t3, h2 = h, t3 = t, arg3 = h4:r, h4 = h, qdelete x t r, arg1 = x)).
constraints:
~(arg1[0,3] & h[0,3])
~(arg1[1,6] & x[1,6])
~(arg2[0,0] & h0[0,0])
~(arg2[1,0] & h2[1,0])
~(arg3[0,4] & t[0,4])
~(arg3[1,3] & h4[1,3])
~(h0[0,0] & h0[0,1])
~(h0[0,1] & h[0,1])
~(h2[1,0] & h2[1,1])
~(h2[1,1] & h[1,1])
~(h4[1,3] & h4[1,4])
~(h4[1,4] & h[1,4])
~(h[0,1] & h[0,3])
~(h[1,1] & h[1,4])
~(r[1,3] & r[1,5])
~(t1[0,0] & t1[0,2])
~(t1[0,2] & t[0,2])
~(t3[1,0] & t3[1,2])
~(t3[1,2] & t[1,2])
~(t[0,2] & t[0,4])
~(t[1,2] & t[1,5])
~(x[1,5] & x[1,6])
(h0[0,0] | h0[0,1])
(h2[1,0] | h2[1,1])
(h4[1,3] | h4[1,4])
(h[0,1] | h[0,3])
(h[1,1] | h[1,4])
(r[1,3] | r[1,5])
(t1[0,0] | t1[0,2])
(t3[1,0] | t3[1,2])
(t[0,2] | t[0,4])
(t[1,2] | t[1,5])
(x[1,5] | x[1,6])
(arg1[0] <-> arg1[0,3])
(arg1[1] <-> arg1[1,6])
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg2[0] <-> arg2[0,0])
(arg2[1] <-> arg2[1,0])
(arg2[] <-> arg2[0])
(arg2[] <-> arg2[1])
(arg3[0] <-> arg3[0,4])
(arg3[1] <-> arg3[1,3])
(arg3[] <-> arg3[0])
(arg3[] <-> arg3[1])
(h0[0,0] <-> t1[0,0])
(h2[1,0] <-> t3[1,0])
(h4[1,3] <-> r[1,3])
(r[1,5] <-> arg3[])
(t[1,5] <-> arg2[])
(x[1,5] <-> arg1[])
1
-}
qdelete_iii = \arg1 arg2 arg3 -> do
  -- solution: h0[0,0] h2[1,0] h4[1,3] h[0,1] h[1,1] r[1,3] t1[0,0] t3[1,0] t[0,2] t[1,2] x[1,6] ~arg1[0,3] ~arg1[0] ~arg1[1,6] ~arg1[1] ~arg1[] ~arg2[0,0] ~arg2[0] ~arg2[1,0] ~arg2[1] ~arg2[] ~arg3[0,4] ~arg3[0] ~arg3[1,3] ~arg3[1] ~arg3[] ~h0[0,1] ~h2[1,1] ~h4[1,4] ~h[0,3] ~h[1,4] ~r[1,5] ~t1[0,2] ~t3[1,2] ~t[0,4] ~t[1,5] ~x[1,5]
  () <- (do
    (h0:t1) <- pure arg2
    h <- pure h0
    guard $ arg1 == h
    t <- pure t1
    guard $ arg3 == t
    pure ()
   ) <|> (do
    x <- pure arg1
    (h2:t3) <- pure arg2
    h <- pure h2
    t <- pure t3
    (h4:r) <- pure arg3
    guard $ h4 == h
    () <- qdelete_iii x t r
    pure ()
   )
  pure ()

qdelete_iio = \arg1 arg2 -> do
  -- solution: arg3[0,4] arg3[0] arg3[1,3] arg3[1] arg3[] h0[0,0] h2[1,0] h4[1,4] h[0,1] h[1,1] r[1,5] t1[0,0] t3[1,0] t[0,2] t[1,2] x[1,6] ~arg1[0,3] ~arg1[0] ~arg1[1,6] ~arg1[1] ~arg1[] ~arg2[0,0] ~arg2[0] ~arg2[1,0] ~arg2[1] ~arg2[] ~h0[0,1] ~h2[1,1] ~h4[1,3] ~h[0,3] ~h[1,4] ~r[1,3] ~t1[0,2] ~t3[1,2] ~t[0,4] ~t[1,5] ~x[1,5]
  (arg3) <- (do
    (h0:t1) <- pure arg2
    h <- pure h0
    guard $ arg1 == h
    t <- pure t1
    arg3 <- pure t
    pure (arg3)
   ) <|> (do
    x <- pure arg1
    (h2:t3) <- pure arg2
    h <- pure h2
    h4 <- pure h
    t <- pure t3
    (r) <- qdelete_iio x t
    arg3 <- pure (h4:r)
    pure (arg3)
   )
  pure (arg3)

qdelete_ioi = \arg1 arg3 -> do
  -- solution: arg2[0,0] arg2[0] arg2[1,0] arg2[1] arg2[] h0[0,1] h2[1,1] h4[1,3] h[0,3] h[1,4] r[1,3] t1[0,2] t3[1,2] t[0,4] t[1,5] x[1,6] ~arg1[0,3] ~arg1[0] ~arg1[1,6] ~arg1[1] ~arg1[] ~arg3[0,4] ~arg3[0] ~arg3[1,3] ~arg3[1] ~arg3[] ~h0[0,0] ~h2[1,0] ~h4[1,4] ~h[0,1] ~h[1,1] ~r[1,5] ~t1[0,0] ~t3[1,0] ~t[0,2] ~t[1,2] ~x[1,5]
  (arg2) <- (do
    h <- pure arg1
    t <- pure arg3
    h0 <- pure h
    t1 <- pure t
    arg2 <- pure (h0:t1)
    pure (arg2)
   ) <|> (do
    x <- pure arg1
    (h4:r) <- pure arg3
    h <- pure h4
    h2 <- pure h
    (t) <- qdelete_ioi x r
    t3 <- pure t
    arg2 <- pure (h2:t3)
    pure (arg2)
   )
  pure (arg2)

qdelete_oii = \arg2 arg3 -> do
  -- solution: arg1[0,3] arg1[0] arg1[1,6] arg1[1] arg1[] h0[0,0] h2[1,0] h4[1,3] h[0,1] h[1,1] r[1,3] t1[0,0] t3[1,0] t[0,2] t[1,2] x[1,5] ~arg2[0,0] ~arg2[0] ~arg2[1,0] ~arg2[1] ~arg2[] ~arg3[0,4] ~arg3[0] ~arg3[1,3] ~arg3[1] ~arg3[] ~h0[0,1] ~h2[1,1] ~h4[1,4] ~h[0,3] ~h[1,4] ~r[1,5] ~t1[0,2] ~t3[1,2] ~t[0,4] ~t[1,5] ~x[1,6]
  (arg1) <- (do
    (h0:t1) <- pure arg2
    h <- pure h0
    arg1 <- pure h
    t <- pure t1
    guard $ arg3 == t
    pure (arg1)
   ) <|> (do
    (h2:t3) <- pure arg2
    h <- pure h2
    t <- pure t3
    (h4:r) <- pure arg3
    guard $ h4 == h
    (x) <- qdelete_oii t r
    arg1 <- pure x
    pure (arg1)
   )
  pure (arg1)

qdelete_oio = \arg2 -> do
  -- solution: arg1[0,3] arg1[0] arg1[1,6] arg1[1] arg1[] arg3[0,4] arg3[0] arg3[1,3] arg3[1] arg3[] h0[0,0] h2[1,0] h4[1,4] h[0,1] h[1,1] r[1,5] t1[0,0] t3[1,0] t[0,2] t[1,2] x[1,5] ~arg2[0,0] ~arg2[0] ~arg2[1,0] ~arg2[1] ~arg2[] ~h0[0,1] ~h2[1,1] ~h4[1,3] ~h[0,3] ~h[1,4] ~r[1,3] ~t1[0,2] ~t3[1,2] ~t[0,4] ~t[1,5] ~x[1,6]
  (arg1,arg3) <- (do
    (h0:t1) <- pure arg2
    h <- pure h0
    arg1 <- pure h
    t <- pure t1
    arg3 <- pure t
    pure (arg1,arg3)
   ) <|> (do
    (h2:t3) <- pure arg2
    h <- pure h2
    h4 <- pure h
    t <- pure t3
    (x,r) <- qdelete_oio t
    arg1 <- pure x
    arg3 <- pure (h4:r)
    pure (arg1,arg3)
   )
  pure (arg1,arg3)

{- qperm/2
qperm arg1 arg2 :- ((arg1 = [], arg2 = []); (arg2 = h:t, qdelete h xs ys, qperm ys t, arg1 = xs)).
constraints:
~(arg1[1,3] & xs[1,3])
~(arg2[1,0] & h[1,0])
~(h[1,0] & h[1,1])
~(t[1,0] & t[1,2])
~(xs[1,1] & xs[1,3])
~(ys[1,1] & ys[1,2])
(h[1,0] | h[1,1])
(t[1,0] | t[1,2])
(xs[1,1] | xs[1,3])
(ys[1,1] | ys[1,2])
((h[1,1] & (~xs[1,1] & ys[1,1])) | ((h[1,1] & (~xs[1,1] & ~ys[1,1])) | ((~h[1,1] & (xs[1,1] & ~ys[1,1])) | ((~h[1,1] & (~xs[1,1] & ys[1,1])) | (~h[1,1] & (~xs[1,1] & ~ys[1,1]))))))
(arg1[0] <-> arg1[0,0])
(arg1[1] <-> arg1[1,3])
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg2[0] <-> arg2[0,1])
(arg2[1] <-> arg2[1,0])
(arg2[] <-> arg2[0])
(arg2[] <-> arg2[1])
(h[1,0] <-> t[1,0])
(t[1,2] <-> arg2[])
(ys[1,2] <-> arg1[])
1
-}
qperm_ii = \arg1 arg2 -> do
  -- solution: h[1,0] t[1,0] xs[1,3] ys[1,1] ~arg1[0,0] ~arg1[0] ~arg1[1,3] ~arg1[1] ~arg1[] ~arg2[0,1] ~arg2[0] ~arg2[1,0] ~arg2[1] ~arg2[] ~h[1,1] ~t[1,2] ~xs[1,1] ~ys[1,2]
  () <- (do
    guard $ arg1 == []
    guard $ arg2 == []
    pure ()
   ) <|> (do
    xs <- pure arg1
    (h:t) <- pure arg2
    (ys) <- qdelete_iio h xs
    () <- qperm_ii ys t
    pure ()
   )
  pure ()

qperm_io = \arg1 -> do
  -- solution: arg2[0,1] arg2[0] arg2[1,0] arg2[1] arg2[] h[1,1] t[1,2] xs[1,3] ys[1,1] ~arg1[0,0] ~arg1[0] ~arg1[1,3] ~arg1[1] ~arg1[] ~h[1,0] ~t[1,0] ~xs[1,1] ~ys[1,2]
  (arg2) <- (do
    guard $ arg1 == []
    arg2 <- pure []
    pure (arg2)
   ) <|> (do
    xs <- pure arg1
    (h,ys) <- qdelete_oio xs
    (t) <- qperm_io ys
    arg2 <- pure (h:t)
    pure (arg2)
   )
  pure (arg2)

qperm_oi = \arg2 -> do
  -- solution: arg1[0,0] arg1[0] arg1[1,3] arg1[1] arg1[] h[1,0] t[1,0] xs[1,1] ys[1,2] ~arg2[0,1] ~arg2[0] ~arg2[1,0] ~arg2[1] ~arg2[] ~h[1,1] ~t[1,2] ~xs[1,3] ~ys[1,1]
  (arg1) <- (do
    guard $ arg2 == []
    arg1 <- pure []
    pure (arg1)
   ) <|> (do
    (h:t) <- pure arg2
    (ys) <- qperm_oi t
    (xs) <- qdelete_ioi h ys
    arg1 <- pure xs
    pure (arg1)
   )
  pure (arg1)

{- nodiag/3
nodiag arg1 arg2 arg3 :- ((arg3 = []); (arg3 = h:t, plus hmb b h, plus bmh h b, succ d d1, if (d = hmb) then (empty) else (if (d = bmh) then (empty) else (nodiag b d1 t)), arg1 = b, arg2 = d)).
constraints:
~arg1[]
~arg2[]
~b[1,4,2,0,2]
~b[1,4,2]
~bmh[1,4,2,0,0,0]
~bmh[1,4,2,0]
~bmh[1,4,2]
~d1[1,4,2,0,2]
~d1[1,4,2]
~d[1,4,0,0]
~d[1,4,2,0,0,0]
~d[1,4,2,0]
~d[1,4,2]
~hmb[1,4,0,0]
~hmb[1,4]
~t[1,4,2,0,2]
~t[1,4,2]
~(arg1[1,5] & b[1,5])
~(arg2[1,6] & d[1,6])
~(arg3[1,0] & h[1,0])
~(b[1,1] & b[1,2])
~(b[1,1] & b[1,4])
~(b[1,1] & b[1,5])
~(b[1,2] & b[1,4])
~(b[1,2] & b[1,5])
~(b[1,4] & b[1,5])
~(bmh[1,2] & bmh[1,4])
~(d1[1,3] & d1[1,4])
~(d[1,3] & d[1,4])
~(d[1,3] & d[1,6])
~(d[1,4,0,0] & hmb[1,4,0,0])
~(d[1,4,2,0,0,0] & bmh[1,4,2,0,0,0])
~(d[1,4] & d[1,6])
~(h[1,0] & h[1,1])
~(h[1,0] & h[1,2])
~(h[1,1] & h[1,2])
~(hmb[1,1] & hmb[1,4])
~(t[1,0] & t[1,4])
(b[1,1] | (b[1,2] | (b[1,4] | b[1,5])))
(bmh[1,2] | bmh[1,4])
(d1[1,3] | d1[1,4])
(d[1,3] | (d[1,4] | d[1,6]))
(h[1,0] | (h[1,1] | h[1,2]))
(hmb[1,1] | hmb[1,4])
(t[1,0] | t[1,4])
((bmh[1,2] & (~h[1,2] & ~b[1,2])) | ((~bmh[1,2] & (h[1,2] & ~b[1,2])) | (~bmh[1,2] & (~h[1,2] & b[1,2]))))
((d[1,3] & ~d1[1,3]) | ((~d[1,3] & d1[1,3]) | (~d[1,3] & ~d1[1,3])))
((hmb[1,1] & (~b[1,1] & ~h[1,1])) | ((~hmb[1,1] & (b[1,1] & ~h[1,1])) | (~hmb[1,1] & (~b[1,1] & h[1,1]))))
(arg1[1] <-> arg1[1,5])
(arg1[] <-> arg1[1])
(arg2[1] <-> arg2[1,6])
(arg2[] <-> arg2[1])
(arg3[0] <-> arg3[0,0])
(arg3[1] <-> arg3[1,0])
(arg3[] <-> arg3[0])
(arg3[] <-> arg3[1])
(b[1,4,2,0,2,0] <-> arg1[])
(b[1,4,2,0,2] <-> b[1,4,2,0,2,0])
(b[1,4,2,0] <-> b[1,4,2,0,2])
(b[1,4,2] <-> b[1,4,2,0])
(b[1,4] <-> b[1,4,2])
(bmh[1,4,2] <-> bmh[1,4,2,0])
(bmh[1,4] <-> bmh[1,4,2])
(d1[1,4,2,0,2,0] <-> arg2[])
(d1[1,4,2,0,2] <-> d1[1,4,2,0,2,0])
(d1[1,4,2,0] <-> d1[1,4,2,0,2])
(d1[1,4,2] <-> d1[1,4,2,0])
(d1[1,4] <-> d1[1,4,2])
(d[1,4,2] <-> d[1,4,2,0])
(d[1,4] <-> d[1,4,2])
(h[1,0] <-> t[1,0])
(t[1,4,2,0,2,0] <-> arg3[])
(t[1,4,2,0,2] <-> t[1,4,2,0,2,0])
(t[1,4,2,0] <-> t[1,4,2,0,2])
(t[1,4,2] <-> t[1,4,2,0])
(t[1,4] <-> t[1,4,2])
1
-}
nodiag_iii = \arg1 arg2 arg3 -> do
  -- solution: b[1,5] bmh[1,2] d1[1,3] d[1,6] h[1,0] hmb[1,1] t[1,0] ~arg1[1,5] ~arg1[1] ~arg1[] ~arg2[1,6] ~arg2[1] ~arg2[] ~arg3[0,0] ~arg3[0] ~arg3[1,0] ~arg3[1] ~arg3[] ~b[1,1] ~b[1,2] ~b[1,4,2,0,2,0] ~b[1,4,2,0,2] ~b[1,4,2,0] ~b[1,4,2] ~b[1,4] ~bmh[1,4,2,0,0,0] ~bmh[1,4,2,0] ~bmh[1,4,2] ~bmh[1,4] ~d1[1,4,2,0,2,0] ~d1[1,4,2,0,2] ~d1[1,4,2,0] ~d1[1,4,2] ~d1[1,4] ~d[1,3] ~d[1,4,0,0] ~d[1,4,2,0,0,0] ~d[1,4,2,0] ~d[1,4,2] ~d[1,4] ~h[1,1] ~h[1,2] ~hmb[1,4,0,0] ~hmb[1,4] ~t[1,4,2,0,2,0] ~t[1,4,2,0,2] ~t[1,4,2,0] ~t[1,4,2] ~t[1,4]
  () <- (do
    guard $ arg3 == []
    pure ()
   ) <|> (do
    b <- pure arg1
    d <- pure arg2
    (h:t) <- pure arg3
    (bmh) <- plus_oii h b
    (hmb) <- plus_oii b h
    (d1) <- succ_io d
    () <- ifte ((do
      guard $ d == hmb
      pure ()
     )) (\() -> (do
      () <- empty 
      pure ()
     )) ((do
      () <- ifte ((do
        guard $ d == bmh
        pure ()
       )) (\() -> (do
        () <- empty 
        pure ()
       )) ((do
        () <- nodiag_iii b d1 t
        pure ()
       ))
      pure ()
     ))
    pure ()
   )
  pure ()

{- safe/1
safe arg1 :- ((arg1 = []); (arg1 = h:t, nodiag h data0 t, data0 = 1, safe t)).
constraints:
~(arg1[1,0] & h[1,0])
~(data0[1,1] & data0[1,2])
~(h[1,0] & h[1,1])
~(t[1,0] & t[1,1])
~(t[1,0] & t[1,3])
~(t[1,1] & t[1,3])
(~h[1,1] & (~data0[1,1] & ~t[1,1]))
(data0[1,1] | data0[1,2])
(h[1,0] | h[1,1])
(t[1,0] | (t[1,1] | t[1,3]))
(arg1[0] <-> arg1[0,0])
(arg1[1] <-> arg1[1,0])
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(h[1,0] <-> t[1,0])
(t[1,3] <-> arg1[])
1
-}
safe_i = \arg1 -> do
  -- solution: data0[1,2] h[1,0] t[1,0] ~arg1[0,0] ~arg1[0] ~arg1[1,0] ~arg1[1] ~arg1[] ~data0[1,1] ~h[1,1] ~t[1,1] ~t[1,3]
  () <- (do
    guard $ arg1 == []
    pure ()
   ) <|> (do
    data0 <- pure 1
    (h:t) <- pure arg1
    () <- nodiag_iii h data0 t
    () <- safe_i t
    pure ()
   )
  pure ()

{- queens1/2
queens1 arg1 arg2 :- ((qperm dat out, safe out, arg1 = dat, arg2 = out)).
constraints:
~out[0,1]
~(arg1[0,2] & dat[0,2])
~(arg2[0,3] & out[0,3])
~(dat[0,0] & dat[0,2])
~(out[0,0] & out[0,1])
~(out[0,0] & out[0,3])
~(out[0,1] & out[0,3])
(dat[0,0] | dat[0,2])
(out[0,0] | (out[0,1] | out[0,3]))
((dat[0,0] & ~out[0,0]) | ((~dat[0,0] & out[0,0]) | (~dat[0,0] & ~out[0,0])))
(arg1[0] <-> arg1[0,2])
(arg1[] <-> arg1[0])
(arg2[0] <-> arg2[0,3])
(arg2[] <-> arg2[0])
1
-}
queens1_ii = \arg1 arg2 -> do
  -- solution: dat[0,0] out[0,3] ~arg1[0,2] ~arg1[0] ~arg1[] ~arg2[0,3] ~arg2[0] ~arg2[] ~dat[0,2] ~out[0,0] ~out[0,1]
  () <- (do
    out <- pure arg2
    () <- safe_i out
    (dat) <- qperm_oi out
    guard $ arg1 == dat
    pure ()
   )
  pure ()

queens1_io = \arg1 -> do
  -- solution: arg2[0,3] arg2[0] arg2[] dat[0,2] out[0,0] ~arg1[0,2] ~arg1[0] ~arg1[] ~dat[0,0] ~out[0,1] ~out[0,3]
  (arg2) <- (do
    dat <- pure arg1
    (out) <- qperm_io dat
    arg2 <- pure out
    () <- safe_i out
    pure (arg2)
   )
  pure (arg2)

queens1_oi = \arg2 -> do
  -- solution: arg1[0,2] arg1[0] arg1[] dat[0,0] out[0,3] ~arg2[0,3] ~arg2[0] ~arg2[] ~dat[0,2] ~out[0,0] ~out[0,1]
  (arg1) <- (do
    out <- pure arg2
    () <- safe_i out
    (dat) <- qperm_oi out
    arg1 <- pure dat
    pure (arg1)
   )
  pure (arg1)

{- cqueens/3
cqueens arg1 arg2 arg3 :- ((arg1 = [], arg3 = []); (arg3 = q0:m, q0 = q, xs = _:_, qdelete q xs r, nodiag q data0 history, data0 = 1, cqueens r data1 m, data1 = q1:history, q1 = q, arg1 = xs, arg2 = history)).
constraints:
~arg2[]
~xs[1,2]
~(arg1[1,9] & xs[1,9])
~(arg2[1,10] & history[1,10])
~(arg3[1,0] & q0[1,0])
~(data0[1,4] & data0[1,5])
~(data1[1,6] & data1[1,7])
~(data1[1,7] & q1[1,7])
~(history[1,10] & history[1,4])
~(history[1,10] & history[1,7])
~(history[1,4] & history[1,7])
~(m[1,0] & m[1,6])
~(q0[1,0] & q0[1,1])
~(q0[1,1] & q[1,1])
~(q1[1,7] & q1[1,8])
~(q1[1,8] & q[1,8])
~(q[1,1] & q[1,3])
~(q[1,1] & q[1,4])
~(q[1,1] & q[1,8])
~(q[1,3] & q[1,4])
~(q[1,3] & q[1,8])
~(q[1,4] & q[1,8])
~(r[1,3] & r[1,6])
~(xs[1,2] & xs[1,3])
~(xs[1,2] & xs[1,9])
~(xs[1,3] & xs[1,9])
(~q[1,4] & (~data0[1,4] & ~history[1,4]))
(data0[1,4] | data0[1,5])
(data1[1,6] | data1[1,7])
(history[1,4] | (history[1,7] | history[1,10]))
(m[1,0] | m[1,6])
(q0[1,0] | q0[1,1])
(q1[1,7] | q1[1,8])
(q[1,1] | (q[1,3] | (q[1,4] | q[1,8])))
(r[1,3] | r[1,6])
(xs[1,2] | (xs[1,3] | xs[1,9]))
((q[1,3] & (~xs[1,3] & r[1,3])) | ((q[1,3] & (~xs[1,3] & ~r[1,3])) | ((~q[1,3] & (xs[1,3] & ~r[1,3])) | ((~q[1,3] & (~xs[1,3] & r[1,3])) | (~q[1,3] & (~xs[1,3] & ~r[1,3]))))))
(arg1[0] <-> arg1[0,0])
(arg1[1] <-> arg1[1,9])
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg2[1] <-> arg2[1,10])
(arg2[] <-> arg2[1])
(arg3[0] <-> arg3[0,1])
(arg3[1] <-> arg3[1,0])
(arg3[] <-> arg3[0])
(arg3[] <-> arg3[1])
(data1[1,6] <-> arg2[])
(m[1,6] <-> arg3[])
(q0[1,0] <-> m[1,0])
(q1[1,7] <-> history[1,7])
(r[1,6] <-> arg1[])
1
-}
cqueens_iii = \arg1 arg2 arg3 -> do
  -- solution: data0[1,5] data1[1,7] history[1,10] m[1,0] q0[1,0] q1[1,8] q[1,1] r[1,3] xs[1,9] ~arg1[0,0] ~arg1[0] ~arg1[1,9] ~arg1[1] ~arg1[] ~arg2[1,10] ~arg2[1] ~arg2[] ~arg3[0,1] ~arg3[0] ~arg3[1,0] ~arg3[1] ~arg3[] ~data0[1,4] ~data1[1,6] ~history[1,4] ~history[1,7] ~m[1,6] ~q0[1,1] ~q1[1,7] ~q[1,3] ~q[1,4] ~q[1,8] ~r[1,6] ~xs[1,2] ~xs[1,3]
  () <- (do
    guard $ arg1 == []
    guard $ arg3 == []
    pure ()
   ) <|> (do
    xs <- pure arg1
    history <- pure arg2
    data0 <- pure 1
    (_:_) <- pure xs
    (q0:m) <- pure arg3
    q <- pure q0
    q1 <- pure q
    data1 <- pure (q1:history)
    () <- nodiag_iii q data0 history
    (r) <- qdelete_iio q xs
    () <- cqueens_iii r data1 m
    pure ()
   )
  pure ()

cqueens_iio = \arg1 arg2 -> do
  -- solution: arg3[0,1] arg3[0] arg3[1,0] arg3[1] arg3[] data0[1,5] data1[1,7] history[1,10] m[1,6] q0[1,1] q1[1,8] q[1,3] r[1,3] xs[1,9] ~arg1[0,0] ~arg1[0] ~arg1[1,9] ~arg1[1] ~arg1[] ~arg2[1,10] ~arg2[1] ~arg2[] ~data0[1,4] ~data1[1,6] ~history[1,4] ~history[1,7] ~m[1,0] ~q0[1,0] ~q1[1,7] ~q[1,1] ~q[1,4] ~q[1,8] ~r[1,6] ~xs[1,2] ~xs[1,3]
  (arg3) <- (do
    guard $ arg1 == []
    arg3 <- pure []
    pure (arg3)
   ) <|> (do
    xs <- pure arg1
    history <- pure arg2
    data0 <- pure 1
    (_:_) <- pure xs
    (q,r) <- qdelete_oio xs
    q0 <- pure q
    q1 <- pure q
    data1 <- pure (q1:history)
    () <- nodiag_iii q data0 history
    (m) <- cqueens_iio r data1
    arg3 <- pure (q0:m)
    pure (arg3)
   )
  pure (arg3)

cqueens_oii = \arg2 arg3 -> do
  -- solution: arg1[0,0] arg1[0] arg1[1,9] arg1[1] arg1[] data0[1,5] data1[1,7] history[1,10] m[1,0] q0[1,0] q1[1,8] q[1,1] r[1,6] xs[1,3] ~arg2[1,10] ~arg2[1] ~arg2[] ~arg3[0,1] ~arg3[0] ~arg3[1,0] ~arg3[1] ~arg3[] ~data0[1,4] ~data1[1,6] ~history[1,4] ~history[1,7] ~m[1,6] ~q0[1,1] ~q1[1,7] ~q[1,3] ~q[1,4] ~q[1,8] ~r[1,3] ~xs[1,2] ~xs[1,9]
  (arg1) <- (do
    guard $ arg3 == []
    arg1 <- pure []
    pure (arg1)
   ) <|> (do
    history <- pure arg2
    data0 <- pure 1
    (q0:m) <- pure arg3
    q <- pure q0
    q1 <- pure q
    data1 <- pure (q1:history)
    () <- nodiag_iii q data0 history
    (r) <- cqueens_oii data1 m
    (xs) <- qdelete_ioi q r
    arg1 <- pure xs
    (_:_) <- pure xs
    pure (arg1)
   )
  pure (arg1)

{- queens2/2
queens2 arg1 arg2 :- ((cqueens dat data0 out, data0 = [], arg1 = dat, arg2 = out)).
constraints:
~(arg1[0,2] & dat[0,2])
~(arg2[0,3] & out[0,3])
~(dat[0,0] & dat[0,2])
~(data0[0,0] & data0[0,1])
~(out[0,0] & out[0,3])
(dat[0,0] | dat[0,2])
(data0[0,0] | data0[0,1])
(out[0,0] | out[0,3])
((dat[0,0] & (~data0[0,0] & ~out[0,0])) | ((~dat[0,0] & (~data0[0,0] & out[0,0])) | (~dat[0,0] & (~data0[0,0] & ~out[0,0]))))
(arg1[0] <-> arg1[0,2])
(arg1[] <-> arg1[0])
(arg2[0] <-> arg2[0,3])
(arg2[] <-> arg2[0])
1
-}
queens2_ii = \arg1 arg2 -> do
  -- solution: dat[0,0] data0[0,1] out[0,3] ~arg1[0,2] ~arg1[0] ~arg1[] ~arg2[0,3] ~arg2[0] ~arg2[] ~dat[0,2] ~data0[0,0] ~out[0,0]
  () <- (do
    out <- pure arg2
    data0 <- pure []
    (dat) <- cqueens_oii data0 out
    guard $ arg1 == dat
    pure ()
   )
  pure ()

queens2_io = \arg1 -> do
  -- solution: arg2[0,3] arg2[0] arg2[] dat[0,2] data0[0,1] out[0,0] ~arg1[0,2] ~arg1[0] ~arg1[] ~dat[0,0] ~data0[0,0] ~out[0,3]
  (arg2) <- (do
    dat <- pure arg1
    data0 <- pure []
    (out) <- cqueens_iio dat data0
    arg2 <- pure out
    pure (arg2)
   )
  pure (arg2)

queens2_oi = \arg2 -> do
  -- solution: arg1[0,2] arg1[0] arg1[] dat[0,0] data0[0,1] out[0,3] ~arg2[0,3] ~arg2[0] ~arg2[] ~dat[0,2] ~data0[0,0] ~out[0,0]
  (arg1) <- (do
    out <- pure arg2
    data0 <- pure []
    (dat) <- cqueens_oii data0 out
    arg1 <- pure dat
    pure (arg1)
   )
  pure (arg1)
