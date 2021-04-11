{-# LANGUAGE NoMonomorphismRestriction #-}
module Kiselyov where

import Control.Applicative
import Control.Monad.Logic
import Control.Monad.Logic.Moded.Prelude
import Data.List
import Data.MemoTrie

{- nat/1
nat arg1 :- ((arg1 = 0); (nat n, succ n n', arg1 = n')).
constraints:
~(arg1[1,2] & n'[1,2])
~(n'[1,1] & n'[1,2])
~(n[1,0] & n[1,1])
(n'[1,1] | n'[1,2])
(n[1,0] | n[1,1])
((n[1,1] & ~n'[1,1]) | ((~n[1,1] & n'[1,1]) | (~n[1,1] & ~n'[1,1])))
(arg1[0] <-> arg1[0,0])
(arg1[1] <-> arg1[1,2])
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(n[1,0] <-> arg1[])
1
-}
nat_i = \arg1 -> do
  -- solution: n'[1,2] n[1,1] ~arg1[0,0] ~arg1[0] ~arg1[1,2] ~arg1[1] ~arg1[] ~n'[1,1] ~n[1,0]
  () <- (do
    guard $ arg1 == 0
    pure ()
   ) <|> (do
    n' <- pure arg1
    (n) <- succ_oi n'
    () <- nat_i n
    pure ()
   )
  pure ()

nat_o = do
  -- solution: arg1[0,0] arg1[0] arg1[1,2] arg1[1] arg1[] n'[1,1] n[1,0] ~n'[1,2] ~n[1,1]
  (arg1) <- (do
    arg1 <- pure 0
    pure (arg1)
   ) <|> (do
    (n) <- nat_o 
    (n') <- succ_io n
    arg1 <- pure n'
    pure (arg1)
   )
  pure (arg1)

{- elem/2
elem arg1 arg2 :- ((arg2 = x:_, arg1 = x); (arg2 = _:xs, elem x xs, arg1 = x)).
constraints:
x[0,0]
xs[1,0]
~arg2[1,0]
~(arg1[0,1] & x[0,1])
~(arg1[1,2] & x[1,2])
~(arg2[0,0] & x[0,0])
~(x[0,0] & x[0,1])
~(x[1,1] & x[1,2])
~(xs[1,0] & xs[1,1])
(x[0,0] | x[0,1])
(x[1,1] | x[1,2])
(xs[1,0] | xs[1,1])
(arg1[0] <-> arg1[0,1])
(arg1[1] <-> arg1[1,2])
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg2[0] <-> arg2[0,0])
(arg2[1] <-> arg2[1,0])
(arg2[] <-> arg2[0])
(arg2[] <-> arg2[1])
(x[1,1] <-> arg1[])
(xs[1,1] <-> arg2[])
1
-}
elem_ii = \arg1 arg2 -> do
  -- solution: x[0,0] x[1,2] xs[1,0] ~arg1[0,1] ~arg1[0] ~arg1[1,2] ~arg1[1] ~arg1[] ~arg2[0,0] ~arg2[0] ~arg2[1,0] ~arg2[1] ~arg2[] ~x[0,1] ~x[1,1] ~xs[1,1]
  () <- (do
    (x:_) <- pure arg2
    guard $ arg1 == x
    pure ()
   ) <|> (do
    x <- pure arg1
    (_:xs) <- pure arg2
    () <- elem_ii x xs
    pure ()
   )
  pure ()

elem_oi = \arg2 -> do
  -- solution: arg1[0,1] arg1[0] arg1[1,2] arg1[1] arg1[] x[0,0] x[1,1] xs[1,0] ~arg2[0,0] ~arg2[0] ~arg2[1,0] ~arg2[1] ~arg2[] ~x[0,1] ~x[1,2] ~xs[1,1]
  (arg1) <- (do
    (x:_) <- pure arg2
    arg1 <- pure x
    pure (arg1)
   ) <|> (do
    (_:xs) <- pure arg2
    (x) <- elem_oi xs
    arg1 <- pure x
    pure (arg1)
   )
  pure (arg1)

{- pythag/3
pythag arg1 arg2 arg3 :- ((nat i, (>) i data0, data0 = 0, nat j, (>) j data1, data1 = 0, nat k, (>) k data2, data2 = 0, (<) i j, timesInt i0 i1 ii, i0 = i, i1 = i, timesInt j2 j3 jj, j2 = j, j3 = j, timesInt k4 k5 kk, k4 = k, k5 = k, plus ii jj kk, arg1 = i, arg2 = j, arg3 = k)).
constraints:
~(arg1[0,20] & i[0,20])
~(arg2[0,21] & j[0,21])
~(arg3[0,22] & k[0,22])
~(data0[0,1] & data0[0,2])
~(data1[0,4] & data1[0,5])
~(data2[0,7] & data2[0,8])
~(i0[0,10] & i0[0,11])
~(i0[0,11] & i[0,11])
~(i1[0,10] & i1[0,12])
~(i1[0,12] & i[0,12])
~(i[0,0] & i[0,11])
~(i[0,0] & i[0,12])
~(i[0,0] & i[0,1])
~(i[0,0] & i[0,20])
~(i[0,0] & i[0,9])
~(i[0,11] & i[0,12])
~(i[0,11] & i[0,1])
~(i[0,11] & i[0,20])
~(i[0,11] & i[0,9])
~(i[0,12] & i[0,1])
~(i[0,12] & i[0,20])
~(i[0,12] & i[0,9])
~(i[0,1] & i[0,20])
~(i[0,1] & i[0,9])
~(i[0,20] & i[0,9])
~(ii[0,10] & ii[0,19])
~(j2[0,13] & j2[0,14])
~(j2[0,14] & j[0,14])
~(j3[0,13] & j3[0,15])
~(j3[0,15] & j[0,15])
~(j[0,14] & j[0,15])
~(j[0,14] & j[0,21])
~(j[0,14] & j[0,3])
~(j[0,14] & j[0,4])
~(j[0,14] & j[0,9])
~(j[0,15] & j[0,21])
~(j[0,15] & j[0,3])
~(j[0,15] & j[0,4])
~(j[0,15] & j[0,9])
~(j[0,21] & j[0,3])
~(j[0,21] & j[0,4])
~(j[0,21] & j[0,9])
~(j[0,3] & j[0,4])
~(j[0,3] & j[0,9])
~(j[0,4] & j[0,9])
~(jj[0,13] & jj[0,19])
~(k4[0,16] & k4[0,17])
~(k4[0,17] & k[0,17])
~(k5[0,16] & k5[0,18])
~(k5[0,18] & k[0,18])
~(k[0,17] & k[0,18])
~(k[0,17] & k[0,22])
~(k[0,17] & k[0,6])
~(k[0,17] & k[0,7])
~(k[0,18] & k[0,22])
~(k[0,18] & k[0,6])
~(k[0,18] & k[0,7])
~(k[0,22] & k[0,6])
~(k[0,22] & k[0,7])
~(k[0,6] & k[0,7])
~(kk[0,16] & kk[0,19])
(~i[0,1] & ~data0[0,1])
(~i[0,9] & ~j[0,9])
(~j[0,4] & ~data1[0,4])
(~k[0,7] & ~data2[0,7])
(data0[0,1] | data0[0,2])
(data1[0,4] | data1[0,5])
(data2[0,7] | data2[0,8])
(i0[0,10] | i0[0,11])
(i1[0,10] | i1[0,12])
(i[0,0] | ~i[0,0])
(i[0,0] | (i[0,1] | (i[0,9] | (i[0,11] | (i[0,12] | i[0,20])))))
(ii[0,10] | ii[0,19])
(j2[0,13] | j2[0,14])
(j3[0,13] | j3[0,15])
(j[0,3] | ~j[0,3])
(j[0,3] | (j[0,4] | (j[0,9] | (j[0,14] | (j[0,15] | j[0,21])))))
(jj[0,13] | jj[0,19])
(k4[0,16] | k4[0,17])
(k5[0,16] | k5[0,18])
(k[0,6] | ~k[0,6])
(k[0,6] | (k[0,7] | (k[0,17] | (k[0,18] | k[0,22]))))
(kk[0,16] | kk[0,19])
((i0[0,10] & (~i1[0,10] & ~ii[0,10])) | ((~i0[0,10] & (i1[0,10] & ~ii[0,10])) | (~i0[0,10] & (~i1[0,10] & ii[0,10]))))
((ii[0,19] & (~jj[0,19] & ~kk[0,19])) | ((~ii[0,19] & (jj[0,19] & ~kk[0,19])) | (~ii[0,19] & (~jj[0,19] & kk[0,19]))))
((j2[0,13] & (~j3[0,13] & ~jj[0,13])) | ((~j2[0,13] & (j3[0,13] & ~jj[0,13])) | (~j2[0,13] & (~j3[0,13] & jj[0,13]))))
((k4[0,16] & (~k5[0,16] & ~kk[0,16])) | ((~k4[0,16] & (k5[0,16] & ~kk[0,16])) | (~k4[0,16] & (~k5[0,16] & kk[0,16]))))
(arg1[0] <-> arg1[0,20])
(arg1[] <-> arg1[0])
(arg2[0] <-> arg2[0,21])
(arg2[] <-> arg2[0])
(arg3[0] <-> arg3[0,22])
(arg3[] <-> arg3[0])
1
-}
-- mode ordering failure, cyclic dependency: [10] timesInt i0::in i1::out ii::in -> [12] i1::in = i::out -> [11] i0::out = i::in
pythag_iii = \arg1 arg2 arg3 -> do
  -- solution: data0[0,2] data1[0,5] data2[0,8] i0[0,10] i1[0,12] i[0,0] ii[0,19] j2[0,14] j3[0,15] j[0,21] jj[0,13] k4[0,17] k5[0,18] k[0,22] kk[0,16] ~arg1[0,20] ~arg1[0] ~arg1[] ~arg2[0,21] ~arg2[0] ~arg2[] ~arg3[0,22] ~arg3[0] ~arg3[] ~data0[0,1] ~data1[0,4] ~data2[0,7] ~i0[0,11] ~i1[0,10] ~i[0,11] ~i[0,12] ~i[0,1] ~i[0,20] ~i[0,9] ~ii[0,10] ~j2[0,13] ~j3[0,13] ~j[0,14] ~j[0,15] ~j[0,3] ~j[0,4] ~j[0,9] ~jj[0,19] ~k4[0,16] ~k5[0,16] ~k[0,17] ~k[0,18] ~k[0,6] ~k[0,7] ~kk[0,19]
  () <- (do
    j <- pure arg2
    k <- pure arg3
    j2 <- pure j
    j3 <- pure j
    k4 <- pure k
    k5 <- pure k
    data0 <- pure 0
    data1 <- pure 0
    data2 <- pure 0
    guard $ (>) j data1
    guard $ (>) k data2
    () <- nat_i j
    () <- nat_i k
    (i) <- nat_o 
    guard $ arg1 == i
    i1 <- pure i
    guard $ (<) i j
    guard $ (>) i data0
    (jj) <- timesInt_iio j2 j3
    (kk) <- timesInt_iio k4 k5
    (ii) <- plus_oii jj kk
    (i0) <- timesInt_oii i1 ii
    guard $ i0 == i
    pure ()
   )
  pure ()

pythag_iio = \arg1 arg2 -> do
  -- solution: arg3[0,22] arg3[0] arg3[] data0[0,2] data1[0,5] data2[0,8] i0[0,10] i1[0,12] i[0,0] ii[0,19] j2[0,14] j3[0,15] j[0,21] jj[0,13] k4[0,17] k5[0,18] k[0,6] kk[0,16] ~arg1[0,20] ~arg1[0] ~arg1[] ~arg2[0,21] ~arg2[0] ~arg2[] ~data0[0,1] ~data1[0,4] ~data2[0,7] ~i0[0,11] ~i1[0,10] ~i[0,11] ~i[0,12] ~i[0,1] ~i[0,20] ~i[0,9] ~ii[0,10] ~j2[0,13] ~j3[0,13] ~j[0,14] ~j[0,15] ~j[0,3] ~j[0,4] ~j[0,9] ~jj[0,19] ~k4[0,16] ~k5[0,16] ~k[0,17] ~k[0,18] ~k[0,22] ~k[0,7] ~kk[0,19]
  (arg3) <- (do
    j <- pure arg2
    j2 <- pure j
    j3 <- pure j
    data0 <- pure 0
    data1 <- pure 0
    data2 <- pure 0
    guard $ (>) j data1
    () <- nat_i j
    (i) <- nat_o 
    guard $ arg1 == i
    i1 <- pure i
    guard $ (<) i j
    guard $ (>) i data0
    (k) <- nat_o 
    arg3 <- pure k
    k4 <- pure k
    k5 <- pure k
    guard $ (>) k data2
    (jj) <- timesInt_iio j2 j3
    (kk) <- timesInt_iio k4 k5
    (ii) <- plus_oii jj kk
    (i0) <- timesInt_oii i1 ii
    guard $ i0 == i
    pure (arg3)
   )
  pure (arg3)

pythag_ioi = \arg1 arg3 -> do
  -- solution: arg2[0,21] arg2[0] arg2[] data0[0,2] data1[0,5] data2[0,8] i0[0,10] i1[0,12] i[0,0] ii[0,19] j2[0,14] j3[0,15] j[0,3] jj[0,13] k4[0,17] k5[0,18] k[0,22] kk[0,16] ~arg1[0,20] ~arg1[0] ~arg1[] ~arg3[0,22] ~arg3[0] ~arg3[] ~data0[0,1] ~data1[0,4] ~data2[0,7] ~i0[0,11] ~i1[0,10] ~i[0,11] ~i[0,12] ~i[0,1] ~i[0,20] ~i[0,9] ~ii[0,10] ~j2[0,13] ~j3[0,13] ~j[0,14] ~j[0,15] ~j[0,21] ~j[0,4] ~j[0,9] ~jj[0,19] ~k4[0,16] ~k5[0,16] ~k[0,17] ~k[0,18] ~k[0,6] ~k[0,7] ~kk[0,19]
  (arg2) <- (do
    k <- pure arg3
    k4 <- pure k
    k5 <- pure k
    data0 <- pure 0
    data1 <- pure 0
    data2 <- pure 0
    guard $ (>) k data2
    () <- nat_i k
    (i) <- nat_o 
    guard $ arg1 == i
    i1 <- pure i
    guard $ (>) i data0
    (j) <- nat_o 
    arg2 <- pure j
    j2 <- pure j
    j3 <- pure j
    guard $ (<) i j
    guard $ (>) j data1
    (jj) <- timesInt_iio j2 j3
    (kk) <- timesInt_iio k4 k5
    (ii) <- plus_oii jj kk
    (i0) <- timesInt_oii i1 ii
    guard $ i0 == i
    pure (arg2)
   )
  pure (arg2)

pythag_ioo = \arg1 -> do
  -- solution: arg2[0,21] arg2[0] arg2[] arg3[0,22] arg3[0] arg3[] data0[0,2] data1[0,5] data2[0,8] i0[0,10] i1[0,12] i[0,0] ii[0,19] j2[0,14] j3[0,15] j[0,3] jj[0,13] k4[0,17] k5[0,18] k[0,6] kk[0,16] ~arg1[0,20] ~arg1[0] ~arg1[] ~data0[0,1] ~data1[0,4] ~data2[0,7] ~i0[0,11] ~i1[0,10] ~i[0,11] ~i[0,12] ~i[0,1] ~i[0,20] ~i[0,9] ~ii[0,10] ~j2[0,13] ~j3[0,13] ~j[0,14] ~j[0,15] ~j[0,21] ~j[0,4] ~j[0,9] ~jj[0,19] ~k4[0,16] ~k5[0,16] ~k[0,17] ~k[0,18] ~k[0,22] ~k[0,7] ~kk[0,19]
  (arg2,arg3) <- (do
    data0 <- pure 0
    data1 <- pure 0
    data2 <- pure 0
    (i) <- nat_o 
    guard $ arg1 == i
    i1 <- pure i
    guard $ (>) i data0
    (j) <- nat_o 
    arg2 <- pure j
    j2 <- pure j
    j3 <- pure j
    guard $ (<) i j
    guard $ (>) j data1
    (k) <- nat_o 
    arg3 <- pure k
    k4 <- pure k
    k5 <- pure k
    guard $ (>) k data2
    (jj) <- timesInt_iio j2 j3
    (kk) <- timesInt_iio k4 k5
    (ii) <- plus_oii jj kk
    (i0) <- timesInt_oii i1 ii
    guard $ i0 == i
    pure (arg2,arg3)
   )
  pure (arg2,arg3)

pythag_oii = \arg2 arg3 -> do
  -- solution: arg1[0,20] arg1[0] arg1[] data0[0,2] data1[0,5] data2[0,8] i0[0,10] i1[0,12] i[0,0] ii[0,19] j2[0,14] j3[0,15] j[0,21] jj[0,13] k4[0,17] k5[0,18] k[0,22] kk[0,16] ~arg2[0,21] ~arg2[0] ~arg2[] ~arg3[0,22] ~arg3[0] ~arg3[] ~data0[0,1] ~data1[0,4] ~data2[0,7] ~i0[0,11] ~i1[0,10] ~i[0,11] ~i[0,12] ~i[0,1] ~i[0,20] ~i[0,9] ~ii[0,10] ~j2[0,13] ~j3[0,13] ~j[0,14] ~j[0,15] ~j[0,3] ~j[0,4] ~j[0,9] ~jj[0,19] ~k4[0,16] ~k5[0,16] ~k[0,17] ~k[0,18] ~k[0,6] ~k[0,7] ~kk[0,19]
  (arg1) <- (do
    j <- pure arg2
    k <- pure arg3
    j2 <- pure j
    j3 <- pure j
    k4 <- pure k
    k5 <- pure k
    data0 <- pure 0
    data1 <- pure 0
    data2 <- pure 0
    guard $ (>) j data1
    guard $ (>) k data2
    () <- nat_i j
    () <- nat_i k
    (i) <- nat_o 
    arg1 <- pure i
    i1 <- pure i
    guard $ (<) i j
    guard $ (>) i data0
    (jj) <- timesInt_iio j2 j3
    (kk) <- timesInt_iio k4 k5
    (ii) <- plus_oii jj kk
    (i0) <- timesInt_oii i1 ii
    guard $ i0 == i
    pure (arg1)
   )
  pure (arg1)

pythag_oio = \arg2 -> do
  -- solution: arg1[0,20] arg1[0] arg1[] arg3[0,22] arg3[0] arg3[] data0[0,2] data1[0,5] data2[0,8] i0[0,10] i1[0,12] i[0,0] ii[0,19] j2[0,14] j3[0,15] j[0,21] jj[0,13] k4[0,17] k5[0,18] k[0,6] kk[0,16] ~arg2[0,21] ~arg2[0] ~arg2[] ~data0[0,1] ~data1[0,4] ~data2[0,7] ~i0[0,11] ~i1[0,10] ~i[0,11] ~i[0,12] ~i[0,1] ~i[0,20] ~i[0,9] ~ii[0,10] ~j2[0,13] ~j3[0,13] ~j[0,14] ~j[0,15] ~j[0,3] ~j[0,4] ~j[0,9] ~jj[0,19] ~k4[0,16] ~k5[0,16] ~k[0,17] ~k[0,18] ~k[0,22] ~k[0,7] ~kk[0,19]
  (arg1,arg3) <- (do
    j <- pure arg2
    j2 <- pure j
    j3 <- pure j
    data0 <- pure 0
    data1 <- pure 0
    data2 <- pure 0
    guard $ (>) j data1
    () <- nat_i j
    (i) <- nat_o 
    arg1 <- pure i
    i1 <- pure i
    guard $ (<) i j
    guard $ (>) i data0
    (k) <- nat_o 
    arg3 <- pure k
    k4 <- pure k
    k5 <- pure k
    guard $ (>) k data2
    (jj) <- timesInt_iio j2 j3
    (kk) <- timesInt_iio k4 k5
    (ii) <- plus_oii jj kk
    (i0) <- timesInt_oii i1 ii
    guard $ i0 == i
    pure (arg1,arg3)
   )
  pure (arg1,arg3)

pythag_ooi = \arg3 -> do
  -- solution: arg1[0,20] arg1[0] arg1[] arg2[0,21] arg2[0] arg2[] data0[0,2] data1[0,5] data2[0,8] i0[0,10] i1[0,12] i[0,0] ii[0,19] j2[0,14] j3[0,15] j[0,3] jj[0,13] k4[0,17] k5[0,18] k[0,22] kk[0,16] ~arg3[0,22] ~arg3[0] ~arg3[] ~data0[0,1] ~data1[0,4] ~data2[0,7] ~i0[0,11] ~i1[0,10] ~i[0,11] ~i[0,12] ~i[0,1] ~i[0,20] ~i[0,9] ~ii[0,10] ~j2[0,13] ~j3[0,13] ~j[0,14] ~j[0,15] ~j[0,21] ~j[0,4] ~j[0,9] ~jj[0,19] ~k4[0,16] ~k5[0,16] ~k[0,17] ~k[0,18] ~k[0,6] ~k[0,7] ~kk[0,19]
  (arg1,arg2) <- (do
    k <- pure arg3
    k4 <- pure k
    k5 <- pure k
    data0 <- pure 0
    data1 <- pure 0
    data2 <- pure 0
    guard $ (>) k data2
    () <- nat_i k
    (i) <- nat_o 
    arg1 <- pure i
    i1 <- pure i
    guard $ (>) i data0
    (j) <- nat_o 
    arg2 <- pure j
    j2 <- pure j
    j3 <- pure j
    guard $ (<) i j
    guard $ (>) j data1
    (jj) <- timesInt_iio j2 j3
    (kk) <- timesInt_iio k4 k5
    (ii) <- plus_oii jj kk
    (i0) <- timesInt_oii i1 ii
    guard $ i0 == i
    pure (arg1,arg2)
   )
  pure (arg1,arg2)

pythag_ooo = do
  -- solution: arg1[0,20] arg1[0] arg1[] arg2[0,21] arg2[0] arg2[] arg3[0,22] arg3[0] arg3[] data0[0,2] data1[0,5] data2[0,8] i0[0,10] i1[0,12] i[0,0] ii[0,19] j2[0,14] j3[0,15] j[0,3] jj[0,13] k4[0,17] k5[0,18] k[0,6] kk[0,16] ~data0[0,1] ~data1[0,4] ~data2[0,7] ~i0[0,11] ~i1[0,10] ~i[0,11] ~i[0,12] ~i[0,1] ~i[0,20] ~i[0,9] ~ii[0,10] ~j2[0,13] ~j3[0,13] ~j[0,14] ~j[0,15] ~j[0,21] ~j[0,4] ~j[0,9] ~jj[0,19] ~k4[0,16] ~k5[0,16] ~k[0,17] ~k[0,18] ~k[0,22] ~k[0,7] ~kk[0,19]
  (arg1,arg2,arg3) <- (do
    data0 <- pure 0
    data1 <- pure 0
    data2 <- pure 0
    (i) <- nat_o 
    arg1 <- pure i
    i1 <- pure i
    guard $ (>) i data0
    (j) <- nat_o 
    arg2 <- pure j
    j2 <- pure j
    j3 <- pure j
    guard $ (<) i j
    guard $ (>) j data1
    (k) <- nat_o 
    arg3 <- pure k
    k4 <- pure k
    k5 <- pure k
    guard $ (>) k data2
    (jj) <- timesInt_iio j2 j3
    (kk) <- timesInt_iio k4 k5
    (ii) <- plus_oii jj kk
    (i0) <- timesInt_oii i1 ii
    guard $ i0 == i
    pure (arg1,arg2,arg3)
   )
  pure (arg1,arg2,arg3)

{- triang/2
triang arg1 arg2 :- ((succ n n', times n n' nn', div nn' data0 r, data0 = 2, arg1 = n, arg2 = r)).
constraints:
~(arg1[0,4] & n[0,4])
~(arg2[0,5] & r[0,5])
~(data0[0,2] & data0[0,3])
~(n'[0,0] & n'[0,1])
~(n[0,0] & n[0,1])
~(n[0,0] & n[0,4])
~(n[0,1] & n[0,4])
~(nn'[0,1] & nn'[0,2])
~(r[0,2] & r[0,5])
(data0[0,2] | data0[0,3])
(n'[0,0] | n'[0,1])
(n[0,0] | (n[0,1] | n[0,4]))
(nn'[0,1] | nn'[0,2])
(r[0,2] | r[0,5])
((n[0,0] & ~n'[0,0]) | ((~n[0,0] & n'[0,0]) | (~n[0,0] & ~n'[0,0])))
((n[0,1] & (~n'[0,1] & ~nn'[0,1])) | ((~n[0,1] & (n'[0,1] & ~nn'[0,1])) | (~n[0,1] & (~n'[0,1] & nn'[0,1]))))
((~nn'[0,2] & (~data0[0,2] & r[0,2])) | (~nn'[0,2] & (~data0[0,2] & ~r[0,2])))
(arg1[0] <-> arg1[0,4])
(arg1[] <-> arg1[0])
(arg2[0] <-> arg2[0,5])
(arg2[] <-> arg2[0])
1
-}
triang_ii = \arg1 arg2 -> do
  -- solution: data0[0,3] n'[0,0] n[0,4] nn'[0,1] r[0,2] ~arg1[0,4] ~arg1[0] ~arg1[] ~arg2[0,5] ~arg2[0] ~arg2[] ~data0[0,2] ~n'[0,1] ~n[0,0] ~n[0,1] ~nn'[0,2] ~r[0,5]
  () <- (do
    n <- pure arg1
    data0 <- pure 2
    (n') <- succ_io n
    (nn') <- times_iio n n'
    (r) <- div_iio nn' data0
    guard $ arg2 == r
    pure ()
   )
  pure ()

triang_io = \arg1 -> do
  -- solution: arg2[0,5] arg2[0] arg2[] data0[0,3] n'[0,0] n[0,4] nn'[0,1] r[0,2] ~arg1[0,4] ~arg1[0] ~arg1[] ~data0[0,2] ~n'[0,1] ~n[0,0] ~n[0,1] ~nn'[0,2] ~r[0,5]
  (arg2) <- (do
    n <- pure arg1
    data0 <- pure 2
    (n') <- succ_io n
    (nn') <- times_iio n n'
    (r) <- div_iio nn' data0
    arg2 <- pure r
    pure (arg2)
   )
  pure (arg2)

{- ptriang/1
ptriang arg1 :- ((elem k data2, data0 = 1, data1 = 30, data2 = .. data0 data1, elem i data4, data3 = 1, data4 = .. data3 k, elem j data6, data5 = 1, data6 = .. data5 i, triang i ti, triang j tj, triang k tk, plus ti tj tk, arg1 = k)).
constraints:
~(arg1[0,14] & k[0,14])
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
~(i[0,10] & i[0,4])
~(i[0,10] & i[0,9])
~(i[0,4] & i[0,9])
~(j[0,11] & j[0,7])
~(k[0,0] & k[0,12])
~(k[0,0] & k[0,14])
~(k[0,0] & k[0,6])
~(k[0,12] & k[0,14])
~(k[0,12] & k[0,6])
~(k[0,14] & k[0,6])
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
(k[0,0] | (k[0,6] | (k[0,12] | k[0,14])))
(ti[0,10] | ti[0,13])
(tj[0,11] | tj[0,13])
(tk[0,12] | tk[0,13])
((i[0,4] & ~data4[0,4]) | (~i[0,4] & ~data4[0,4]))
((j[0,7] & ~data6[0,7]) | (~j[0,7] & ~data6[0,7]))
((k[0,0] & ~data2[0,0]) | (~k[0,0] & ~data2[0,0]))
((ti[0,13] & (~tj[0,13] & ~tk[0,13])) | ((~ti[0,13] & (tj[0,13] & ~tk[0,13])) | (~ti[0,13] & (~tj[0,13] & tk[0,13]))))
((~i[0,10] & ti[0,10]) | (~i[0,10] & ~ti[0,10]))
((~j[0,11] & tj[0,11]) | (~j[0,11] & ~tj[0,11]))
((~k[0,12] & tk[0,12]) | (~k[0,12] & ~tk[0,12]))
(arg1[0] <-> arg1[0,14])
(arg1[] <-> arg1[0])
(data0[0,3] <-> data1[0,3])
(data3[0,6] <-> k[0,6])
(data5[0,9] <-> i[0,9])
1
-}
ptriang_i = \arg1 -> choose . nub . observeAll $ do
  -- solution: data0[0,1] data1[0,2] data2[0,3] data3[0,5] data4[0,6] data5[0,8] data6[0,9] i[0,4] j[0,7] k[0,0] ti[0,10] tj[0,11] tk[0,13] ~arg1[0,14] ~arg1[0] ~arg1[] ~data0[0,3] ~data1[0,3] ~data2[0,0] ~data3[0,6] ~data4[0,4] ~data5[0,9] ~data6[0,7] ~i[0,10] ~i[0,9] ~j[0,11] ~k[0,12] ~k[0,14] ~k[0,6] ~ti[0,13] ~tj[0,13] ~tk[0,12]
  () <- (do
    data0 <- pure 1
    data3 <- pure 1
    data5 <- pure 1
    data1 <- pure 30
    data2 <- pure [data0..data1]
    (k) <- elem_oi data2
    guard $ arg1 == k
    data4 <- pure [data3..k]
    (i) <- elem_oi data4
    data6 <- pure [data5..i]
    (j) <- elem_oi data6
    (ti) <- triang_io i
    (tj) <- triang_io j
    (tk) <- plus_iio ti tj
    () <- triang_ii k tk
    pure ()
   )
  pure ()

ptriang_o = choose . nub . observeAll $ do
  -- solution: arg1[0,14] arg1[0] arg1[] data0[0,1] data1[0,2] data2[0,3] data3[0,5] data4[0,6] data5[0,8] data6[0,9] i[0,4] j[0,7] k[0,0] ti[0,10] tj[0,11] tk[0,13] ~data0[0,3] ~data1[0,3] ~data2[0,0] ~data3[0,6] ~data4[0,4] ~data5[0,9] ~data6[0,7] ~i[0,10] ~i[0,9] ~j[0,11] ~k[0,12] ~k[0,14] ~k[0,6] ~ti[0,13] ~tj[0,13] ~tk[0,12]
  (arg1) <- (do
    data0 <- pure 1
    data3 <- pure 1
    data5 <- pure 1
    data1 <- pure 30
    data2 <- pure [data0..data1]
    (k) <- elem_oi data2
    arg1 <- pure k
    data4 <- pure [data3..k]
    (i) <- elem_oi data4
    data6 <- pure [data5..i]
    (j) <- elem_oi data6
    (ti) <- triang_io i
    (tj) <- triang_io j
    (tk) <- plus_iio ti tj
    () <- triang_ii k tk
    pure (arg1)
   )
  pure (arg1)

{- stepN/2
stepN arg1 arg2 :- ((arg1 = 0, arg2 = 0); ((>) n' data0, data0 = 0, succ n n', stepN n i, succ i i', elem r data2, data1 = [], data2 = i:i':data1, arg1 = n', arg2 = r)).
constraints:
~(arg1[1,8] & n'[1,8])
~(arg2[1,9] & r[1,9])
~(data0[1,0] & data0[1,1])
~(data1[1,6] & data1[1,7])
~(data2[1,5] & data2[1,7])
~(data2[1,7] & i[1,7])
~(i'[1,4] & i'[1,7])
~(i[1,3] & i[1,4])
~(i[1,3] & i[1,7])
~(i[1,4] & i[1,7])
~(n'[1,0] & n'[1,2])
~(n'[1,0] & n'[1,8])
~(n'[1,2] & n'[1,8])
~(n[1,2] & n[1,3])
~(r[1,5] & r[1,9])
(~n'[1,0] & ~data0[1,0])
(data0[1,0] | data0[1,1])
(data1[1,6] | data1[1,7])
(data2[1,5] | data2[1,7])
(i'[1,4] | i'[1,7])
(i[1,3] | (i[1,4] | i[1,7]))
(n'[1,0] | (n'[1,2] | n'[1,8]))
(n[1,2] | n[1,3])
(r[1,5] | r[1,9])
((i[1,4] & ~i'[1,4]) | ((~i[1,4] & i'[1,4]) | (~i[1,4] & ~i'[1,4])))
((n[1,2] & ~n'[1,2]) | ((~n[1,2] & n'[1,2]) | (~n[1,2] & ~n'[1,2])))
((r[1,5] & ~data2[1,5]) | (~r[1,5] & ~data2[1,5]))
(arg1[0] <-> arg1[0,0])
(arg1[1] <-> arg1[1,8])
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg2[0] <-> arg2[0,1])
(arg2[1] <-> arg2[1,9])
(arg2[] <-> arg2[0])
(arg2[] <-> arg2[1])
(i[1,3] <-> arg2[])
(i[1,7] <-> data1[1,7])
(i[1,7] <-> i'[1,7])
(n[1,3] <-> arg1[])
1
-}
stepN_io = \arg1 -> choose . nub . observeAll $ do
  -- solution: arg2[0,1] arg2[0] arg2[1,9] arg2[1] arg2[] data0[1,1] data1[1,6] data2[1,7] i'[1,4] i[1,3] n'[1,8] n[1,2] r[1,5] ~arg1[0,0] ~arg1[0] ~arg1[1,8] ~arg1[1] ~arg1[] ~data0[1,0] ~data1[1,7] ~data2[1,5] ~i'[1,7] ~i[1,4] ~i[1,7] ~n'[1,0] ~n'[1,2] ~n[1,3] ~r[1,9]
  (arg2) <- (do
    guard $ arg1 == 0
    arg2 <- pure 0
    pure (arg2)
   ) <|> (do
    n' <- pure arg1
    data0 <- pure 0
    data1 <- pure []
    guard $ (>) n' data0
    (n) <- succ_oi n'
    (i) <- stepN_io n
    (i') <- succ_io i
    data2 <- pure (i:i':data1)
    (r) <- elem_oi data2
    arg2 <- pure r
    pure (arg2)
   )
  pure (arg2)

stepN_oo = choose . nub . observeAll $ do
  -- solution: arg1[0,0] arg1[0] arg1[1,8] arg1[1] arg1[] arg2[0,1] arg2[0] arg2[1,9] arg2[1] arg2[] data0[1,1] data1[1,6] data2[1,7] i'[1,4] i[1,3] n'[1,2] n[1,3] r[1,5] ~data0[1,0] ~data1[1,7] ~data2[1,5] ~i'[1,7] ~i[1,4] ~i[1,7] ~n'[1,0] ~n'[1,8] ~n[1,2] ~r[1,9]
  (arg1,arg2) <- (do
    arg1 <- pure 0
    arg2 <- pure 0
    pure (arg1,arg2)
   ) <|> (do
    data0 <- pure 0
    data1 <- pure []
    (n,i) <- stepN_oo 
    (i') <- succ_io i
    data2 <- pure (i:i':data1)
    (r) <- elem_oi data2
    arg2 <- pure r
    (n') <- succ_io n
    arg1 <- pure n'
    guard $ (>) n' data0
    pure (arg1,arg2)
   )
  pure (arg1,arg2)

{- test/1
test arg1 :- ((arg1 = 10); (arg1 = 20); (arg1 = 30)).
constraints:
(arg1[0] <-> arg1[0,0])
(arg1[1] <-> arg1[1,0])
(arg1[2] <-> arg1[2,0])
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg1[] <-> arg1[2])
-}
test_i = \arg1 -> do
  -- solution: ~arg1[0,0] ~arg1[0] ~arg1[1,0] ~arg1[1] ~arg1[2,0] ~arg1[2] ~arg1[]
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

test_o = do
  -- solution: arg1[0,0] arg1[0] arg1[1,0] arg1[1] arg1[2,0] arg1[2] arg1[]
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
  pure (arg1)

{- odds/1
odds arg1 :- ((arg1 = 1); (odds m, plus data0 m n, data0 = 2, arg1 = n)).
constraints:
~(arg1[1,3] & n[1,3])
~(data0[1,1] & data0[1,2])
~(m[1,0] & m[1,1])
~(n[1,1] & n[1,3])
(data0[1,1] | data0[1,2])
(m[1,0] | m[1,1])
(n[1,1] | n[1,3])
((data0[1,1] & (~m[1,1] & ~n[1,1])) | ((~data0[1,1] & (m[1,1] & ~n[1,1])) | (~data0[1,1] & (~m[1,1] & n[1,1]))))
(arg1[0] <-> arg1[0,0])
(arg1[1] <-> arg1[1,3])
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(m[1,0] <-> arg1[])
1
-}
odds_i = \arg1 -> do
  -- solution: data0[1,2] m[1,1] n[1,3] ~arg1[0,0] ~arg1[0] ~arg1[1,3] ~arg1[1] ~arg1[] ~data0[1,1] ~m[1,0] ~n[1,1]
  () <- (do
    guard $ arg1 == 1
    pure ()
   ) <|> (do
    n <- pure arg1
    data0 <- pure 2
    (m) <- plus_ioi data0 n
    () <- odds_i m
    pure ()
   )
  pure ()

odds_o = do
  -- solution: arg1[0,0] arg1[0] arg1[1,3] arg1[1] arg1[] data0[1,2] m[1,0] n[1,1] ~data0[1,1] ~m[1,1] ~n[1,3]
  (arg1) <- (do
    arg1 <- pure 1
    pure (arg1)
   ) <|> (do
    data0 <- pure 2
    (m) <- odds_o 
    (n) <- plus_iio data0 m
    arg1 <- pure n
    pure (arg1)
   )
  pure (arg1)

{- even/1
even arg1 :- ((mod n data0 data1, data0 = 2, data1 = 0, arg1 = n)).
constraints:
~(arg1[0,3] & n[0,3])
~(data0[0,0] & data0[0,1])
~(data1[0,0] & data1[0,2])
~(n[0,0] & n[0,3])
(data0[0,0] | data0[0,1])
(data1[0,0] | data1[0,2])
(n[0,0] | n[0,3])
((~n[0,0] & (~data0[0,0] & data1[0,0])) | (~n[0,0] & (~data0[0,0] & ~data1[0,0])))
(arg1[0] <-> arg1[0,3])
(arg1[] <-> arg1[0])
1
-}
even_i = \arg1 -> do
  -- solution: data0[0,1] data1[0,0] n[0,3] ~arg1[0,3] ~arg1[0] ~arg1[] ~data0[0,0] ~data1[0,2] ~n[0,0]
  () <- (do
    n <- pure arg1
    data0 <- pure 2
    (data1) <- mod_iio n data0
    guard $ data1 == 0
    pure ()
   )
  pure ()

{- oddsTest/1
oddsTest arg1 :- ((even x, ((odds x); (test x)), arg1 = x)).
constraints:
~x[0,0]
~(arg1[0,2] & x[0,2])
~(x[0,0] & x[0,1])
~(x[0,0] & x[0,2])
~(x[0,1] & x[0,2])
(x[0,0] | (x[0,1] | x[0,2]))
(x[0,1,0,0] | ~x[0,1,0,0])
(x[0,1,1,0] | ~x[0,1,1,0])
(arg1[0] <-> arg1[0,2])
(arg1[] <-> arg1[0])
(x[0,1,0] <-> x[0,1,0,0])
(x[0,1,1] <-> x[0,1,1,0])
(x[0,1] <-> x[0,1,0])
(x[0,1] <-> x[0,1,1])
1
-}
oddsTest_i = \arg1 -> do
  -- solution: x[0,1,0,0] x[0,1,0] x[0,1,1,0] x[0,1,1] x[0,1] ~arg1[0,2] ~arg1[0] ~arg1[] ~x[0,0] ~x[0,2]
  () <- (do
    (x) <- (do
      (x) <- odds_o 
      pure (x)
     ) <|> (do
      (x) <- test_o 
      pure (x)
     )
    guard $ arg1 == x
    () <- even_i x
    pure ()
   )
  pure ()

oddsTest_o = do
  -- solution: arg1[0,2] arg1[0] arg1[] x[0,1,0,0] x[0,1,0] x[0,1,1,0] x[0,1,1] x[0,1] ~x[0,0] ~x[0,2]
  (arg1) <- (do
    (x) <- (do
      (x) <- odds_o 
      pure (x)
     ) <|> (do
      (x) <- test_o 
      pure (x)
     )
    arg1 <- pure x
    () <- even_i x
    pure (arg1)
   )
  pure (arg1)

{- oddsPlus/2
oddsPlus arg1 arg2 :- ((odds a, plus a n x, arg1 = n, arg2 = x)).
constraints:
~(a[0,0] & a[0,1])
~(arg1[0,2] & n[0,2])
~(arg2[0,3] & x[0,3])
~(n[0,1] & n[0,2])
~(x[0,1] & x[0,3])
(a[0,0] | a[0,1])
(a[0,0] | ~a[0,0])
(n[0,1] | n[0,2])
(x[0,1] | x[0,3])
((a[0,1] & (~n[0,1] & ~x[0,1])) | ((~a[0,1] & (n[0,1] & ~x[0,1])) | (~a[0,1] & (~n[0,1] & x[0,1]))))
(arg1[0] <-> arg1[0,2])
(arg1[] <-> arg1[0])
(arg2[0] <-> arg2[0,3])
(arg2[] <-> arg2[0])
1
-}
oddsPlus_ii = \arg1 arg2 -> do
  -- solution: a[0,0] n[0,1] x[0,3] ~a[0,1] ~arg1[0,2] ~arg1[0] ~arg1[] ~arg2[0,3] ~arg2[0] ~arg2[] ~n[0,2] ~x[0,1]
  () <- (do
    x <- pure arg2
    (a) <- odds_o 
    (n) <- plus_ioi a x
    guard $ arg1 == n
    pure ()
   )
  pure ()

oddsPlus_io = \arg1 -> do
  -- solution: a[0,0] arg2[0,3] arg2[0] arg2[] n[0,2] x[0,1] ~a[0,1] ~arg1[0,2] ~arg1[0] ~arg1[] ~n[0,1] ~x[0,3]
  (arg2) <- (do
    n <- pure arg1
    (a) <- odds_o 
    (x) <- plus_iio a n
    arg2 <- pure x
    pure (arg2)
   )
  pure (arg2)

oddsPlus_oi = \arg2 -> do
  -- solution: a[0,0] arg1[0,2] arg1[0] arg1[] n[0,1] x[0,3] ~a[0,1] ~arg2[0,3] ~arg2[0] ~arg2[] ~n[0,2] ~x[0,1]
  (arg1) <- (do
    x <- pure arg2
    (a) <- odds_o 
    (n) <- plus_ioi a x
    arg1 <- pure n
    pure (arg1)
   )
  pure (arg1)

{- oddsPlusTest/1
oddsPlusTest arg1 :- ((oddsPlus n x, even x, ((n = 0); (n = 1)), arg1 = x)).
constraints:
~x[0,1]
~(arg1[0,3] & x[0,3])
~(n[0,0] & n[0,2])
~(x[0,0] & x[0,1])
~(x[0,0] & x[0,3])
~(x[0,1] & x[0,3])
(n[0,0] | n[0,2])
(x[0,0] | (x[0,1] | x[0,3]))
((n[0,0] & ~x[0,0]) | ((~n[0,0] & x[0,0]) | (~n[0,0] & ~x[0,0])))
(arg1[0] <-> arg1[0,3])
(arg1[] <-> arg1[0])
(n[0,2,0] <-> n[0,2,0,0])
(n[0,2,1] <-> n[0,2,1,0])
(n[0,2] <-> n[0,2,0])
(n[0,2] <-> n[0,2,1])
1
-}
oddsPlusTest_i = \arg1 -> do
  -- solution: n[0,0] x[0,3] ~arg1[0,3] ~arg1[0] ~arg1[] ~n[0,2,0,0] ~n[0,2,0] ~n[0,2,1,0] ~n[0,2,1] ~n[0,2] ~x[0,0] ~x[0,1]
  () <- (do
    x <- pure arg1
    () <- even_i x
    (n) <- oddsPlus_oi x
    () <- (do
      guard $ n == 0
      pure ()
     ) <|> (do
      guard $ n == 1
      pure ()
     )
    pure ()
   )
  pure ()

oddsPlusTest_o = do
  -- solution: arg1[0,3] arg1[0] arg1[] n[0,2,0,0] n[0,2,0] n[0,2,1,0] n[0,2,1] n[0,2] x[0,0] ~n[0,0] ~x[0,1] ~x[0,3]
  (arg1) <- (do
    (n) <- (do
      n <- pure 0
      pure (n)
     ) <|> (do
      n <- pure 1
      pure (n)
     )
    (x) <- oddsPlus_io n
    arg1 <- pure x
    () <- even_i x
    pure (arg1)
   )
  pure (arg1)

{- oddsPrime/1
oddsPrime arg1 :- ((odds n, (>) n data0, data0 = 1, succ n' n, if (elem d data2, data1 = 1, data2 = .. data1 n', (>) d data3, data3 = 1, mod n d data4, data4 = 0) then (empty) else (), arg1 = n)).
constraints:
~n'[0,4,0,2]
~n'[0,4]
~n[0,4,0,5]
~n[0,4]
~(arg1[0,5] & n[0,5])
~(d[0,4,0,0] & d[0,4,0,3])
~(d[0,4,0,0] & d[0,4,0,5])
~(d[0,4,0,3] & d[0,4,0,5])
~(data0[0,1] & data0[0,2])
~(data1[0,4,0,1] & data1[0,4,0,2])
~(data2[0,4,0,0] & data2[0,4,0,2])
~(data2[0,4,0,2] & data1[0,4,0,2])
~(data3[0,4,0,3] & data3[0,4,0,4])
~(data4[0,4,0,5] & data4[0,4,0,6])
~(n'[0,3] & n'[0,4])
~(n[0,0] & n[0,1])
~(n[0,0] & n[0,3])
~(n[0,0] & n[0,4])
~(n[0,0] & n[0,5])
~(n[0,1] & n[0,3])
~(n[0,1] & n[0,4])
~(n[0,1] & n[0,5])
~(n[0,3] & n[0,4])
~(n[0,3] & n[0,5])
~(n[0,4] & n[0,5])
(~d[0,4,0,3] & ~data3[0,4,0,3])
(~n[0,1] & ~data0[0,1])
(d[0,4,0,0] | (d[0,4,0,3] | d[0,4,0,5]))
(data0[0,1] | data0[0,2])
(data1[0,4,0,1] | data1[0,4,0,2])
(data2[0,4,0,0] | data2[0,4,0,2])
(data3[0,4,0,3] | data3[0,4,0,4])
(data4[0,4,0,5] | data4[0,4,0,6])
(n'[0,3] | n'[0,4])
(n[0,0] | ~n[0,0])
(n[0,0] | (n[0,1] | (n[0,3] | (n[0,4] | n[0,5]))))
((d[0,4,0,0] & ~data2[0,4,0,0]) | (~d[0,4,0,0] & ~data2[0,4,0,0]))
((n'[0,3] & ~n[0,3]) | ((~n'[0,3] & n[0,3]) | (~n'[0,3] & ~n[0,3])))
((~n[0,4,0,5] & (~d[0,4,0,5] & data4[0,4,0,5])) | (~n[0,4,0,5] & (~d[0,4,0,5] & ~data4[0,4,0,5])))
(arg1[0] <-> arg1[0,5])
(arg1[] <-> arg1[0])
(data1[0,4,0,2] <-> n'[0,4,0,2])
1
-}
oddsPrime_i = \arg1 -> do
  -- solution: d[0,4,0,0] data0[0,2] data1[0,4,0,1] data2[0,4,0,2] data3[0,4,0,4] data4[0,4,0,5] n'[0,3] n[0,0] ~arg1[0,5] ~arg1[0] ~arg1[] ~d[0,4,0,3] ~d[0,4,0,5] ~data0[0,1] ~data1[0,4,0,2] ~data2[0,4,0,0] ~data3[0,4,0,3] ~data4[0,4,0,6] ~n'[0,4,0,2] ~n'[0,4] ~n[0,1] ~n[0,3] ~n[0,4,0,5] ~n[0,4] ~n[0,5]
  () <- (do
    data0 <- pure 1
    (n) <- odds_o 
    guard $ arg1 == n
    guard $ (>) n data0
    (n') <- succ_oi n
    () <- ifte ((do
      data1 <- pure 1
      data2 <- pure [data1..n']
      data3 <- pure 1
      (d) <- elem_oi data2
      guard $ (>) d data3
      (data4) <- mod_iio n d
      guard $ data4 == 0
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

oddsPrime_o = do
  -- solution: arg1[0,5] arg1[0] arg1[] d[0,4,0,0] data0[0,2] data1[0,4,0,1] data2[0,4,0,2] data3[0,4,0,4] data4[0,4,0,5] n'[0,3] n[0,0] ~d[0,4,0,3] ~d[0,4,0,5] ~data0[0,1] ~data1[0,4,0,2] ~data2[0,4,0,0] ~data3[0,4,0,3] ~data4[0,4,0,6] ~n'[0,4,0,2] ~n'[0,4] ~n[0,1] ~n[0,3] ~n[0,4,0,5] ~n[0,4] ~n[0,5]
  (arg1) <- (do
    data0 <- pure 1
    (n) <- odds_o 
    arg1 <- pure n
    guard $ (>) n data0
    (n') <- succ_oi n
    () <- ifte ((do
      data1 <- pure 1
      data2 <- pure [data1..n']
      data3 <- pure 1
      (d) <- elem_oi data2
      guard $ (>) d data3
      (data4) <- mod_iio n d
      guard $ data4 == 0
      pure ()
     )) (\() -> (do
      () <- empty 
      pure ()
     )) ((do
      
      pure ()
     ))
    pure (arg1)
   )
  pure (arg1)

{- nontrivialDivisor/2
nontrivialDivisor arg1 arg2 :- ((succ n' n, elem d data1, data0 = 2, data1 = .. data0 n', mod n d data2, data2 = 0, arg1 = n, arg2 = d)).
constraints:
~(arg1[0,6] & n[0,6])
~(arg2[0,7] & d[0,7])
~(d[0,1] & d[0,4])
~(d[0,1] & d[0,7])
~(d[0,4] & d[0,7])
~(data0[0,2] & data0[0,3])
~(data1[0,1] & data1[0,3])
~(data1[0,3] & data0[0,3])
~(data2[0,4] & data2[0,5])
~(n'[0,0] & n'[0,3])
~(n[0,0] & n[0,4])
~(n[0,0] & n[0,6])
~(n[0,4] & n[0,6])
(d[0,1] | (d[0,4] | d[0,7]))
(data0[0,2] | data0[0,3])
(data1[0,1] | data1[0,3])
(data2[0,4] | data2[0,5])
(n'[0,0] | n'[0,3])
(n[0,0] | (n[0,4] | n[0,6]))
((d[0,1] & ~data1[0,1]) | (~d[0,1] & ~data1[0,1]))
((n'[0,0] & ~n[0,0]) | ((~n'[0,0] & n[0,0]) | (~n'[0,0] & ~n[0,0])))
((~n[0,4] & (~d[0,4] & data2[0,4])) | (~n[0,4] & (~d[0,4] & ~data2[0,4])))
(arg1[0] <-> arg1[0,6])
(arg1[] <-> arg1[0])
(arg2[0] <-> arg2[0,7])
(arg2[] <-> arg2[0])
(data0[0,3] <-> n'[0,3])
1
-}
nontrivialDivisor_ii = \arg1 arg2 -> do
  -- solution: d[0,1] data0[0,2] data1[0,3] data2[0,4] n'[0,0] n[0,6] ~arg1[0,6] ~arg1[0] ~arg1[] ~arg2[0,7] ~arg2[0] ~arg2[] ~d[0,4] ~d[0,7] ~data0[0,3] ~data1[0,1] ~data2[0,5] ~n'[0,3] ~n[0,0] ~n[0,4]
  () <- (do
    n <- pure arg1
    data0 <- pure 2
    (n') <- succ_oi n
    data1 <- pure [data0..n']
    (d) <- elem_oi data1
    guard $ arg2 == d
    (data2) <- mod_iio n d
    guard $ data2 == 0
    pure ()
   )
  pure ()

nontrivialDivisor_io = \arg1 -> do
  -- solution: arg2[0,7] arg2[0] arg2[] d[0,1] data0[0,2] data1[0,3] data2[0,4] n'[0,0] n[0,6] ~arg1[0,6] ~arg1[0] ~arg1[] ~d[0,4] ~d[0,7] ~data0[0,3] ~data1[0,1] ~data2[0,5] ~n'[0,3] ~n[0,0] ~n[0,4]
  (arg2) <- (do
    n <- pure arg1
    data0 <- pure 2
    (n') <- succ_oi n
    data1 <- pure [data0..n']
    (d) <- elem_oi data1
    arg2 <- pure d
    (data2) <- mod_iio n d
    guard $ data2 == 0
    pure (arg2)
   )
  pure (arg2)

{- oddsPrimeIO/1
oddsPrimeIO arg1 :- ((odds n, (>) n data0, data0 = 1, if (nontrivialDivisor n d, print d) then (empty) else (), arg1 = n)).
constraints:
~d[0,3,0,1]
~n[0,3,0,0]
~n[0,3]
~(arg1[0,4] & n[0,4])
~(d[0,3,0,0] & d[0,3,0,1])
~(data0[0,1] & data0[0,2])
~(n[0,0] & n[0,1])
~(n[0,0] & n[0,3])
~(n[0,0] & n[0,4])
~(n[0,1] & n[0,3])
~(n[0,1] & n[0,4])
~(n[0,3] & n[0,4])
(~n[0,1] & ~data0[0,1])
(d[0,3,0,0] | d[0,3,0,1])
(data0[0,1] | data0[0,2])
(n[0,0] | ~n[0,0])
(n[0,0] | (n[0,1] | (n[0,3] | n[0,4])))
((~n[0,3,0,0] & d[0,3,0,0]) | (~n[0,3,0,0] & ~d[0,3,0,0]))
(arg1[0] <-> arg1[0,4])
(arg1[] <-> arg1[0])
1
-}
oddsPrimeIO_i = \arg1 -> do
  -- solution: d[0,3,0,0] data0[0,2] n[0,0] ~arg1[0,4] ~arg1[0] ~arg1[] ~d[0,3,0,1] ~data0[0,1] ~n[0,1] ~n[0,3,0,0] ~n[0,3] ~n[0,4]
  () <- (do
    data0 <- pure 1
    (n) <- odds_o 
    guard $ arg1 == n
    guard $ (>) n data0
    () <- ifte ((do
      (d) <- nontrivialDivisor_io n
      () <- print_i d
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

oddsPrimeIO_o = do
  -- solution: arg1[0,4] arg1[0] arg1[] d[0,3,0,0] data0[0,2] n[0,0] ~d[0,3,0,1] ~data0[0,1] ~n[0,1] ~n[0,3,0,0] ~n[0,3] ~n[0,4]
  (arg1) <- (do
    data0 <- pure 1
    (n) <- odds_o 
    arg1 <- pure n
    guard $ (>) n data0
    () <- ifte ((do
      (d) <- nontrivialDivisor_io n
      () <- print_i d
      pure ()
     )) (\() -> (do
      () <- empty 
      pure ()
     )) ((do
      
      pure ()
     ))
    pure (arg1)
   )
  pure (arg1)
