{-# LANGUAGE NoMonomorphismRestriction #-}
module Kiselyov where

import Control.Applicative
import Control.Monad.Logic
import Control.Monad.Logic.Moded.Prelude

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
nat_i arg1 = do
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

nat_o  = do
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
pythag_iii arg1 arg2 arg3 = do
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
    () <- if (>) j data1 then pure () else empty
    () <- if (>) k data2 then pure () else empty
    () <- nat_i j
    () <- nat_i k
    (i) <- nat_o 
    guard $ arg1 == i
    i1 <- pure i
    () <- if (<) i j then pure () else empty
    () <- if (>) i data0 then pure () else empty
    (jj) <- timesInt_iio j2 j3
    (kk) <- timesInt_iio k4 k5
    (ii) <- plus_oii jj kk
    (i0) <- timesInt_oii i1 ii
    guard $ i0 == i
    pure ()
   )
  pure ()

pythag_iio arg1 arg2 = do
  -- solution: arg3[0,22] arg3[0] arg3[] data0[0,2] data1[0,5] data2[0,8] i0[0,10] i1[0,12] i[0,0] ii[0,19] j2[0,14] j3[0,15] j[0,21] jj[0,13] k4[0,17] k5[0,18] k[0,6] kk[0,16] ~arg1[0,20] ~arg1[0] ~arg1[] ~arg2[0,21] ~arg2[0] ~arg2[] ~data0[0,1] ~data1[0,4] ~data2[0,7] ~i0[0,11] ~i1[0,10] ~i[0,11] ~i[0,12] ~i[0,1] ~i[0,20] ~i[0,9] ~ii[0,10] ~j2[0,13] ~j3[0,13] ~j[0,14] ~j[0,15] ~j[0,3] ~j[0,4] ~j[0,9] ~jj[0,19] ~k4[0,16] ~k5[0,16] ~k[0,17] ~k[0,18] ~k[0,22] ~k[0,7] ~kk[0,19]
  (arg3) <- (do
    j <- pure arg2
    j2 <- pure j
    j3 <- pure j
    data0 <- pure 0
    data1 <- pure 0
    data2 <- pure 0
    () <- if (>) j data1 then pure () else empty
    () <- nat_i j
    (i) <- nat_o 
    guard $ arg1 == i
    i1 <- pure i
    () <- if (<) i j then pure () else empty
    () <- if (>) i data0 then pure () else empty
    (k) <- nat_o 
    arg3 <- pure k
    k4 <- pure k
    k5 <- pure k
    () <- if (>) k data2 then pure () else empty
    (jj) <- timesInt_iio j2 j3
    (kk) <- timesInt_iio k4 k5
    (ii) <- plus_oii jj kk
    (i0) <- timesInt_oii i1 ii
    guard $ i0 == i
    pure (arg3)
   )
  pure (arg3)

pythag_ioi arg1 arg3 = do
  -- solution: arg2[0,21] arg2[0] arg2[] data0[0,2] data1[0,5] data2[0,8] i0[0,10] i1[0,12] i[0,0] ii[0,19] j2[0,14] j3[0,15] j[0,3] jj[0,13] k4[0,17] k5[0,18] k[0,22] kk[0,16] ~arg1[0,20] ~arg1[0] ~arg1[] ~arg3[0,22] ~arg3[0] ~arg3[] ~data0[0,1] ~data1[0,4] ~data2[0,7] ~i0[0,11] ~i1[0,10] ~i[0,11] ~i[0,12] ~i[0,1] ~i[0,20] ~i[0,9] ~ii[0,10] ~j2[0,13] ~j3[0,13] ~j[0,14] ~j[0,15] ~j[0,21] ~j[0,4] ~j[0,9] ~jj[0,19] ~k4[0,16] ~k5[0,16] ~k[0,17] ~k[0,18] ~k[0,6] ~k[0,7] ~kk[0,19]
  (arg2) <- (do
    k <- pure arg3
    k4 <- pure k
    k5 <- pure k
    data0 <- pure 0
    data1 <- pure 0
    data2 <- pure 0
    () <- if (>) k data2 then pure () else empty
    () <- nat_i k
    (i) <- nat_o 
    guard $ arg1 == i
    i1 <- pure i
    () <- if (>) i data0 then pure () else empty
    (j) <- nat_o 
    arg2 <- pure j
    j2 <- pure j
    j3 <- pure j
    () <- if (<) i j then pure () else empty
    () <- if (>) j data1 then pure () else empty
    (jj) <- timesInt_iio j2 j3
    (kk) <- timesInt_iio k4 k5
    (ii) <- plus_oii jj kk
    (i0) <- timesInt_oii i1 ii
    guard $ i0 == i
    pure (arg2)
   )
  pure (arg2)

pythag_ioo arg1 = do
  -- solution: arg2[0,21] arg2[0] arg2[] arg3[0,22] arg3[0] arg3[] data0[0,2] data1[0,5] data2[0,8] i0[0,10] i1[0,12] i[0,0] ii[0,19] j2[0,14] j3[0,15] j[0,3] jj[0,13] k4[0,17] k5[0,18] k[0,6] kk[0,16] ~arg1[0,20] ~arg1[0] ~arg1[] ~data0[0,1] ~data1[0,4] ~data2[0,7] ~i0[0,11] ~i1[0,10] ~i[0,11] ~i[0,12] ~i[0,1] ~i[0,20] ~i[0,9] ~ii[0,10] ~j2[0,13] ~j3[0,13] ~j[0,14] ~j[0,15] ~j[0,21] ~j[0,4] ~j[0,9] ~jj[0,19] ~k4[0,16] ~k5[0,16] ~k[0,17] ~k[0,18] ~k[0,22] ~k[0,7] ~kk[0,19]
  (arg2,arg3) <- (do
    data0 <- pure 0
    data1 <- pure 0
    data2 <- pure 0
    (i) <- nat_o 
    guard $ arg1 == i
    i1 <- pure i
    () <- if (>) i data0 then pure () else empty
    (j) <- nat_o 
    arg2 <- pure j
    j2 <- pure j
    j3 <- pure j
    () <- if (<) i j then pure () else empty
    () <- if (>) j data1 then pure () else empty
    (k) <- nat_o 
    arg3 <- pure k
    k4 <- pure k
    k5 <- pure k
    () <- if (>) k data2 then pure () else empty
    (jj) <- timesInt_iio j2 j3
    (kk) <- timesInt_iio k4 k5
    (ii) <- plus_oii jj kk
    (i0) <- timesInt_oii i1 ii
    guard $ i0 == i
    pure (arg2,arg3)
   )
  pure (arg2,arg3)

pythag_oii arg2 arg3 = do
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
    () <- if (>) j data1 then pure () else empty
    () <- if (>) k data2 then pure () else empty
    () <- nat_i j
    () <- nat_i k
    (i) <- nat_o 
    arg1 <- pure i
    i1 <- pure i
    () <- if (<) i j then pure () else empty
    () <- if (>) i data0 then pure () else empty
    (jj) <- timesInt_iio j2 j3
    (kk) <- timesInt_iio k4 k5
    (ii) <- plus_oii jj kk
    (i0) <- timesInt_oii i1 ii
    guard $ i0 == i
    pure (arg1)
   )
  pure (arg1)

pythag_oio arg2 = do
  -- solution: arg1[0,20] arg1[0] arg1[] arg3[0,22] arg3[0] arg3[] data0[0,2] data1[0,5] data2[0,8] i0[0,10] i1[0,12] i[0,0] ii[0,19] j2[0,14] j3[0,15] j[0,21] jj[0,13] k4[0,17] k5[0,18] k[0,6] kk[0,16] ~arg2[0,21] ~arg2[0] ~arg2[] ~data0[0,1] ~data1[0,4] ~data2[0,7] ~i0[0,11] ~i1[0,10] ~i[0,11] ~i[0,12] ~i[0,1] ~i[0,20] ~i[0,9] ~ii[0,10] ~j2[0,13] ~j3[0,13] ~j[0,14] ~j[0,15] ~j[0,3] ~j[0,4] ~j[0,9] ~jj[0,19] ~k4[0,16] ~k5[0,16] ~k[0,17] ~k[0,18] ~k[0,22] ~k[0,7] ~kk[0,19]
  (arg1,arg3) <- (do
    j <- pure arg2
    j2 <- pure j
    j3 <- pure j
    data0 <- pure 0
    data1 <- pure 0
    data2 <- pure 0
    () <- if (>) j data1 then pure () else empty
    () <- nat_i j
    (i) <- nat_o 
    arg1 <- pure i
    i1 <- pure i
    () <- if (<) i j then pure () else empty
    () <- if (>) i data0 then pure () else empty
    (k) <- nat_o 
    arg3 <- pure k
    k4 <- pure k
    k5 <- pure k
    () <- if (>) k data2 then pure () else empty
    (jj) <- timesInt_iio j2 j3
    (kk) <- timesInt_iio k4 k5
    (ii) <- plus_oii jj kk
    (i0) <- timesInt_oii i1 ii
    guard $ i0 == i
    pure (arg1,arg3)
   )
  pure (arg1,arg3)

pythag_ooi arg3 = do
  -- solution: arg1[0,20] arg1[0] arg1[] arg2[0,21] arg2[0] arg2[] data0[0,2] data1[0,5] data2[0,8] i0[0,10] i1[0,12] i[0,0] ii[0,19] j2[0,14] j3[0,15] j[0,3] jj[0,13] k4[0,17] k5[0,18] k[0,22] kk[0,16] ~arg3[0,22] ~arg3[0] ~arg3[] ~data0[0,1] ~data1[0,4] ~data2[0,7] ~i0[0,11] ~i1[0,10] ~i[0,11] ~i[0,12] ~i[0,1] ~i[0,20] ~i[0,9] ~ii[0,10] ~j2[0,13] ~j3[0,13] ~j[0,14] ~j[0,15] ~j[0,21] ~j[0,4] ~j[0,9] ~jj[0,19] ~k4[0,16] ~k5[0,16] ~k[0,17] ~k[0,18] ~k[0,6] ~k[0,7] ~kk[0,19]
  (arg1,arg2) <- (do
    k <- pure arg3
    k4 <- pure k
    k5 <- pure k
    data0 <- pure 0
    data1 <- pure 0
    data2 <- pure 0
    () <- if (>) k data2 then pure () else empty
    () <- nat_i k
    (i) <- nat_o 
    arg1 <- pure i
    i1 <- pure i
    () <- if (>) i data0 then pure () else empty
    (j) <- nat_o 
    arg2 <- pure j
    j2 <- pure j
    j3 <- pure j
    () <- if (<) i j then pure () else empty
    () <- if (>) j data1 then pure () else empty
    (jj) <- timesInt_iio j2 j3
    (kk) <- timesInt_iio k4 k5
    (ii) <- plus_oii jj kk
    (i0) <- timesInt_oii i1 ii
    guard $ i0 == i
    pure (arg1,arg2)
   )
  pure (arg1,arg2)

pythag_ooo  = do
  -- solution: arg1[0,20] arg1[0] arg1[] arg2[0,21] arg2[0] arg2[] arg3[0,22] arg3[0] arg3[] data0[0,2] data1[0,5] data2[0,8] i0[0,10] i1[0,12] i[0,0] ii[0,19] j2[0,14] j3[0,15] j[0,3] jj[0,13] k4[0,17] k5[0,18] k[0,6] kk[0,16] ~data0[0,1] ~data1[0,4] ~data2[0,7] ~i0[0,11] ~i1[0,10] ~i[0,11] ~i[0,12] ~i[0,1] ~i[0,20] ~i[0,9] ~ii[0,10] ~j2[0,13] ~j3[0,13] ~j[0,14] ~j[0,15] ~j[0,21] ~j[0,4] ~j[0,9] ~jj[0,19] ~k4[0,16] ~k5[0,16] ~k[0,17] ~k[0,18] ~k[0,22] ~k[0,7] ~kk[0,19]
  (arg1,arg2,arg3) <- (do
    data0 <- pure 0
    data1 <- pure 0
    data2 <- pure 0
    (i) <- nat_o 
    arg1 <- pure i
    i1 <- pure i
    () <- if (>) i data0 then pure () else empty
    (j) <- nat_o 
    arg2 <- pure j
    j2 <- pure j
    j3 <- pure j
    () <- if (<) i j then pure () else empty
    () <- if (>) j data1 then pure () else empty
    (k) <- nat_o 
    arg3 <- pure k
    k4 <- pure k
    k5 <- pure k
    () <- if (>) k data2 then pure () else empty
    (jj) <- timesInt_iio j2 j3
    (kk) <- timesInt_iio k4 k5
    (ii) <- plus_oii jj kk
    (i0) <- timesInt_oii i1 ii
    guard $ i0 == i
    pure (arg1,arg2,arg3)
   )
  pure (arg1,arg2,arg3)
