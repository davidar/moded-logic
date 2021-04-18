{-# LANGUAGE NoMonomorphismRestriction #-}
module Euler where

import Control.Applicative
import Control.Monad.Logic
import Control.Monad.Logic.Moded.Prelude
import Data.List
import Data.MemoTrie

{- elem/2
elem x arg2 :- ((arg2 = x:_); (arg2 = _:xs, elem x xs)).
constraints:
x[0,0]
xs[1,0]
~arg2[1,0]
~(arg2[0,0] & x[0,0])
~(xs[1,0] & xs[1,1])
(xs[1,0] | xs[1,1])
(arg2[] <-> arg2[0])
(arg2[] <-> arg2[1])
(arg2[0] <-> arg2[0,0])
(arg2[1] <-> arg2[1,0])
(x[] <-> x[0])
(x[] <-> x[1])
(x[0] <-> x[0,0])
(x[1] <-> x[1,1])
(x[1,1] <-> x[])
(xs[1,1] <-> arg2[])
1
-}
elem_oi = \arg2 -> do
  -- solution: x[] x[0] x[0,0] x[1] x[1,1] xs[1,0] ~arg2[] ~arg2[0] ~arg2[0,0] ~arg2[1] ~arg2[1,0] ~xs[1,1]
  (x) <- (do
    (x:_) <- pure arg2
    pure (x)
   ) <|> (do
    (_:xs) <- pure arg2
    (x) <- elem_oi xs
    pure (x)
   )
  pure (x)

{- multiple/2
multiple x y :- ((mod x y data0, data0 = 0)).
constraints:
~(data0[0,0] & data0[0,1])
(data0[0,0] | data0[0,1])
((~x[0,0] & (~y[0,0] & data0[0,0])) | (~x[0,0] & (~y[0,0] & ~data0[0,0])))
(x[] <-> x[0])
(x[0] <-> x[0,0])
(y[] <-> y[0])
(y[0] <-> y[0,0])
1
-}
multiple_ii = \x y -> do
  -- solution: data0[0,0] ~data0[0,1] ~x[] ~x[0] ~x[0,0] ~y[] ~y[0] ~y[0,0]
  () <- (do
    (data0) <- mod_iio x y
    guard $ data0 == 0
    pure ()
   )
  pure ()

{- euler1/1
euler1 x :- ((elem x data2, data0 = 0, data1 = 999, data2 = .. data0 data1, multiple x y, ((y = 3); (y = 5)))).
constraints:
~(data0[0,1] & data0[0,3])
~(data1[0,2] & data1[0,3])
~(data2[0,0] & data2[0,3])
~(data2[0,3] & data0[0,3])
~(x[0,0] & x[0,4])
~(y[0,4] & y[0,5])
(x[0,0] & ~data2[0,0])
(~x[0,4] & ~y[0,4])
(data0[0,1] | data0[0,3])
(data1[0,2] | data1[0,3])
(data2[0,0] | data2[0,3])
(y[0,4] | y[0,5])
(data0[0,3] <-> data1[0,3])
(x[] <-> x[0])
(x[0] <-> (x[0,0] | x[0,4]))
(y[0,5] <-> y[0,5,0])
(y[0,5] <-> y[0,5,1])
(y[0,5,0] <-> y[0,5,0,0])
(y[0,5,1] <-> y[0,5,1,0])
1
-}
euler1_o = choose . nub . observeAll $ do
  -- solution: data0[0,1] data1[0,2] data2[0,3] x[] x[0] x[0,0] y[0,5] y[0,5,0] y[0,5,0,0] y[0,5,1] y[0,5,1,0] ~data0[0,3] ~data1[0,3] ~data2[0,0] ~x[0,4] ~y[0,4]
  (x) <- (do
    data0 <- pure 0
    data1 <- pure 999
    data2 <- pure [data0..data1]
    (x) <- elem_oi data2
    (y) <- (do
      y <- pure 3
      pure (y)
     ) <|> (do
      y <- pure 5
      pure (y)
     )
    () <- multiple_ii x y
    pure (x)
   )
  pure (x)

{- euler1'/1
euler1' s :- ((observeAll p r, sum r s, (p x :- (euler1 x)))).
constraints:
x[0,2,0,0]
~(p[0,0] & p[0,2])
~(r[0,0] & r[0,1])
(~p[0,0] & (p(1) & r[0,0]))
(p[0,0] | p[0,2])
(r[0,0] | r[0,1])
((~r[0,1] & s[0,1]) | (~r[0,1] & ~s[0,1]))
(s[] <-> s[0])
(s[0] <-> s[0,1])
(x[0,2,0] <-> x[0,2,0,0])
(p(1) <-> x[0,2,0])
1
-}
euler1'_i = \s -> do
  -- solution: p[0,2] r[0,0] x[0,2,0] x[0,2,0,0] p(1) ~p[0,0] ~r[0,1] ~s[] ~s[0] ~s[0,1]
  () <- (do
    (p) <- pure $  do
      (x) <- (do
        (x) <- euler1_o 
        pure (x)
       )
      pure (x)
    (r) <- observeAll_p1oo p
    () <- sum_ii r s
    pure ()
   )
  pure ()

euler1'_o = do
  -- solution: p[0,2] r[0,0] s[] s[0] s[0,1] x[0,2,0] x[0,2,0,0] p(1) ~p[0,0] ~r[0,1]
  (s) <- (do
    (p) <- pure $  do
      (x) <- (do
        (x) <- euler1_o 
        pure (x)
       )
      pure (x)
    (r) <- observeAll_p1oo p
    (s) <- sum_io r
    pure (s)
   )
  pure (s)

{- fib/2
fib arg1 arg2 :- ((arg1 = 0, arg2 = 0); (arg1 = 1, arg2 = 1); ((>) k data0, data0 = 1, succ i j, succ j k, fib i fi, fib j fj, plus fi fj fk, arg1 = k, arg2 = fk)).
constraints:
~(arg1[2,7] & k[2,7])
~(arg2[2,8] & fk[2,8])
~(data0[2,0] & data0[2,1])
~(fi[2,4] & fi[2,6])
~(fj[2,5] & fj[2,6])
~(fk[2,6] & fk[2,8])
~(i[2,2] & i[2,4])
~(j[2,2] & j[2,3])
~(j[2,2] & j[2,5])
~(j[2,3] & j[2,5])
~(k[2,0] & k[2,3])
~(k[2,0] & k[2,7])
~(k[2,3] & k[2,7])
(~k[2,0] & ~data0[2,0])
(data0[2,0] | data0[2,1])
(fi[2,4] | fi[2,6])
(fj[2,5] | fj[2,6])
(fk[2,6] | fk[2,8])
(i[2,2] | i[2,4])
(j[2,2] | (j[2,3] | j[2,5]))
(k[2,0] | (k[2,3] | k[2,7]))
((fi[2,6] & (~fj[2,6] & ~fk[2,6])) | ((~fi[2,6] & (fj[2,6] & ~fk[2,6])) | (~fi[2,6] & (~fj[2,6] & fk[2,6]))))
((i[2,2] & ~j[2,2]) | ((~i[2,2] & j[2,2]) | (~i[2,2] & ~j[2,2])))
((j[2,3] & ~k[2,3]) | ((~j[2,3] & k[2,3]) | (~j[2,3] & ~k[2,3])))
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg1[] <-> arg1[2])
(arg1[0] <-> arg1[0,0])
(arg1[1] <-> arg1[1,0])
(arg1[2] <-> arg1[2,7])
(arg2[] <-> arg2[0])
(arg2[] <-> arg2[1])
(arg2[] <-> arg2[2])
(arg2[0] <-> arg2[0,1])
(arg2[1] <-> arg2[1,1])
(arg2[2] <-> arg2[2,8])
(fi[2,4] <-> arg2[])
(fj[2,5] <-> arg2[])
(i[2,4] <-> arg1[])
(j[2,5] <-> arg1[])
1
-}
fib_io = memo $ \arg1 -> choose . observeAll $ do
  -- solution: arg2[] arg2[0] arg2[0,1] arg2[1] arg2[1,1] arg2[2] arg2[2,8] data0[2,1] fi[2,4] fj[2,5] fk[2,6] i[2,2] j[2,3] k[2,7] ~arg1[] ~arg1[0] ~arg1[0,0] ~arg1[1] ~arg1[1,0] ~arg1[2] ~arg1[2,7] ~data0[2,0] ~fi[2,6] ~fj[2,6] ~fk[2,8] ~i[2,4] ~j[2,2] ~j[2,5] ~k[2,0] ~k[2,3]
  (arg2) <- (do
    guard $ arg1 == 0
    arg2 <- pure 0
    pure (arg2)
   ) <|> (do
    guard $ arg1 == 1
    arg2 <- pure 1
    pure (arg2)
   ) <|> (do
    k <- pure arg1
    data0 <- pure 1
    guard $ (>) k data0
    (j) <- succ_oi k
    (fj) <- fib_io j
    (i) <- succ_oi j
    (fi) <- fib_io i
    (fk) <- plus_iio fi fj
    arg2 <- pure fk
    pure (arg2)
   )
  pure (arg2)

fib_oo = choose . observeAll $ do
  -- solution: arg1[] arg1[0] arg1[0,0] arg1[1] arg1[1,0] arg1[2] arg1[2,7] arg2[] arg2[0] arg2[0,1] arg2[1] arg2[1,1] arg2[2] arg2[2,8] data0[2,1] fi[2,4] fj[2,5] fk[2,6] i[2,4] j[2,5] k[2,3] ~data0[2,0] ~fi[2,6] ~fj[2,6] ~fk[2,8] ~i[2,2] ~j[2,2] ~j[2,3] ~k[2,0] ~k[2,7]
  (arg1,arg2) <- (do
    arg1 <- pure 0
    arg2 <- pure 0
    pure (arg1,arg2)
   ) <|> (do
    arg1 <- pure 1
    arg2 <- pure 1
    pure (arg1,arg2)
   ) <|> (do
    data0 <- pure 1
    (i,fi) <- fib_oo 
    (j,fj) <- fib_oo 
    () <- succ_ii i j
    (fk) <- plus_iio fi fj
    arg2 <- pure fk
    (k) <- succ_io j
    arg1 <- pure k
    guard $ (>) k data0
    pure (arg1,arg2)
   )
  pure (arg1,arg2)
