{-# LANGUAGE NoMonomorphismRestriction #-}
module Euler where

import Control.Applicative
import Control.Monad.Logic
import Control.Monad.Logic.Moded.Prelude
import Data.List

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
elem_ii arg1 arg2 = do
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

elem_oi arg2 = do
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

{- multiple/2
multiple arg1 arg2 :- ((mod x y data0, data0 = 0, arg1 = x, arg2 = y)).
constraints:
~(arg1[0,2] & x[0,2])
~(arg2[0,3] & y[0,3])
~(data0[0,0] & data0[0,1])
~(x[0,0] & x[0,2])
~(y[0,0] & y[0,3])
(data0[0,0] | data0[0,1])
(x[0,0] | x[0,2])
(y[0,0] | y[0,3])
((~x[0,0] & (~y[0,0] & data0[0,0])) | (~x[0,0] & (~y[0,0] & ~data0[0,0])))
(arg1[0] <-> arg1[0,2])
(arg1[] <-> arg1[0])
(arg2[0] <-> arg2[0,3])
(arg2[] <-> arg2[0])
1
-}
multiple_ii arg1 arg2 = do
  -- solution: data0[0,0] x[0,2] y[0,3] ~arg1[0,2] ~arg1[0] ~arg1[] ~arg2[0,3] ~arg2[0] ~arg2[] ~data0[0,1] ~x[0,0] ~y[0,0]
  () <- (do
    x <- pure arg1
    y <- pure arg2
    (data0) <- mod_iio x y
    guard $ data0 == 0
    pure ()
   )
  pure ()

{- euler1/1
euler1 arg1 :- ((elem x data2, data0 = 0, data1 = 999, data2 = .. data0 data1, multiple x y, ((y = 3); (y = 5)), arg1 = x)).
constraints:
~(arg1[0,6] & x[0,6])
~(data0[0,1] & data0[0,3])
~(data1[0,2] & data1[0,3])
~(data2[0,0] & data2[0,3])
~(data2[0,3] & data0[0,3])
~(x[0,0] & x[0,4])
~(x[0,0] & x[0,6])
~(x[0,4] & x[0,6])
~(y[0,4] & y[0,5])
(~x[0,4] & ~y[0,4])
(data0[0,1] | data0[0,3])
(data1[0,2] | data1[0,3])
(data2[0,0] | data2[0,3])
(x[0,0] | (x[0,4] | x[0,6]))
(y[0,4] | y[0,5])
((x[0,0] & ~data2[0,0]) | (~x[0,0] & ~data2[0,0]))
(arg1[0] <-> arg1[0,6])
(arg1[] <-> arg1[0])
(data0[0,3] <-> data1[0,3])
(y[0,5,0] <-> y[0,5,0,0])
(y[0,5,1] <-> y[0,5,1,0])
(y[0,5] <-> y[0,5,0])
(y[0,5] <-> y[0,5,1])
1
-}
euler1_i arg1 = do
  -- solution: data0[0,1] data1[0,2] data2[0,3] x[0,0] y[0,5,0,0] y[0,5,0] y[0,5,1,0] y[0,5,1] y[0,5] ~arg1[0,6] ~arg1[0] ~arg1[] ~data0[0,3] ~data1[0,3] ~data2[0,0] ~x[0,4] ~x[0,6] ~y[0,4]
  () <- (do
    data0 <- pure 0
    data1 <- pure 999
    data2 <- pure [data0..data1]
    (x) <- elem_oi data2
    guard $ arg1 == x
    (y) <- (do
      y <- pure 3
      pure (y)
     ) <|> (do
      y <- pure 5
      pure (y)
     )
    () <- multiple_ii x y
    pure ()
   )
  pure ()

euler1_o  = do
  -- solution: arg1[0,6] arg1[0] arg1[] data0[0,1] data1[0,2] data2[0,3] x[0,0] y[0,5,0,0] y[0,5,0] y[0,5,1,0] y[0,5,1] y[0,5] ~data0[0,3] ~data1[0,3] ~data2[0,0] ~x[0,4] ~x[0,6] ~y[0,4]
  (arg1) <- (do
    data0 <- pure 0
    data1 <- pure 999
    data2 <- pure [data0..data1]
    (x) <- elem_oi data2
    arg1 <- pure x
    (y) <- (do
      y <- pure 3
      pure (y)
     ) <|> (do
      y <- pure 5
      pure (y)
     )
    () <- multiple_ii x y
    pure (arg1)
   )
  pure (arg1)
