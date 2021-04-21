{-# LANGUAGE NoMonomorphismRestriction #-}
module Euler where

import Control.Applicative
import Control.Monad.Logic
import Control.Monad.Logic.Moded.Prelude
import Data.List
import Data.MemoTrie

{- nat/1
nat arg1 :- ((arg1 = 0); (nat n, succ n n', arg1 = n')).
constraints:
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
nat_i = \arg1 -> once $ do
  -- solution: n[1,1] n'[1,2] ~arg1[] ~arg1[0] ~arg1[0,0] ~arg1[1] ~arg1[1,2] ~n[1,0] ~n'[1,1]
  -- cost: 3
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
  -- solution: arg1[] arg1[0] arg1[0,0] arg1[1] arg1[1,2] n[1,0] n'[1,1] ~n[1,1] ~n'[1,2]
  -- cost: 4
  (arg1) <- (do
    arg1 <- pure 0
    pure (arg1)
   ) <|> (do
    (n) <- nat_o 
    (n') <- succ_io n
    arg1 <- pure n'
    pure (arg1)
   )
  pure (arg1 :: Integer)

{- oddNat/1
oddNat arg1 :- ((arg1 = 1); (oddNat n, plus n data0 n', data0 = 2, arg1 = n')).
constraints:
~(arg1[1,3] & n'[1,3])
~(data0[1,1] & data0[1,2])
~(n[1,0] & n[1,1])
~(n'[1,1] & n'[1,3])
(data0[1,1] | data0[1,2])
(n[1,0] | n[1,1])
(n'[1,1] | n'[1,3])
((n[1,1] & (~data0[1,1] & ~n'[1,1])) | ((~n[1,1] & (data0[1,1] & ~n'[1,1])) | (~n[1,1] & (~data0[1,1] & n'[1,1]))))
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg1[0] <-> arg1[0,0])
(arg1[1] <-> arg1[1,3])
(n[1,0] <-> arg1[])
1
-}
oddNat_i = \arg1 -> once $ do
  -- solution: data0[1,2] n[1,1] n'[1,3] ~arg1[] ~arg1[0] ~arg1[0,0] ~arg1[1] ~arg1[1,3] ~data0[1,1] ~n[1,0] ~n'[1,1]
  -- cost: 3
  () <- (do
    guard $ arg1 == 1
    pure ()
   ) <|> (do
    n' <- pure arg1
    data0 <- pure 2
    (n) <- plus_oii data0 n'
    () <- oddNat_i n
    pure ()
   )
  pure ()

oddNat_o = do
  -- solution: arg1[] arg1[0] arg1[0,0] arg1[1] arg1[1,3] data0[1,2] n[1,0] n'[1,1] ~data0[1,1] ~n[1,1] ~n'[1,3]
  -- cost: 4
  (arg1) <- (do
    arg1 <- pure 1
    pure (arg1)
   ) <|> (do
    data0 <- pure 2
    (n) <- oddNat_o 
    (n') <- plus_iio n data0
    arg1 <- pure n'
    pure (arg1)
   )
  pure (arg1)

{- even/1
even x :- ((mod x data0 data1, data0 = 2, data1 = 0)).
constraints:
~(data0[0,0] & data0[0,1])
~(data1[0,0] & data1[0,2])
(data0[0,0] | data0[0,1])
(data1[0,0] | data1[0,2])
((~x[0,0] & (~data0[0,0] & data1[0,0])) | (~x[0,0] & (~data0[0,0] & ~data1[0,0])))
(x[] <-> x[0])
(x[0] <-> x[0,0])
1
-}
even_i = \x -> once $ do
  -- solution: data0[0,1] data1[0,2] ~data0[0,0] ~data1[0,0] ~x[] ~x[0] ~x[0,0]
  -- cost: 1
  () <- (do
    data1 <- pure 0
    data0 <- pure 2
    () <- mod_iii x data0 data1
    pure ()
   )
  pure ()

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
  -- cost: 2
  (x) <- (do
    (x:_) <- pure arg2
    pure (x)
   ) <|> (do
    (_:xs) <- pure arg2
    (x) <- elem_oi xs
    pure (x)
   )
  pure (x)

{- span/4
span p arg2 arg3 arg4 :- ((arg2 = [], arg3 = [], arg4 = []); (arg2 = x0:xs1, x0 = x, xs1 = xs, if (p x) then (span p xs yt zs, ys = x2:yt, x2 = x) else (ys = [], zs = x3:xs4, x3 = x, xs4 = xs), arg3 = ys, arg4 = zs)).
constraints:
~p[]
~p[1,3,1]
~x[1,3,0,0]
~x[1,3,1,2]
~x[1,3,2]
~(arg2[1,0] & x0[1,0])
~(arg3[1,4] & ys[1,4])
~(arg4[1,5] & zs[1,5])
~(x[1,1] & x[1,3])
~(x0[1,0] & x0[1,1])
~(x0[1,1] & x[1,1])
~(x2[1,3,1,1] & x2[1,3,1,2])
~(x2[1,3,1,2] & x[1,3,1,2])
~(x3[1,3,2,1] & x3[1,3,2,2])
~(x3[1,3,2,2] & x[1,3,2,2])
~(xs[1,2] & xs[1,3])
~(xs1[1,0] & xs1[1,2])
~(xs1[1,2] & xs[1,2])
~(xs4[1,3,2,1] & xs4[1,3,2,3])
~(xs4[1,3,2,3] & xs[1,3,2,3])
~(ys[1,3] & ys[1,4])
~(ys[1,3,1,1] & x2[1,3,1,1])
~(yt[1,3,1,0] & yt[1,3,1,1])
~(zs[1,3] & zs[1,5])
~(zs[1,3,2,1] & x3[1,3,2,1])
(x[1,1] | x[1,3])
(x0[1,0] | x0[1,1])
(x2[1,3,1,1] | x2[1,3,1,2])
(x3[1,3,2,1] | x3[1,3,2,2])
(xs[1,2] | xs[1,3])
(xs1[1,0] | xs1[1,2])
(xs4[1,3,2,1] | xs4[1,3,2,3])
(ys[1,3] | ys[1,4])
(yt[1,3,1,0] | yt[1,3,1,1])
(zs[1,3] | zs[1,5])
(arg2[] <-> arg2[0])
(arg2[] <-> arg2[1])
(arg2[0] <-> arg2[0,0])
(arg2[1] <-> arg2[1,0])
(arg3[] <-> arg3[0])
(arg3[] <-> arg3[1])
(arg3[0] <-> arg3[0,1])
(arg3[1] <-> arg3[1,4])
(arg4[] <-> arg4[0])
(arg4[] <-> arg4[1])
(arg4[0] <-> arg4[0,2])
(arg4[1] <-> arg4[1,5])
(p[] <-> p[1])
(p[1] <-> p[1,3])
(p[1,3] <-> p[1,3,1])
(p[1,3,1] <-> p[1,3,1,0])
(p[1,3,1,0] <-> p[])
(x[1,3] <-> x[1,3,2])
(x[1,3,0,0] <-> p(1))
(x[1,3,2] <-> x[1,3,2,2])
(x0[1,0] <-> xs1[1,0])
(x2[1,3,1,1] <-> yt[1,3,1,1])
(x3[1,3,2,1] <-> xs4[1,3,2,1])
(xs[1,3] <-> (xs[1,3,1] | xs[1,3,2]))
(xs[1,3,1] <-> xs[1,3,1,0])
(xs[1,3,1] <-> xs[1,3,2])
(xs[1,3,1,0] <-> arg2[])
(xs[1,3,2] <-> xs[1,3,2,3])
(ys[1,3] <-> (ys[1,3,1] | ys[1,3,2]))
(ys[1,3,1] <-> ys[1,3,1,1])
(ys[1,3,1] <-> ys[1,3,2])
(ys[1,3,2] <-> ys[1,3,2,0])
(yt[1,3,1,0] <-> arg3[])
(zs[1,3] <-> (zs[1,3,1] | zs[1,3,2]))
(zs[1,3,1] <-> zs[1,3,1,0])
(zs[1,3,1] <-> zs[1,3,2])
(zs[1,3,1,0] <-> arg4[])
(zs[1,3,2] <-> zs[1,3,2,1])
1
-}
span_p1iiii = \p arg2 arg3 arg4 -> once $ do
  -- solution: x[1,1] x0[1,0] x2[1,3,1,1] x3[1,3,2,1] xs[1,2] xs1[1,0] xs4[1,3,2,1] ys[1,4] yt[1,3,1,1] zs[1,5] ~arg2[] ~arg2[0] ~arg2[0,0] ~arg2[1] ~arg2[1,0] ~arg3[] ~arg3[0] ~arg3[0,1] ~arg3[1] ~arg3[1,4] ~arg4[] ~arg4[0] ~arg4[0,2] ~arg4[1] ~arg4[1,5] ~p[] ~p[1] ~p[1,3] ~p[1,3,1] ~p[1,3,1,0] ~x[1,3] ~x[1,3,0,0] ~x[1,3,1,2] ~x[1,3,2] ~x[1,3,2,2] ~x0[1,1] ~x2[1,3,1,2] ~x3[1,3,2,2] ~xs[1,3] ~xs[1,3,1] ~xs[1,3,1,0] ~xs[1,3,2] ~xs[1,3,2,3] ~xs1[1,2] ~xs4[1,3,2,3] ~ys[1,3] ~ys[1,3,1] ~ys[1,3,1,1] ~ys[1,3,2] ~ys[1,3,2,0] ~yt[1,3,1,0] ~zs[1,3] ~zs[1,3,1] ~zs[1,3,1,0] ~zs[1,3,2] ~zs[1,3,2,1] ~p(1)
  -- cost: 2
  () <- (do
    guard $ arg2 == []
    guard $ arg3 == []
    guard $ arg4 == []
    pure ()
   ) <|> (do
    ys <- pure arg3
    zs <- pure arg4
    (x0:xs1) <- pure arg2
    x <- pure x0
    xs <- pure xs1
    () <- ifte ((do
      () <- p x
      pure ()
     )) (\() -> (do
      (x2:yt) <- pure ys
      guard $ x2 == x
      () <- span_p1iiii p xs yt zs
      pure ()
     )) ((do
      (x3:xs4) <- pure zs
      guard $ x3 == x
      guard $ xs4 == xs
      guard $ ys == []
      pure ()
     ))
    pure ()
   )
  pure ()

span_p1iiio = \p arg2 arg3 -> do
  -- solution: arg4[] arg4[0] arg4[0,2] arg4[1] arg4[1,5] x[1,1] x0[1,0] x2[1,3,1,1] x3[1,3,2,2] xs[1,2] xs1[1,0] xs4[1,3,2,3] ys[1,4] yt[1,3,1,1] zs[1,3] zs[1,3,1] zs[1,3,1,0] zs[1,3,2] zs[1,3,2,1] ~arg2[] ~arg2[0] ~arg2[0,0] ~arg2[1] ~arg2[1,0] ~arg3[] ~arg3[0] ~arg3[0,1] ~arg3[1] ~arg3[1,4] ~p[] ~p[1] ~p[1,3] ~p[1,3,1] ~p[1,3,1,0] ~x[1,3] ~x[1,3,0,0] ~x[1,3,1,2] ~x[1,3,2] ~x[1,3,2,2] ~x0[1,1] ~x2[1,3,1,2] ~x3[1,3,2,1] ~xs[1,3] ~xs[1,3,1] ~xs[1,3,1,0] ~xs[1,3,2] ~xs[1,3,2,3] ~xs1[1,2] ~xs4[1,3,2,1] ~ys[1,3] ~ys[1,3,1] ~ys[1,3,1,1] ~ys[1,3,2] ~ys[1,3,2,0] ~yt[1,3,1,0] ~zs[1,5] ~p(1)
  -- cost: 3
  (arg4) <- (do
    guard $ arg2 == []
    guard $ arg3 == []
    arg4 <- pure []
    pure (arg4)
   ) <|> (do
    ys <- pure arg3
    (x0:xs1) <- pure arg2
    x <- pure x0
    xs <- pure xs1
    (zs) <- ifte ((do
      () <- p x
      pure ()
     )) (\() -> (do
      (x2:yt) <- pure ys
      guard $ x2 == x
      (zs) <- span_p1iiio p xs yt
      pure (zs)
     )) ((do
      x3 <- pure x
      xs4 <- pure xs
      zs <- pure (x3:xs4)
      guard $ ys == []
      pure (zs)
     ))
    arg4 <- pure zs
    pure (arg4)
   )
  pure (arg4)

span_p1iioi = \p arg2 arg4 -> do
  -- solution: arg3[] arg3[0] arg3[0,1] arg3[1] arg3[1,4] x[1,1] x0[1,0] x2[1,3,1,2] x3[1,3,2,1] xs[1,2] xs1[1,0] xs4[1,3,2,1] ys[1,3] ys[1,3,1] ys[1,3,1,1] ys[1,3,2] ys[1,3,2,0] yt[1,3,1,0] zs[1,5] ~arg2[] ~arg2[0] ~arg2[0,0] ~arg2[1] ~arg2[1,0] ~arg4[] ~arg4[0] ~arg4[0,2] ~arg4[1] ~arg4[1,5] ~p[] ~p[1] ~p[1,3] ~p[1,3,1] ~p[1,3,1,0] ~x[1,3] ~x[1,3,0,0] ~x[1,3,1,2] ~x[1,3,2] ~x[1,3,2,2] ~x0[1,1] ~x2[1,3,1,1] ~x3[1,3,2,2] ~xs[1,3] ~xs[1,3,1] ~xs[1,3,1,0] ~xs[1,3,2] ~xs[1,3,2,3] ~xs1[1,2] ~xs4[1,3,2,3] ~ys[1,4] ~yt[1,3,1,1] ~zs[1,3] ~zs[1,3,1] ~zs[1,3,1,0] ~zs[1,3,2] ~zs[1,3,2,1] ~p(1)
  -- cost: 3
  (arg3) <- (do
    guard $ arg2 == []
    arg3 <- pure []
    guard $ arg4 == []
    pure (arg3)
   ) <|> (do
    zs <- pure arg4
    (x0:xs1) <- pure arg2
    x <- pure x0
    xs <- pure xs1
    (ys) <- ifte ((do
      () <- p x
      pure ()
     )) (\() -> (do
      x2 <- pure x
      (yt) <- span_p1iioi p xs zs
      ys <- pure (x2:yt)
      pure (ys)
     )) ((do
      (x3:xs4) <- pure zs
      guard $ x3 == x
      guard $ xs4 == xs
      ys <- pure []
      pure (ys)
     ))
    arg3 <- pure ys
    pure (arg3)
   )
  pure (arg3)

span_p1iioo = \p arg2 -> do
  -- solution: arg3[] arg3[0] arg3[0,1] arg3[1] arg3[1,4] arg4[] arg4[0] arg4[0,2] arg4[1] arg4[1,5] x[1,1] x0[1,0] x2[1,3,1,2] x3[1,3,2,2] xs[1,2] xs1[1,0] xs4[1,3,2,3] ys[1,3] ys[1,3,1] ys[1,3,1,1] ys[1,3,2] ys[1,3,2,0] yt[1,3,1,0] zs[1,3] zs[1,3,1] zs[1,3,1,0] zs[1,3,2] zs[1,3,2,1] ~arg2[] ~arg2[0] ~arg2[0,0] ~arg2[1] ~arg2[1,0] ~p[] ~p[1] ~p[1,3] ~p[1,3,1] ~p[1,3,1,0] ~x[1,3] ~x[1,3,0,0] ~x[1,3,1,2] ~x[1,3,2] ~x[1,3,2,2] ~x0[1,1] ~x2[1,3,1,1] ~x3[1,3,2,1] ~xs[1,3] ~xs[1,3,1] ~xs[1,3,1,0] ~xs[1,3,2] ~xs[1,3,2,3] ~xs1[1,2] ~xs4[1,3,2,1] ~ys[1,4] ~yt[1,3,1,1] ~zs[1,5] ~p(1)
  -- cost: 4
  (arg3,arg4) <- (do
    guard $ arg2 == []
    arg3 <- pure []
    arg4 <- pure []
    pure (arg3,arg4)
   ) <|> (do
    (x0:xs1) <- pure arg2
    x <- pure x0
    xs <- pure xs1
    (ys,zs) <- ifte ((do
      () <- p x
      pure ()
     )) (\() -> (do
      x2 <- pure x
      (yt,zs) <- span_p1iioo p xs
      ys <- pure (x2:yt)
      pure (ys,zs)
     )) ((do
      x3 <- pure x
      xs4 <- pure xs
      zs <- pure (x3:xs4)
      ys <- pure []
      pure (ys,zs)
     ))
    arg3 <- pure ys
    arg4 <- pure zs
    pure (arg3,arg4)
   )
  pure (arg3,arg4)

{- reverseDL/3
reverseDL arg1 arg2 arg3 :- ((arg1 = [], arg2 = xs, arg3 = xs); (arg1 = h0:t, h0 = h, reverseDL t data0 r, data0 = h1:rest, h1 = h, arg2 = rest, arg3 = r)).
constraints:
~(arg1[1,0] & h0[1,0])
~(arg2[0,1] & xs[0,1])
~(arg2[1,5] & rest[1,5])
~(arg3[0,2] & xs[0,2])
~(arg3[1,6] & r[1,6])
~(data0[1,2] & data0[1,3])
~(data0[1,3] & h1[1,3])
~(h[1,1] & h[1,4])
~(h0[1,0] & h0[1,1])
~(h0[1,1] & h[1,1])
~(h1[1,3] & h1[1,4])
~(h1[1,4] & h[1,4])
~(r[1,2] & r[1,6])
~(rest[1,3] & rest[1,5])
~(t[1,0] & t[1,2])
~(xs[0,1] & xs[0,2])
(data0[1,2] | data0[1,3])
(h[1,1] | h[1,4])
(h0[1,0] | h0[1,1])
(h1[1,3] | h1[1,4])
(r[1,2] | r[1,6])
(rest[1,3] | rest[1,5])
(t[1,0] | t[1,2])
(xs[0,1] | xs[0,2])
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg1[0] <-> arg1[0,0])
(arg1[1] <-> arg1[1,0])
(arg2[] <-> arg2[0])
(arg2[] <-> arg2[1])
(arg2[0] <-> arg2[0,1])
(arg2[1] <-> arg2[1,5])
(arg3[] <-> arg3[0])
(arg3[] <-> arg3[1])
(arg3[0] <-> arg3[0,2])
(arg3[1] <-> arg3[1,6])
(data0[1,2] <-> arg2[])
(h0[1,0] <-> t[1,0])
(h1[1,3] <-> rest[1,3])
(r[1,2] <-> arg3[])
(t[1,2] <-> arg1[])
1
-}
reverseDL_iii = \arg1 arg2 arg3 -> once $ do
  -- solution: data0[1,3] h[1,1] h0[1,0] h1[1,4] r[1,6] rest[1,5] t[1,0] xs[0,1] ~arg1[] ~arg1[0] ~arg1[0,0] ~arg1[1] ~arg1[1,0] ~arg2[] ~arg2[0] ~arg2[0,1] ~arg2[1] ~arg2[1,5] ~arg3[] ~arg3[0] ~arg3[0,2] ~arg3[1] ~arg3[1,6] ~data0[1,2] ~h[1,4] ~h0[1,1] ~h1[1,3] ~r[1,2] ~rest[1,3] ~t[1,2] ~xs[0,2]
  -- cost: 1
  () <- (do
    xs <- pure arg2
    guard $ arg3 == xs
    guard $ arg1 == []
    pure ()
   ) <|> (do
    rest <- pure arg2
    r <- pure arg3
    (h0:t) <- pure arg1
    h <- pure h0
    h1 <- pure h
    data0 <- pure (h1:rest)
    () <- reverseDL_iii t data0 r
    pure ()
   )
  pure ()

reverseDL_iio = \arg1 arg2 -> do
  -- solution: arg3[] arg3[0] arg3[0,2] arg3[1] arg3[1,6] data0[1,3] h[1,1] h0[1,0] h1[1,4] r[1,2] rest[1,5] t[1,0] xs[0,1] ~arg1[] ~arg1[0] ~arg1[0,0] ~arg1[1] ~arg1[1,0] ~arg2[] ~arg2[0] ~arg2[0,1] ~arg2[1] ~arg2[1,5] ~data0[1,2] ~h[1,4] ~h0[1,1] ~h1[1,3] ~r[1,6] ~rest[1,3] ~t[1,2] ~xs[0,2]
  -- cost: 2
  (arg3) <- (do
    xs <- pure arg2
    arg3 <- pure xs
    guard $ arg1 == []
    pure (arg3)
   ) <|> (do
    rest <- pure arg2
    (h0:t) <- pure arg1
    h <- pure h0
    h1 <- pure h
    data0 <- pure (h1:rest)
    (r) <- reverseDL_iio t data0
    arg3 <- pure r
    pure (arg3)
   )
  pure (arg3)

reverseDL_ioi = \arg1 arg3 -> do
  -- solution: arg2[] arg2[0] arg2[0,1] arg2[1] arg2[1,5] data0[1,2] h[1,1] h0[1,0] h1[1,3] r[1,6] rest[1,3] t[1,0] xs[0,2] ~arg1[] ~arg1[0] ~arg1[0,0] ~arg1[1] ~arg1[1,0] ~arg3[] ~arg3[0] ~arg3[0,2] ~arg3[1] ~arg3[1,6] ~data0[1,3] ~h[1,4] ~h0[1,1] ~h1[1,4] ~r[1,2] ~rest[1,5] ~t[1,2] ~xs[0,1]
  -- cost: 2
  (arg2) <- (do
    xs <- pure arg3
    arg2 <- pure xs
    guard $ arg1 == []
    pure (arg2)
   ) <|> (do
    r <- pure arg3
    (h0:t) <- pure arg1
    h <- pure h0
    (data0) <- reverseDL_ioi t r
    (h1:rest) <- pure data0
    arg2 <- pure rest
    guard $ h1 == h
    pure (arg2)
   )
  pure (arg2)

reverseDL_ooi = \arg3 -> do
  -- solution: arg1[] arg1[0] arg1[0,0] arg1[1] arg1[1,0] arg2[] arg2[0] arg2[0,1] arg2[1] arg2[1,5] data0[1,2] h[1,4] h0[1,1] h1[1,3] r[1,6] rest[1,3] t[1,2] xs[0,2] ~arg3[] ~arg3[0] ~arg3[0,2] ~arg3[1] ~arg3[1,6] ~data0[1,3] ~h[1,1] ~h0[1,0] ~h1[1,4] ~r[1,2] ~rest[1,5] ~t[1,0] ~xs[0,1]
  -- cost: 3
  (arg1,arg2) <- (do
    xs <- pure arg3
    arg2 <- pure xs
    arg1 <- pure []
    pure (arg1,arg2)
   ) <|> (do
    r <- pure arg3
    (t,data0) <- reverseDL_ooi r
    (h1:rest) <- pure data0
    arg2 <- pure rest
    h <- pure h1
    h0 <- pure h
    arg1 <- pure (h0:t)
    pure (arg1,arg2)
   )
  pure (arg1,arg2)

{- reverse/2
reverse s r :- ((reverseDL s data0 r, data0 = [])).
constraints:
~(data0[0,0] & data0[0,1])
(data0[0,0] | data0[0,1])
((s[0,0] & (data0[0,0] & ~r[0,0])) | ((~s[0,0] & (data0[0,0] & ~r[0,0])) | ((~s[0,0] & (~data0[0,0] & r[0,0])) | (~s[0,0] & (~data0[0,0] & ~r[0,0])))))
(r[] <-> r[0])
(r[0] <-> r[0,0])
(s[] <-> s[0])
(s[0] <-> s[0,0])
1
-}
reverse_ii = \s r -> once $ do
  -- solution: data0[0,1] ~data0[0,0] ~r[] ~r[0] ~r[0,0] ~s[] ~s[0] ~s[0,0]
  -- cost: 1
  () <- (do
    data0 <- pure []
    () <- reverseDL_iii s data0 r
    pure ()
   )
  pure ()

reverse_io = \s -> do
  -- solution: data0[0,1] r[] r[0] r[0,0] ~data0[0,0] ~s[] ~s[0] ~s[0,0]
  -- cost: 2
  (r) <- (do
    data0 <- pure []
    (r) <- reverseDL_iio s data0
    pure (r)
   )
  pure (r)

reverse_oi = \r -> do
  -- solution: data0[0,0] s[] s[0] s[0,0] ~data0[0,1] ~r[] ~r[0] ~r[0,0]
  -- cost: 3
  (s) <- (do
    (s,data0) <- reverseDL_ooi r
    guard $ data0 == []
    pure (s)
   )
  pure (s)

{- all/2
all p arg2 :- ((arg2 = []); (arg2 = h:t, if (p h) then (all p t) else (empty))).
constraints:
~h[1,1]
~h[1,1,0,0]
~p[]
~p[1,1,1]
~t[1,1,1]
~(arg2[1,0] & h[1,0])
~(h[1,0] & h[1,1])
~(t[1,0] & t[1,1])
(h[1,0] | h[1,1])
(t[1,0] | t[1,1])
(arg2[] <-> arg2[0])
(arg2[] <-> arg2[1])
(arg2[0] <-> arg2[0,0])
(arg2[1] <-> arg2[1,0])
(h[1,0] <-> t[1,0])
(h[1,1,0,0] <-> p(1))
(p[] <-> p[1])
(p[1] <-> p[1,1])
(p[1,1] <-> p[1,1,1])
(p[1,1,1] <-> p[1,1,1,0])
(p[1,1,1,0] <-> p[])
(t[1,1] <-> t[1,1,1])
(t[1,1,1] <-> t[1,1,1,0])
(t[1,1,1,0] <-> arg2[])
1
-}
all_p1ii = \p arg2 -> once $ do
  -- solution: h[1,0] t[1,0] ~arg2[] ~arg2[0] ~arg2[0,0] ~arg2[1] ~arg2[1,0] ~h[1,1] ~h[1,1,0,0] ~p[] ~p[1] ~p[1,1] ~p[1,1,1] ~p[1,1,1,0] ~t[1,1] ~t[1,1,1] ~t[1,1,1,0] ~p(1)
  -- cost: 3
  () <- (do
    guard $ arg2 == []
    pure ()
   ) <|> (do
    (h:t) <- pure arg2
    () <- ifte ((do
      () <- p h
      pure ()
     )) (\() -> (do
      () <- all_p1ii p t
      pure ()
     )) ((do
      () <- empty 
      pure ()
     ))
    pure ()
   )
  pure ()

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
multiple_ii = \x y -> once $ do
  -- solution: data0[0,1] ~data0[0,0] ~x[] ~x[0] ~x[0,0] ~y[] ~y[0] ~y[0,0]
  -- cost: 1
  () <- (do
    data0 <- pure 0
    () <- mod_iii x y data0
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
  -- cost: 3
  (x) <- (do
    data0 <- pure 0
    data1 <- pure 999
    data2 <- pure [data0..data1]
    (y) <- (do
      y <- pure 3
      pure (y)
     ) <|> (do
      y <- pure 5
      pure (y)
     )
    (x) <- elem_oi data2
    () <- multiple_ii x y
    pure (x)
   )
  pure (x)

{- euler1'/1
euler1' s :- ((observeAll pred0 r, (pred0 x :- (euler1 x)), sum r s)).
constraints:
x[0,1,0,0]
~pred0[0,0]
~x[0]
~(r[0,0] & r[0,2])
(~pred0[0,0] & (pred0(1) & r[0,0]))
(r[0,0] | r[0,2])
((~r[0,2] & s[0,2]) | (~r[0,2] & ~s[0,2]))
(s[] <-> s[0])
(s[0] <-> s[0,2])
(x[0,1,0] <-> x[0,1,0,0])
(pred0(1) <-> x[0,1,0])
1
-}
euler1'_i = \s -> once $ do
  -- solution: r[0,0] x[0,1,0] x[0,1,0,0] pred0(1) ~pred0[0,0] ~r[0,2] ~s[] ~s[0] ~s[0,2] ~x[0]
  -- cost: 5
  () <- (do
    let pred0 =
          do
            (x) <- (do
              (x) <- euler1_o 
              pure (x)
             )
            pure (x)
    (r) <- observeAll_p1oo pred0
    () <- sum_ii r s
    pure ()
   )
  pure ()

euler1'_o = do
  -- solution: r[0,0] s[] s[0] s[0,2] x[0,1,0] x[0,1,0,0] pred0(1) ~pred0[0,0] ~r[0,2] ~x[0]
  -- cost: 6
  (s) <- (do
    let pred0 =
          do
            (x) <- (do
              (x) <- euler1_o 
              pure (x)
             )
            pure (x)
    (r) <- observeAll_p1oo pred0
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
  -- cost: 11
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
  -- cost: 12
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

{- fib'/1
fib' f :- ((nat i, fib i f)).
constraints:
~(i[0,0] & i[0,1])
(i[0,0] | i[0,1])
(i[0,0] | ~i[0,0])
((i[0,1] & f[0,1]) | (~i[0,1] & f[0,1]))
(f[] <-> f[0])
(f[0] <-> f[0,1])
1
-}
fib'_o = do
  -- solution: f[] f[0] f[0,1] i[0,0] ~i[0,1]
  -- cost: 4
  (f) <- (do
    (i) <- nat_o 
    (f) <- fib_io i
    pure (f)
   )
  pure (f)

{- euler2/1
euler2 s :- ((observeAll pred0 fs, (pred0 x :- (fib' x, even x)), span pred2 fs xs _, data1 = 1000000, (pred2 x :- ((<) x data1, data1 = 1000000)), sum xs s)).
constraints:
data1[0,3]
x[0,1,0,0]
~pred0[0,0]
~pred2[0,2]
~x[0]
~x[0,1,0,1]
~(data1[0,4,0,0] & data1[0,4,0,1])
~(fs[0,0] & fs[0,2])
~(x[0,1,0,0] & x[0,1,0,1])
~(xs[0,2] & xs[0,5])
(~pred0[0,0] & (pred0(1) & fs[0,0]))
(~x[0,4,0,0] & ~data1[0,4,0,0])
(fs[0,0] | fs[0,2])
(xs[0,2] | xs[0,5])
((~pred2[0,2] & (~pred2(1) & (~fs[0,2] & xs[0,2]))) | (~pred2[0,2] & (~pred2(1) & (~fs[0,2] & ~xs[0,2]))))
((~xs[0,5] & s[0,5]) | (~xs[0,5] & ~s[0,5]))
(data1[0,4,0] <-> (data1[0,4,0,0] | data1[0,4,0,1]))
(s[] <-> s[0])
(s[0] <-> s[0,5])
(x[0,1,0] <-> (x[0,1,0,0] | x[0,1,0,1]))
(x[0,4,0] <-> x[0,4,0,0])
(pred0(1) <-> x[0,1,0])
(pred2(1) <-> x[0,4,0])
1
-}
euler2_i = \s -> once $ do
  -- solution: data1[0,3] data1[0,4,0] data1[0,4,0,1] fs[0,0] x[0,1,0] x[0,1,0,0] xs[0,2] pred0(1) ~data1[0,4,0,0] ~fs[0,2] ~pred0[0,0] ~pred2[0,2] ~s[] ~s[0] ~s[0,5] ~x[0] ~x[0,1,0,1] ~x[0,4,0] ~x[0,4,0,0] ~xs[0,5] ~pred2(1)
  -- cost: 10
  () <- (do
    data1 <- pure 1000000
    let pred0 =
          do
            (x) <- (do
              (x) <- fib'_o 
              () <- even_i x
              pure (x)
             )
            pure (x)
    let pred2 =
          \x -> do
            (data1) <- (do
              data1 <- pure 1000000
              guard $ (<) x data1
              pure (data1)
             )
            pure ()
    (fs) <- observeAll_p1oo pred0
    (xs,_) <- span_p1iioo pred2 fs
    () <- sum_ii xs s
    pure ()
   )
  pure ()

euler2_o = do
  -- solution: data1[0,3] data1[0,4,0] data1[0,4,0,1] fs[0,0] s[] s[0] s[0,5] x[0,1,0] x[0,1,0,0] xs[0,2] pred0(1) ~data1[0,4,0,0] ~fs[0,2] ~pred0[0,0] ~pred2[0,2] ~x[0] ~x[0,1,0,1] ~x[0,4,0] ~x[0,4,0,0] ~xs[0,5] ~pred2(1)
  -- cost: 11
  (s) <- (do
    data1 <- pure 1000000
    let pred0 =
          do
            (x) <- (do
              (x) <- fib'_o 
              () <- even_i x
              pure (x)
             )
            pure (x)
    let pred2 =
          \x -> do
            (data1) <- (do
              data1 <- pure 1000000
              guard $ (<) x data1
              pure (data1)
             )
            pure ()
    (fs) <- observeAll_p1oo pred0
    (xs,_) <- span_p1iioo pred2 fs
    (s) <- sum_io xs
    pure (s)
   )
  pure (s)

{- nontrivialDivisor/2
nontrivialDivisor n d :- ((succ n' n, elem d data1, data0 = 2, data1 = .. data0 n', mod n d data2, data2 = 0)).
constraints:
~(d[0,1] & d[0,4])
~(data0[0,2] & data0[0,3])
~(data1[0,1] & data1[0,3])
~(data1[0,3] & data0[0,3])
~(data2[0,4] & data2[0,5])
~(n[0,0] & n[0,4])
~(n'[0,0] & n'[0,3])
(d[0,1] & ~data1[0,1])
(data0[0,2] | data0[0,3])
(data1[0,1] | data1[0,3])
(data2[0,4] | data2[0,5])
(n'[0,0] | n'[0,3])
((n'[0,0] & ~n[0,0]) | ((~n'[0,0] & n[0,0]) | (~n'[0,0] & ~n[0,0])))
((~n[0,4] & (~d[0,4] & data2[0,4])) | (~n[0,4] & (~d[0,4] & ~data2[0,4])))
(d[] <-> d[0])
(d[0] <-> (d[0,1] | d[0,4]))
(data0[0,3] <-> n'[0,3])
(n[] <-> n[0])
(n[0] <-> (n[0,0] | n[0,4]))
1
-}
nontrivialDivisor_io = \n -> do
  -- solution: d[] d[0] d[0,1] data0[0,2] data1[0,3] data2[0,5] n'[0,0] ~d[0,4] ~data0[0,3] ~data1[0,1] ~data2[0,4] ~n[] ~n[0] ~n[0,0] ~n[0,4] ~n'[0,3]
  -- cost: 5
  (d) <- (do
    data2 <- pure 0
    data0 <- pure 2
    (n') <- succ_oi n
    data1 <- pure [data0..n']
    (d) <- elem_oi data1
    () <- mod_iii n d data2
    pure (d)
   )
  pure (d)

{- primeSlow/1
primeSlow n :- ((nat n, (>) n data0, data0 = 1, if (nontrivialDivisor n _) then (empty) else ())).
constraints:
_[0,3]
~n[0,3]
~n[0,3,0,0]
~(data0[0,1] & data0[0,2])
~(n[0,0] & n[0,1])
~(n[0,0] & n[0,3])
~(n[0,1] & n[0,3])
(~n[0,1] & ~data0[0,1])
(data0[0,1] | data0[0,2])
(n[0,0] | ~n[0,0])
(_[0] <-> _[0,3])
(n[] <-> n[0])
(n[0] <-> (n[0,0] | (n[0,1] | n[0,3])))
1
-}
primeSlow_i = \n -> once $ do
  -- solution: _[0] _[0,3] data0[0,2] ~data0[0,1] ~n[] ~n[0] ~n[0,0] ~n[0,1] ~n[0,3] ~n[0,3,0,0]
  -- cost: 5
  () <- (do
    data0 <- pure 1
    guard $ (>) n data0
    () <- nat_i n
    () <- ifte ((do
      (_) <- nontrivialDivisor_io n
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

primeSlow_o = do
  -- solution: _[0] _[0,3] data0[0,2] n[] n[0] n[0,0] ~data0[0,1] ~n[0,1] ~n[0,3] ~n[0,3,0,0]
  -- cost: 6
  (n) <- (do
    data0 <- pure 1
    (n) <- nat_o 
    guard $ (>) n data0
    () <- ifte ((do
      (_) <- nontrivialDivisor_io n
      pure ()
     )) (\() -> (do
      () <- empty 
      pure ()
     )) ((do
      
      pure ()
     ))
    pure (n)
   )
  pure (n)

{- factor/3
factor arg1 n f :- ((arg1 = p0:ps1, p0 = p, ps1 = ps, if (times p2 p3 pp, p2 = p, p3 = p, (>) pp n) then (f = n) else (if (divMod n p d data0, data0 = 0) then (((f = p); (factor data1 d f, data1 = p4:ps5, p4 = p, ps5 = ps))) else (factor ps n f)))).
constraints:
d[0,3,2,0,0]
data0[0,3,2,0]
p2[0,3]
p3[0,3]
pp[0,3]
~d[0,3,2,0,1,0]
~n[0,3,0,3]
~n[0,3,1,0]
~n[0,3,2]
~n[0,3,2,0,0,0]
~n[0,3,2,0,2]
~p[0,3,2]
~p[0,3,2,0]
~p[0,3,2,0,0,0]
~p[0,3,2,0,1,0]
~ps[0,3,2]
~ps[0,3,2,0,1,0]
~(arg1[0,0] & p0[0,0])
~(data0[0,3,2,0,0,0] & data0[0,3,2,0,0,1])
~(data1[0,3,2,0,1,0,1,0] & data1[0,3,2,0,1,0,1,1])
~(data1[0,3,2,0,1,0,1,1] & p4[0,3,2,0,1,0,1,1])
~(f[0,3,1,0] & n[0,3,1,0])
~(f[0,3,2,0,1,0,0,0] & p[0,3,2,0,1,0,0,0])
~(p[0,1] & p[0,3])
~(p[0,3,0,1] & p[0,3,0,2])
~(p0[0,0] & p0[0,1])
~(p0[0,1] & p[0,1])
~(p2[0,3,0,0] & p2[0,3,0,1])
~(p2[0,3,0,1] & p[0,3,0,1])
~(p3[0,3,0,0] & p3[0,3,0,2])
~(p3[0,3,0,2] & p[0,3,0,2])
~(p4[0,3,2,0,1,0,1,1] & p4[0,3,2,0,1,0,1,2])
~(p4[0,3,2,0,1,0,1,2] & p[0,3,2,0,1,0,1,2])
~(pp[0,3,0,0] & pp[0,3,0,3])
~(ps[0,2] & ps[0,3])
~(ps1[0,0] & ps1[0,2])
~(ps1[0,2] & ps[0,2])
~(ps5[0,3,2,0,1,0,1,1] & ps5[0,3,2,0,1,0,1,3])
~(ps5[0,3,2,0,1,0,1,3] & ps[0,3,2,0,1,0,1,3])
~(p[0,3,0,1] | p[0,3,0,2])
(~pp[0,3,0,3] & ~n[0,3,0,3])
(data0[0,3,2,0,0,0] | data0[0,3,2,0,0,1])
(data1[0,3,2,0,1,0,1,0] | data1[0,3,2,0,1,0,1,1])
(p[0,1] | p[0,3])
(p0[0,0] | p0[0,1])
(p2[0,3,0,0] | p2[0,3,0,1])
(p3[0,3,0,0] | p3[0,3,0,2])
(p4[0,3,2,0,1,0,1,1] | p4[0,3,2,0,1,0,1,2])
(pp[0,3,0,0] | pp[0,3,0,3])
(ps[0,2] | ps[0,3])
(ps1[0,0] | ps1[0,2])
(ps5[0,3,2,0,1,0,1,1] | ps5[0,3,2,0,1,0,1,3])
((p2[0,3,0,0] & (~p3[0,3,0,0] & ~pp[0,3,0,0])) | ((~p2[0,3,0,0] & (p3[0,3,0,0] & ~pp[0,3,0,0])) | (~p2[0,3,0,0] & (~p3[0,3,0,0] & pp[0,3,0,0]))))
((~n[0,3,2,0,0,0] & (~p[0,3,2,0,0,0] & (d[0,3,2,0,0,0] & data0[0,3,2,0,0,0]))) | ((~n[0,3,2,0,0,0] & (~p[0,3,2,0,0,0] & (d[0,3,2,0,0,0] & ~data0[0,3,2,0,0,0]))) | ((~n[0,3,2,0,0,0] & (~p[0,3,2,0,0,0] & (~d[0,3,2,0,0,0] & data0[0,3,2,0,0,0]))) | (~n[0,3,2,0,0,0] & (~p[0,3,2,0,0,0] & (~d[0,3,2,0,0,0] & ~data0[0,3,2,0,0,0]))))))
(arg1[] <-> arg1[0])
(arg1[0] <-> arg1[0,0])
(d[0,3,2,0,0] <-> d[0,3,2,0,0,0])
(d[0,3,2,0,1,0] <-> d[0,3,2,0,1,0,1])
(d[0,3,2,0,1,0,1] <-> d[0,3,2,0,1,0,1,0])
(d[0,3,2,0,1,0,1,0] <-> n[])
(data0[0] <-> data0[0,3])
(data0[0,3] <-> data0[0,3,2])
(data0[0,3,2] <-> data0[0,3,2,0])
(data1[0,3,2,0,1,0,1,0] <-> arg1[])
(f[] <-> f[0])
(f[0] <-> f[0,3])
(f[0,3] <-> (f[0,3,1] | f[0,3,2]))
(f[0,3,1] <-> f[0,3,1,0])
(f[0,3,1] <-> f[0,3,2])
(f[0,3,2] <-> f[0,3,2,0])
(f[0,3,2,0] <-> (f[0,3,2,0,1] | f[0,3,2,0,2]))
(f[0,3,2,0,1] <-> f[0,3,2,0,1,0])
(f[0,3,2,0,1] <-> f[0,3,2,0,2])
(f[0,3,2,0,1,0] <-> f[0,3,2,0,1,0,0])
(f[0,3,2,0,1,0] <-> f[0,3,2,0,1,0,1])
(f[0,3,2,0,1,0,0] <-> f[0,3,2,0,1,0,0,0])
(f[0,3,2,0,1,0,1] <-> f[0,3,2,0,1,0,1,0])
(f[0,3,2,0,1,0,1,0] <-> f[])
(f[0,3,2,0,2] <-> f[0,3,2,0,2,0])
(f[0,3,2,0,2,0] <-> f[])
(n[] <-> n[0])
(n[0] <-> n[0,3])
(n[0,3] <-> n[0,3,2])
(n[0,3,2] <-> n[0,3,2,0])
(n[0,3,2,0] <-> n[0,3,2,0,2])
(n[0,3,2,0,2] <-> n[0,3,2,0,2,0])
(n[0,3,2,0,2,0] <-> n[])
(p[0,3] <-> p[0,3,2])
(p[0,3,2] <-> p[0,3,2,0])
(p[0,3,2,0,1,0] <-> p[0,3,2,0,1,0,0])
(p[0,3,2,0,1,0] <-> p[0,3,2,0,1,0,1])
(p[0,3,2,0,1,0,0] <-> p[0,3,2,0,1,0,0,0])
(p[0,3,2,0,1,0,1] <-> p[0,3,2,0,1,0,1,2])
(p0[0,0] <-> ps1[0,0])
(p2[0] <-> p2[0,3])
(p3[0] <-> p3[0,3])
(p4[0,3,2,0,1,0,1,1] <-> ps5[0,3,2,0,1,0,1,1])
(pp[0] <-> pp[0,3])
(ps[0,3] <-> ps[0,3,2])
(ps[0,3,2] <-> ps[0,3,2,0])
(ps[0,3,2,0] <-> (ps[0,3,2,0,1] | ps[0,3,2,0,2]))
(ps[0,3,2,0,1] <-> ps[0,3,2,0,1,0])
(ps[0,3,2,0,1] <-> ps[0,3,2,0,2])
(ps[0,3,2,0,1,0] <-> ps[0,3,2,0,1,0,1])
(ps[0,3,2,0,1,0,1] <-> ps[0,3,2,0,1,0,1,3])
(ps[0,3,2,0,2] <-> ps[0,3,2,0,2,0])
(ps[0,3,2,0,2,0] <-> arg1[])
1
-}
factor_iii = \arg1 n f -> once $ do
  -- solution: d[0,3,2,0,0] d[0,3,2,0,0,0] data0[0] data0[0,3] data0[0,3,2] data0[0,3,2,0] data0[0,3,2,0,0,1] data1[0,3,2,0,1,0,1,1] p[0,1] p0[0,0] p2[0] p2[0,3] p2[0,3,0,1] p3[0] p3[0,3] p3[0,3,0,2] p4[0,3,2,0,1,0,1,2] pp[0] pp[0,3] pp[0,3,0,0] ps[0,2] ps1[0,0] ps5[0,3,2,0,1,0,1,3] ~arg1[] ~arg1[0] ~arg1[0,0] ~d[0,3,2,0,1,0] ~d[0,3,2,0,1,0,1] ~d[0,3,2,0,1,0,1,0] ~data0[0,3,2,0,0,0] ~data1[0,3,2,0,1,0,1,0] ~f[] ~f[0] ~f[0,3] ~f[0,3,1] ~f[0,3,1,0] ~f[0,3,2] ~f[0,3,2,0] ~f[0,3,2,0,1] ~f[0,3,2,0,1,0] ~f[0,3,2,0,1,0,0] ~f[0,3,2,0,1,0,0,0] ~f[0,3,2,0,1,0,1] ~f[0,3,2,0,1,0,1,0] ~f[0,3,2,0,2] ~f[0,3,2,0,2,0] ~n[] ~n[0] ~n[0,3] ~n[0,3,0,3] ~n[0,3,1,0] ~n[0,3,2] ~n[0,3,2,0] ~n[0,3,2,0,0,0] ~n[0,3,2,0,2] ~n[0,3,2,0,2,0] ~p[0,3] ~p[0,3,0,1] ~p[0,3,0,2] ~p[0,3,2] ~p[0,3,2,0] ~p[0,3,2,0,0,0] ~p[0,3,2,0,1,0] ~p[0,3,2,0,1,0,0] ~p[0,3,2,0,1,0,0,0] ~p[0,3,2,0,1,0,1] ~p[0,3,2,0,1,0,1,2] ~p0[0,1] ~p2[0,3,0,0] ~p3[0,3,0,0] ~p4[0,3,2,0,1,0,1,1] ~pp[0,3,0,3] ~ps[0,3] ~ps[0,3,2] ~ps[0,3,2,0] ~ps[0,3,2,0,1] ~ps[0,3,2,0,1,0] ~ps[0,3,2,0,1,0,1] ~ps[0,3,2,0,1,0,1,3] ~ps[0,3,2,0,2] ~ps[0,3,2,0,2,0] ~ps1[0,2] ~ps5[0,3,2,0,1,0,1,1]
  -- cost: 7
  () <- (do
    (p0:ps1) <- pure arg1
    p <- pure p0
    ps <- pure ps1
    () <- ifte ((do
      p2 <- pure p
      p3 <- pure p
      (pp) <- times_iio p2 p3
      guard $ (>) pp n
      pure ()
     )) (\() -> (do
      guard $ f == n
      pure ()
     )) ((do
      () <- ifte ((do
        data0 <- pure 0
        (d) <- divMod_iioi n p data0
        pure (d)
       )) (\(d) -> (do
        () <- (do
          guard $ f == p
          pure ()
         ) <|> (do
          p4 <- pure p
          ps5 <- pure ps
          data1 <- pure (p4:ps5)
          () <- factor_iii data1 d f
          pure ()
         )
        pure ()
       )) ((do
        () <- factor_iii ps n f
        pure ()
       ))
      pure ()
     ))
    pure ()
   )
  pure ()

factor_iio = \arg1 n -> do
  -- solution: d[0,3,2,0,0] d[0,3,2,0,0,0] data0[0] data0[0,3] data0[0,3,2] data0[0,3,2,0] data0[0,3,2,0,0,1] data1[0,3,2,0,1,0,1,1] f[] f[0] f[0,3] f[0,3,1] f[0,3,1,0] f[0,3,2] f[0,3,2,0] f[0,3,2,0,1] f[0,3,2,0,1,0] f[0,3,2,0,1,0,0] f[0,3,2,0,1,0,0,0] f[0,3,2,0,1,0,1] f[0,3,2,0,1,0,1,0] f[0,3,2,0,2] f[0,3,2,0,2,0] p[0,1] p0[0,0] p2[0] p2[0,3] p2[0,3,0,1] p3[0] p3[0,3] p3[0,3,0,2] p4[0,3,2,0,1,0,1,2] pp[0] pp[0,3] pp[0,3,0,0] ps[0,2] ps1[0,0] ps5[0,3,2,0,1,0,1,3] ~arg1[] ~arg1[0] ~arg1[0,0] ~d[0,3,2,0,1,0] ~d[0,3,2,0,1,0,1] ~d[0,3,2,0,1,0,1,0] ~data0[0,3,2,0,0,0] ~data1[0,3,2,0,1,0,1,0] ~n[] ~n[0] ~n[0,3] ~n[0,3,0,3] ~n[0,3,1,0] ~n[0,3,2] ~n[0,3,2,0] ~n[0,3,2,0,0,0] ~n[0,3,2,0,2] ~n[0,3,2,0,2,0] ~p[0,3] ~p[0,3,0,1] ~p[0,3,0,2] ~p[0,3,2] ~p[0,3,2,0] ~p[0,3,2,0,0,0] ~p[0,3,2,0,1,0] ~p[0,3,2,0,1,0,0] ~p[0,3,2,0,1,0,0,0] ~p[0,3,2,0,1,0,1] ~p[0,3,2,0,1,0,1,2] ~p0[0,1] ~p2[0,3,0,0] ~p3[0,3,0,0] ~p4[0,3,2,0,1,0,1,1] ~pp[0,3,0,3] ~ps[0,3] ~ps[0,3,2] ~ps[0,3,2,0] ~ps[0,3,2,0,1] ~ps[0,3,2,0,1,0] ~ps[0,3,2,0,1,0,1] ~ps[0,3,2,0,1,0,1,3] ~ps[0,3,2,0,2] ~ps[0,3,2,0,2,0] ~ps1[0,2] ~ps5[0,3,2,0,1,0,1,1]
  -- cost: 9
  (f) <- (do
    (p0:ps1) <- pure arg1
    p <- pure p0
    ps <- pure ps1
    (f) <- ifte ((do
      p2 <- pure p
      p3 <- pure p
      (pp) <- times_iio p2 p3
      guard $ (>) pp n
      pure ()
     )) (\() -> (do
      f <- pure n
      pure (f)
     )) ((do
      (f) <- ifte ((do
        data0 <- pure 0
        (d) <- divMod_iioi n p data0
        pure (d)
       )) (\(d) -> (do
        (f) <- (do
          f <- pure p
          pure (f)
         ) <|> (do
          p4 <- pure p
          ps5 <- pure ps
          data1 <- pure (p4:ps5)
          (f) <- factor_iio data1 d
          pure (f)
         )
        pure (f)
       )) ((do
        (f) <- factor_iio ps n
        pure (f)
       ))
      pure (f)
     ))
    pure (f)
   )
  pure (f)

{- prime/1
prime arg1 :- ((arg1 = 2); (oddNat p, (>) p data0, data0 = 2, observeAll pred1 primes, (pred1 x :- (prime x)), if (factor primes p d, (/=) p d) then (empty) else (), arg1 = p)).
constraints:
d[1,5]
~p[1,5]
~pred1[1,3]
~primes[1,5]
~primes[1,5,0,0]
~x[1]
~(arg1[1,6] & p[1,6])
~(d[1,5,0,0] & d[1,5,0,1])
~(data0[1,1] & data0[1,2])
~(p[1,0] & p[1,1])
~(p[1,0] & p[1,5])
~(p[1,0] & p[1,6])
~(p[1,1] & p[1,5])
~(p[1,1] & p[1,6])
~(p[1,5] & p[1,6])
~(p[1,5,0,0] & p[1,5,0,1])
~(primes[1,3] & primes[1,5])
~(p[1,5,0,0] | p[1,5,0,1])
(~p[1,1] & ~data0[1,1])
(~p[1,5,0,1] & ~d[1,5,0,1])
(~pred1[1,3] & (pred1(1) & primes[1,3]))
(d[1,5,0,0] | d[1,5,0,1])
(data0[1,1] | data0[1,2])
(p[1,0] | ~p[1,0])
(p[1,0] | (p[1,1] | (p[1,5] | p[1,6])))
(primes[1,3] | primes[1,5])
((~primes[1,5,0,0] & (~p[1,5,0,0] & d[1,5,0,0])) | (~primes[1,5,0,0] & (~p[1,5,0,0] & ~d[1,5,0,0])))
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg1[0] <-> arg1[0,0])
(arg1[1] <-> arg1[1,6])
(d[1] <-> d[1,5])
(x[1,4,0] <-> x[1,4,0,0])
(x[1,4,0,0] <-> arg1[])
(pred1(1) <-> x[1,4,0])
1
-}
prime_o = choose . observeAll $ do
  -- solution: arg1[] arg1[0] arg1[0,0] arg1[1] arg1[1,6] d[1] d[1,5] d[1,5,0,0] data0[1,2] p[1,0] primes[1,3] x[1,4,0] x[1,4,0,0] pred1(1) ~d[1,5,0,1] ~data0[1,1] ~p[1,1] ~p[1,5] ~p[1,5,0,0] ~p[1,5,0,1] ~p[1,6] ~pred1[1,3] ~primes[1,5] ~primes[1,5,0,0] ~x[1]
  -- cost: 11
  (arg1) <- (do
    arg1 <- pure 2
    pure (arg1)
   ) <|> (do
    data0 <- pure 2
    (p) <- oddNat_o 
    arg1 <- pure p
    guard $ (>) p data0
    let pred1 =
          do
            (x) <- (do
              (x) <- prime_o 
              pure (x)
             )
            pure (x)
    (primes) <- observeAll_p1oo pred1
    () <- ifte ((do
      (d) <- factor_iio primes p
      guard $ (/=) p d
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

{- primeFactor/2
primeFactor n d :- ((observeAll pred0 primes, (pred0 x :- (prime x)), factor primes n d)).
constraints:
x[0,1,0,0]
~pred0[0,0]
~x[0]
~(primes[0,0] & primes[0,2])
(~pred0[0,0] & (pred0(1) & primes[0,0]))
(primes[0,0] | primes[0,2])
((~primes[0,2] & (~n[0,2] & d[0,2])) | (~primes[0,2] & (~n[0,2] & ~d[0,2])))
(d[] <-> d[0])
(d[0] <-> d[0,2])
(n[] <-> n[0])
(n[0] <-> n[0,2])
(x[0,1,0] <-> x[0,1,0,0])
(pred0(1) <-> x[0,1,0])
1
-}
primeFactor_ii = \n d -> once $ do
  -- solution: primes[0,0] x[0,1,0] x[0,1,0,0] pred0(1) ~d[] ~d[0] ~d[0,2] ~n[] ~n[0] ~n[0,2] ~pred0[0,0] ~primes[0,2] ~x[0]
  -- cost: 5
  () <- (do
    let pred0 =
          do
            (x) <- (do
              (x) <- prime_o 
              pure (x)
             )
            pure (x)
    (primes) <- observeAll_p1oo pred0
    () <- factor_iii primes n d
    pure ()
   )
  pure ()

primeFactor_io = \n -> do
  -- solution: d[] d[0] d[0,2] primes[0,0] x[0,1,0] x[0,1,0,0] pred0(1) ~n[] ~n[0] ~n[0,2] ~pred0[0,0] ~primes[0,2] ~x[0]
  -- cost: 6
  (d) <- (do
    let pred0 =
          do
            (x) <- (do
              (x) <- prime_o 
              pure (x)
             )
            pure (x)
    (primes) <- observeAll_p1oo pred0
    (d) <- factor_iio primes n
    pure (d)
   )
  pure (d)

{- euler3/2
euler3 n r :- ((observeAll pred0 fs, (pred0 d :- (primeFactor n d)), maximum fs r)).
constraints:
~d[0]
~n[0]
~pred0[0,0]
~(fs[0,0] & fs[0,2])
(~pred0[0,0] & (pred0(1) & fs[0,0]))
(fs[0,0] | fs[0,2])
((~fs[0,2] & r[0,2]) | (~fs[0,2] & ~r[0,2]))
((~n[0,1,0,0] & d[0,1,0,0]) | (~n[0,1,0,0] & ~d[0,1,0,0]))
(d[0,1,0] <-> d[0,1,0,0])
(n[] <-> n[0])
(n[0,1,0] <-> n[0,1,0,0])
(r[] <-> r[0])
(r[0] <-> r[0,2])
(pred0(1) <-> d[0,1,0])
1
-}
euler3_ii = \n r -> once $ do
  -- solution: d[0,1,0] d[0,1,0,0] fs[0,0] pred0(1) ~d[0] ~fs[0,2] ~n[] ~n[0] ~n[0,1,0] ~n[0,1,0,0] ~pred0[0,0] ~r[] ~r[0] ~r[0,2]
  -- cost: 5
  () <- (do
    let pred0 =
          do
            (d) <- (do
              (d) <- primeFactor_io n
              pure (d)
             )
            pure (d)
    (fs) <- observeAll_p1oo pred0
    () <- maximum_ii fs r
    pure ()
   )
  pure ()

euler3_io = \n -> do
  -- solution: d[0,1,0] d[0,1,0,0] fs[0,0] r[] r[0] r[0,2] pred0(1) ~d[0] ~fs[0,2] ~n[] ~n[0] ~n[0,1,0] ~n[0,1,0,0] ~pred0[0,0]
  -- cost: 6
  (r) <- (do
    let pred0 =
          do
            (d) <- (do
              (d) <- primeFactor_io n
              pure (d)
             )
            pure (d)
    (fs) <- observeAll_p1oo pred0
    (r) <- maximum_io fs
    pure (r)
   )
  pure (r)

{- euler4/1
euler4 n :- ((elem x data2, data0 = 10, data1 = 99, data2 = .. data0 data1, elem y data5, data3 = 10, data4 = 99, data5 = .. data3 data4, times x y n, show n s, reverse s0 s1, s0 = s, s1 = s)).
constraints:
~(data0[0,1] & data0[0,3])
~(data1[0,2] & data1[0,3])
~(data2[0,0] & data2[0,3])
~(data2[0,3] & data0[0,3])
~(data3[0,5] & data3[0,7])
~(data4[0,6] & data4[0,7])
~(data5[0,4] & data5[0,7])
~(data5[0,7] & data3[0,7])
~(n[0,8] & n[0,9])
~(s[0,9] & s[0,11])
~(s[0,9] & s[0,12])
~(s[0,11] & s[0,12])
~(s0[0,10] & s0[0,11])
~(s0[0,11] & s[0,11])
~(s1[0,10] & s1[0,12])
~(s1[0,12] & s[0,12])
~(x[0,0] & x[0,8])
~(y[0,4] & y[0,8])
(x[0,0] & ~data2[0,0])
(y[0,4] & ~data5[0,4])
(data0[0,1] | data0[0,3])
(data1[0,2] | data1[0,3])
(data2[0,0] | data2[0,3])
(data3[0,5] | data3[0,7])
(data4[0,6] | data4[0,7])
(data5[0,4] | data5[0,7])
(s[0,9] | (s[0,11] | s[0,12]))
(s0[0,10] | s0[0,11])
(s1[0,10] | s1[0,12])
(x[0,0] | x[0,8])
(y[0,4] | y[0,8])
((n[0,9] & ~s[0,9]) | ((~n[0,9] & s[0,9]) | (~n[0,9] & ~s[0,9])))
((s0[0,10] & ~s1[0,10]) | ((~s0[0,10] & s1[0,10]) | (~s0[0,10] & ~s1[0,10])))
((x[0,8] & (~y[0,8] & ~n[0,8])) | ((~x[0,8] & (y[0,8] & ~n[0,8])) | (~x[0,8] & (~y[0,8] & n[0,8]))))
(data0[0,3] <-> data1[0,3])
(data3[0,7] <-> data4[0,7])
(n[] <-> n[0])
(n[0] <-> (n[0,8] | n[0,9]))
1
-}
--mode ordering failure, cyclic dependency: [10] reverse s0::o s1::i -> [11] s0::i = s::o -> [12] s1::o = s::i
--mode ordering failure, cyclic dependency: [10] reverse s0::i s1::o -> [12] s1::i = s::o -> [11] s0::o = s::i
euler4_o = do
  -- solution: data0[0,1] data1[0,2] data2[0,3] data3[0,5] data4[0,6] data5[0,7] n[] n[0] n[0,8] s[0,9] s0[0,11] s1[0,12] x[0,0] y[0,4] ~data0[0,3] ~data1[0,3] ~data2[0,0] ~data3[0,7] ~data4[0,7] ~data5[0,4] ~n[0,9] ~s[0,11] ~s[0,12] ~s0[0,10] ~s1[0,10] ~x[0,8] ~y[0,8]
  -- cost: 9
  (n) <- (do
    data0 <- pure 10
    data3 <- pure 10
    data1 <- pure 99
    data2 <- pure [data0..data1]
    data4 <- pure 99
    data5 <- pure [data3..data4]
    (x) <- elem_oi data2
    (y) <- elem_oi data5
    (n) <- times_iio x y
    (s) <- show_io n
    s0 <- pure s
    s1 <- pure s
    () <- reverse_ii s0 s1
    pure (n)
   )
  pure (n)

{- euler4'/1
euler4' n :- ((observeAll pred0 s, (pred0 x :- (euler4 x)), maximum s n)).
constraints:
x[0,1,0,0]
~pred0[0,0]
~x[0]
~(s[0,0] & s[0,2])
(~pred0[0,0] & (pred0(1) & s[0,0]))
(s[0,0] | s[0,2])
((~s[0,2] & n[0,2]) | (~s[0,2] & ~n[0,2]))
(n[] <-> n[0])
(n[0] <-> n[0,2])
(x[0,1,0] <-> x[0,1,0,0])
(pred0(1) <-> x[0,1,0])
1
-}
euler4'_i = \n -> once $ do
  -- solution: s[0,0] x[0,1,0] x[0,1,0,0] pred0(1) ~n[] ~n[0] ~n[0,2] ~pred0[0,0] ~s[0,2] ~x[0]
  -- cost: 5
  () <- (do
    let pred0 =
          do
            (x) <- (do
              (x) <- euler4_o 
              pure (x)
             )
            pure (x)
    (s) <- observeAll_p1oo pred0
    () <- maximum_ii s n
    pure ()
   )
  pure ()

euler4'_o = do
  -- solution: n[] n[0] n[0,2] s[0,0] x[0,1,0] x[0,1,0,0] pred0(1) ~pred0[0,0] ~s[0,2] ~x[0]
  -- cost: 6
  (n) <- (do
    let pred0 =
          do
            (x) <- (do
              (x) <- euler4_o 
              pure (x)
             )
            pure (x)
    (s) <- observeAll_p1oo pred0
    (n) <- maximum_io s
    pure (n)
   )
  pure (n)

{- euler5/1
euler5 n :- ((nat n, (>) n data0, data0 = 0, all pred1 data4, data2 = 1, data3 = 5, data4 = .. data2 data3, (pred1 x :- (multiple n x)))).
constraints:
~pred1[0,3]
~x[0]
~(data0[0,1] & data0[0,2])
~(data2[0,4] & data2[0,6])
~(data3[0,5] & data3[0,6])
~(data4[0,3] & data4[0,6])
~(data4[0,6] & data2[0,6])
~(n[0,0] & n[0,1])
(~n[0,1] & ~data0[0,1])
(~n[0,7,0,0] & ~x[0,7,0,0])
(~pred1[0,3] & (~pred1(1) & ~data4[0,3]))
(data0[0,1] | data0[0,2])
(data2[0,4] | data2[0,6])
(data3[0,5] | data3[0,6])
(data4[0,3] | data4[0,6])
(n[0,0] | ~n[0,0])
(data2[0,6] <-> data3[0,6])
(n[] <-> n[0])
(n[0] <-> (n[0,0] | n[0,1]))
(n[0,7,0] <-> n[0,7,0,0])
(x[0,7,0] <-> x[0,7,0,0])
(pred1(1) <-> x[0,7,0])
1
-}
euler5_i = \n -> once $ do
  -- solution: data0[0,2] data2[0,4] data3[0,5] data4[0,6] ~data0[0,1] ~data2[0,6] ~data3[0,6] ~data4[0,3] ~n[] ~n[0] ~n[0,0] ~n[0,1] ~n[0,7,0] ~n[0,7,0,0] ~pred1[0,3] ~x[0] ~x[0,7,0] ~x[0,7,0,0] ~pred1(1)
  -- cost: 4
  () <- (do
    data0 <- pure 0
    data2 <- pure 1
    data3 <- pure 5
    data4 <- pure [data2..data3]
    guard $ (>) n data0
    () <- nat_i n
    let pred1 =
          \x -> do
            () <- (do
              () <- multiple_ii n x
              pure ()
             )
            pure ()
    () <- all_p1ii pred1 data4
    pure ()
   )
  pure ()

euler5_o = do
  -- solution: data0[0,2] data2[0,4] data3[0,5] data4[0,6] n[] n[0] n[0,0] ~data0[0,1] ~data2[0,6] ~data3[0,6] ~data4[0,3] ~n[0,1] ~n[0,7,0] ~n[0,7,0,0] ~pred1[0,3] ~x[0] ~x[0,7,0] ~x[0,7,0,0] ~pred1(1)
  -- cost: 5
  (n) <- (do
    data0 <- pure 0
    data2 <- pure 1
    data3 <- pure 5
    data4 <- pure [data2..data3]
    (n) <- nat_o 
    guard $ (>) n data0
    let pred1 =
          \x -> do
            () <- (do
              () <- multiple_ii n x
              pure ()
             )
            pure ()
    () <- all_p1ii pred1 data4
    pure (n)
   )
  pure (n)
