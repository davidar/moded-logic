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
  -- solution: data0[0,1] data1[0,0] ~data0[0,0] ~data1[0,2] ~x[] ~x[0] ~x[0,0]
  () <- (do
    data0 <- pure 2
    (data1) <- mod_iio x data0
    guard $ data1 == 0
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
~p[0,0]
~x[0]
~(r[0,0] & r[0,1])
(~p[0,0] & (p(1) & r[0,0]))
(r[0,0] | r[0,1])
((~r[0,1] & s[0,1]) | (~r[0,1] & ~s[0,1]))
(s[] <-> s[0])
(s[0] <-> s[0,1])
(x[0,2,0] <-> x[0,2,0,0])
(p(1) <-> x[0,2,0])
1
-}
euler1'_i = \s -> once $ do
  -- solution: r[0,0] x[0,2,0] x[0,2,0,0] p(1) ~p[0,0] ~r[0,1] ~s[] ~s[0] ~s[0,1] ~x[0]
  () <- (do
    let p =
          do
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
  -- solution: r[0,0] s[] s[0] s[0,1] x[0,2,0] x[0,2,0,0] p(1) ~p[0,0] ~r[0,1] ~x[0]
  (s) <- (do
    let p =
          do
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
  (f) <- (do
    (i) <- nat_o 
    (f) <- fib_io i
    pure (f)
   )
  pure (f)

{- euler2/1
euler2 s :- ((observeAll p fs, span q fs xs _, sum xs s, (p x :- (fib' x, even x)), (q x :- ((<) x data0, data0 = 1000000)))).
constraints:
x[0,3,0,0]
~p[0,0]
~q[0,1]
~x[0]
~x[0,3,0,1]
~(data0[0,4,0,0] & data0[0,4,0,1])
~(fs[0,0] & fs[0,1])
~(x[0,3,0,0] & x[0,3,0,1])
~(xs[0,1] & xs[0,2])
(~p[0,0] & (p(1) & fs[0,0]))
(~x[0,4,0,0] & ~data0[0,4,0,0])
(data0[0,4,0,0] | data0[0,4,0,1])
(fs[0,0] | fs[0,1])
(xs[0,1] | xs[0,2])
((~q[0,1] & (~q(1) & (~fs[0,1] & xs[0,1]))) | (~q[0,1] & (~q(1) & (~fs[0,1] & ~xs[0,1]))))
((~xs[0,2] & s[0,2]) | (~xs[0,2] & ~s[0,2]))
(data0[0] <-> data0[0,4])
(s[] <-> s[0])
(s[0] <-> s[0,2])
(x[0,3,0] <-> (x[0,3,0,0] | x[0,3,0,1]))
(x[0,4,0] <-> x[0,4,0,0])
(p(1) <-> x[0,3,0])
(q(1) <-> x[0,4,0])
1
-}
euler2_i = \s -> once $ do
  -- solution: data0[0,4,0,1] fs[0,0] x[0,3,0] x[0,3,0,0] xs[0,1] p(1) ~data0[0] ~data0[0,4] ~data0[0,4,0,0] ~fs[0,1] ~p[0,0] ~q[0,1] ~s[] ~s[0] ~s[0,2] ~x[0] ~x[0,3,0,1] ~x[0,4,0] ~x[0,4,0,0] ~xs[0,2] ~q(1)
  () <- (do
    let p =
          do
            (x) <- (do
              (x) <- fib'_o 
              () <- even_i x
              pure (x)
             )
            pure (x)
    (fs) <- observeAll_p1oo p
    let q =
          \x -> do
            () <- (do
              data0 <- pure 1000000
              guard $ (<) x data0
              pure ()
             )
            pure ()
    (xs,_) <- span_p1iioo q fs
    () <- sum_ii xs s
    pure ()
   )
  pure ()

euler2_o = do
  -- solution: data0[0,4,0,1] fs[0,0] s[] s[0] s[0,2] x[0,3,0] x[0,3,0,0] xs[0,1] p(1) ~data0[0] ~data0[0,4] ~data0[0,4,0,0] ~fs[0,1] ~p[0,0] ~q[0,1] ~x[0] ~x[0,3,0,1] ~x[0,4,0] ~x[0,4,0,0] ~xs[0,2] ~q(1)
  (s) <- (do
    let p =
          do
            (x) <- (do
              (x) <- fib'_o 
              () <- even_i x
              pure (x)
             )
            pure (x)
    (fs) <- observeAll_p1oo p
    let q =
          \x -> do
            () <- (do
              data0 <- pure 1000000
              guard $ (<) x data0
              pure ()
             )
            pure ()
    (xs,_) <- span_p1iioo q fs
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
  -- solution: d[] d[0] d[0,1] data0[0,2] data1[0,3] data2[0,4] n'[0,0] ~d[0,4] ~data0[0,3] ~data1[0,1] ~data2[0,5] ~n[] ~n[0] ~n[0,0] ~n[0,4] ~n'[0,3]
  (d) <- (do
    data0 <- pure 2
    (n') <- succ_oi n
    data1 <- pure [data0..n']
    (d) <- elem_oi data1
    (data2) <- mod_iio n d
    guard $ data2 == 0
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
  -- solution: d[0,3,2,0,0] d[0,3,2,0,0,0] data0[0] data0[0,3] data0[0,3,2] data0[0,3,2,0] data0[0,3,2,0,0,0] data1[0,3,2,0,1,0,1,1] p[0,1] p0[0,0] p2[0] p2[0,3] p2[0,3,0,1] p3[0] p3[0,3] p3[0,3,0,2] p4[0,3,2,0,1,0,1,2] pp[0] pp[0,3] pp[0,3,0,0] ps[0,2] ps1[0,0] ps5[0,3,2,0,1,0,1,3] ~arg1[] ~arg1[0] ~arg1[0,0] ~d[0,3,2,0,1,0] ~d[0,3,2,0,1,0,1] ~d[0,3,2,0,1,0,1,0] ~data0[0,3,2,0,0,1] ~data1[0,3,2,0,1,0,1,0] ~f[] ~f[0] ~f[0,3] ~f[0,3,1] ~f[0,3,1,0] ~f[0,3,2] ~f[0,3,2,0] ~f[0,3,2,0,1] ~f[0,3,2,0,1,0] ~f[0,3,2,0,1,0,0] ~f[0,3,2,0,1,0,0,0] ~f[0,3,2,0,1,0,1] ~f[0,3,2,0,1,0,1,0] ~f[0,3,2,0,2] ~f[0,3,2,0,2,0] ~n[] ~n[0] ~n[0,3] ~n[0,3,0,3] ~n[0,3,1,0] ~n[0,3,2] ~n[0,3,2,0] ~n[0,3,2,0,0,0] ~n[0,3,2,0,2] ~n[0,3,2,0,2,0] ~p[0,3] ~p[0,3,0,1] ~p[0,3,0,2] ~p[0,3,2] ~p[0,3,2,0] ~p[0,3,2,0,0,0] ~p[0,3,2,0,1,0] ~p[0,3,2,0,1,0,0] ~p[0,3,2,0,1,0,0,0] ~p[0,3,2,0,1,0,1] ~p[0,3,2,0,1,0,1,2] ~p0[0,1] ~p2[0,3,0,0] ~p3[0,3,0,0] ~p4[0,3,2,0,1,0,1,1] ~pp[0,3,0,3] ~ps[0,3] ~ps[0,3,2] ~ps[0,3,2,0] ~ps[0,3,2,0,1] ~ps[0,3,2,0,1,0] ~ps[0,3,2,0,1,0,1] ~ps[0,3,2,0,1,0,1,3] ~ps[0,3,2,0,2] ~ps[0,3,2,0,2,0] ~ps1[0,2] ~ps5[0,3,2,0,1,0,1,1]
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
        (d,data0) <- divMod_iioo n p
        guard $ data0 == 0
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
  -- solution: d[0,3,2,0,0] d[0,3,2,0,0,0] data0[0] data0[0,3] data0[0,3,2] data0[0,3,2,0] data0[0,3,2,0,0,0] data1[0,3,2,0,1,0,1,1] f[] f[0] f[0,3] f[0,3,1] f[0,3,1,0] f[0,3,2] f[0,3,2,0] f[0,3,2,0,1] f[0,3,2,0,1,0] f[0,3,2,0,1,0,0] f[0,3,2,0,1,0,0,0] f[0,3,2,0,1,0,1] f[0,3,2,0,1,0,1,0] f[0,3,2,0,2] f[0,3,2,0,2,0] p[0,1] p0[0,0] p2[0] p2[0,3] p2[0,3,0,1] p3[0] p3[0,3] p3[0,3,0,2] p4[0,3,2,0,1,0,1,2] pp[0] pp[0,3] pp[0,3,0,0] ps[0,2] ps1[0,0] ps5[0,3,2,0,1,0,1,3] ~arg1[] ~arg1[0] ~arg1[0,0] ~d[0,3,2,0,1,0] ~d[0,3,2,0,1,0,1] ~d[0,3,2,0,1,0,1,0] ~data0[0,3,2,0,0,1] ~data1[0,3,2,0,1,0,1,0] ~n[] ~n[0] ~n[0,3] ~n[0,3,0,3] ~n[0,3,1,0] ~n[0,3,2] ~n[0,3,2,0] ~n[0,3,2,0,0,0] ~n[0,3,2,0,2] ~n[0,3,2,0,2,0] ~p[0,3] ~p[0,3,0,1] ~p[0,3,0,2] ~p[0,3,2] ~p[0,3,2,0] ~p[0,3,2,0,0,0] ~p[0,3,2,0,1,0] ~p[0,3,2,0,1,0,0] ~p[0,3,2,0,1,0,0,0] ~p[0,3,2,0,1,0,1] ~p[0,3,2,0,1,0,1,2] ~p0[0,1] ~p2[0,3,0,0] ~p3[0,3,0,0] ~p4[0,3,2,0,1,0,1,1] ~pp[0,3,0,3] ~ps[0,3] ~ps[0,3,2] ~ps[0,3,2,0] ~ps[0,3,2,0,1] ~ps[0,3,2,0,1,0] ~ps[0,3,2,0,1,0,1] ~ps[0,3,2,0,1,0,1,3] ~ps[0,3,2,0,2] ~ps[0,3,2,0,2,0] ~ps1[0,2] ~ps5[0,3,2,0,1,0,1,1]
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
        (d,data0) <- divMod_iioo n p
        guard $ data0 == 0
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
prime arg1 :- ((arg1 = 2); (oddNat p, (>) p data0, data0 = 2, observeAll q primes, (q x :- (prime x)), if (factor primes p d, (/=) p d) then (empty) else (), arg1 = p)).
constraints:
d[1,5]
~p[1,5]
~primes[1,5]
~primes[1,5,0,0]
~q[1,3]
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
(~q[1,3] & (q(1) & primes[1,3]))
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
(q(1) <-> x[1,4,0])
1
-}
prime_o = choose . observeAll $ do
  -- solution: arg1[] arg1[0] arg1[0,0] arg1[1] arg1[1,6] d[1] d[1,5] d[1,5,0,0] data0[1,2] p[1,0] primes[1,3] x[1,4,0] x[1,4,0,0] q(1) ~d[1,5,0,1] ~data0[1,1] ~p[1,1] ~p[1,5] ~p[1,5,0,0] ~p[1,5,0,1] ~p[1,6] ~primes[1,5] ~primes[1,5,0,0] ~q[1,3] ~x[1]
  (arg1) <- (do
    arg1 <- pure 2
    pure (arg1)
   ) <|> (do
    data0 <- pure 2
    (p) <- oddNat_o 
    arg1 <- pure p
    guard $ (>) p data0
    let q =
          do
            (x) <- (do
              (x) <- prime_o 
              pure (x)
             )
            pure (x)
    (primes) <- observeAll_p1oo q
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
primeFactor n d :- ((observeAll p primes, factor primes n d, (p x :- (prime x)))).
constraints:
x[0,2,0,0]
~p[0,0]
~x[0]
~(primes[0,0] & primes[0,1])
(~p[0,0] & (p(1) & primes[0,0]))
(primes[0,0] | primes[0,1])
((~primes[0,1] & (~n[0,1] & d[0,1])) | (~primes[0,1] & (~n[0,1] & ~d[0,1])))
(d[] <-> d[0])
(d[0] <-> d[0,1])
(n[] <-> n[0])
(n[0] <-> n[0,1])
(x[0,2,0] <-> x[0,2,0,0])
(p(1) <-> x[0,2,0])
1
-}
primeFactor_ii = \n d -> once $ do
  -- solution: primes[0,0] x[0,2,0] x[0,2,0,0] p(1) ~d[] ~d[0] ~d[0,1] ~n[] ~n[0] ~n[0,1] ~p[0,0] ~primes[0,1] ~x[0]
  () <- (do
    let p =
          do
            (x) <- (do
              (x) <- prime_o 
              pure (x)
             )
            pure (x)
    (primes) <- observeAll_p1oo p
    () <- factor_iii primes n d
    pure ()
   )
  pure ()

primeFactor_io = \n -> do
  -- solution: d[] d[0] d[0,1] primes[0,0] x[0,2,0] x[0,2,0,0] p(1) ~n[] ~n[0] ~n[0,1] ~p[0,0] ~primes[0,1] ~x[0]
  (d) <- (do
    let p =
          do
            (x) <- (do
              (x) <- prime_o 
              pure (x)
             )
            pure (x)
    (primes) <- observeAll_p1oo p
    (d) <- factor_iio primes n
    pure (d)
   )
  pure (d)

{- euler3/2
euler3 n r :- ((observeAll p fs, maximum fs r, (p d :- (primeFactor n d)))).
constraints:
~d[0]
~n[0]
~p[0,0]
~(fs[0,0] & fs[0,1])
(~p[0,0] & (p(1) & fs[0,0]))
(fs[0,0] | fs[0,1])
((~fs[0,1] & r[0,1]) | (~fs[0,1] & ~r[0,1]))
((~n[0,2,0,0] & d[0,2,0,0]) | (~n[0,2,0,0] & ~d[0,2,0,0]))
(d[0,2,0] <-> d[0,2,0,0])
(n[] <-> n[0])
(n[0,2,0] <-> n[0,2,0,0])
(r[] <-> r[0])
(r[0] <-> r[0,1])
(p(1) <-> d[0,2,0])
1
-}
euler3_ii = \n r -> once $ do
  -- solution: d[0,2,0] d[0,2,0,0] fs[0,0] p(1) ~d[0] ~fs[0,1] ~n[] ~n[0] ~n[0,2,0] ~n[0,2,0,0] ~p[0,0] ~r[] ~r[0] ~r[0,1]
  () <- (do
    let p =
          do
            (d) <- (do
              (d) <- primeFactor_io n
              pure (d)
             )
            pure (d)
    (fs) <- observeAll_p1oo p
    () <- maximum_ii fs r
    pure ()
   )
  pure ()

euler3_io = \n -> do
  -- solution: d[0,2,0] d[0,2,0,0] fs[0,0] r[] r[0] r[0,1] p(1) ~d[0] ~fs[0,1] ~n[] ~n[0] ~n[0,2,0] ~n[0,2,0,0] ~p[0,0]
  (r) <- (do
    let p =
          do
            (d) <- (do
              (d) <- primeFactor_io n
              pure (d)
             )
            pure (d)
    (fs) <- observeAll_p1oo p
    (r) <- maximum_io fs
    pure (r)
   )
  pure (r)
