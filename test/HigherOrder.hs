{-# LANGUAGE NoMonomorphismRestriction #-}
module HigherOrder where

import Control.Applicative
import Control.Monad.Logic
import Control.Monad.Logic.Moded.Prelude
import Data.List
import Data.MemoTrie

{- even/1
even n :- ((mod n data0 data1, data0 = 2, data1 = 0)).
constraints:
~(data0[0,0] & data0[0,1])
~(data1[0,0] & data1[0,2])
(data0[0,0] | data0[0,1])
(data1[0,0] | data1[0,2])
((~n[0,0] & (~data0[0,0] & data1[0,0])) | (~n[0,0] & (~data0[0,0] & ~data1[0,0])))
(n[] <-> n[0])
(n[0] <-> n[0,0])
1
-}
even_i = \n -> once $ do
  -- solution: data0[0,1] data1[0,0] ~data0[0,0] ~data1[0,2] ~n[] ~n[0] ~n[0,0]
  () <- (do
    data0 <- pure 2
    (data1) <- mod_iio n data0
    guard $ data1 == 0
    pure ()
   )
  pure ()

{- map/3
map p arg2 arg3 :- ((arg2 = [], arg3 = []); (arg2 = x:xs, arg3 = y:ys, p x y, map p xs ys)).
constraints:
~p[]
~(arg2[1,0] & x[1,0])
~(arg3[1,1] & y[1,1])
~(x[1,0] & x[1,2])
~(xs[1,0] & xs[1,3])
~(y[1,1] & y[1,2])
~(ys[1,1] & ys[1,3])
(x[1,0] | x[1,2])
(xs[1,0] | xs[1,3])
(y[1,1] | y[1,2])
(ys[1,1] | ys[1,3])
(arg2[] <-> arg2[0])
(arg2[] <-> arg2[1])
(arg2[0] <-> arg2[0,0])
(arg2[1] <-> arg2[1,0])
(arg3[] <-> arg3[0])
(arg3[] <-> arg3[1])
(arg3[0] <-> arg3[0,1])
(arg3[1] <-> arg3[1,1])
(p[] <-> p[1])
(p[1] <-> p[1,3])
(p[1,3] <-> p[])
(x[1,0] <-> xs[1,0])
(x[1,2] <-> p(1))
(xs[1,3] <-> arg2[])
(y[1,1] <-> ys[1,1])
(y[1,2] <-> p(2))
(ys[1,3] <-> arg3[])
1
-}
map_p2iiii = \p arg2 arg3 -> once $ do
  -- solution: x[1,0] xs[1,0] y[1,1] ys[1,1] ~arg2[] ~arg2[0] ~arg2[0,0] ~arg2[1] ~arg2[1,0] ~arg3[] ~arg3[0] ~arg3[0,1] ~arg3[1] ~arg3[1,1] ~p[] ~p[1] ~p[1,3] ~x[1,2] ~xs[1,3] ~y[1,2] ~ys[1,3] ~p(1) ~p(2)
  () <- (do
    guard $ arg2 == []
    guard $ arg3 == []
    pure ()
   ) <|> (do
    (x:xs) <- pure arg2
    (y:ys) <- pure arg3
    () <- map_p2iiii p xs ys
    () <- p x y
    pure ()
   )
  pure ()

map_p2ioio = \p arg2 -> do
  -- solution: arg3[] arg3[0] arg3[0,1] arg3[1] arg3[1,1] x[1,0] xs[1,0] y[1,2] ys[1,3] p(2) ~arg2[] ~arg2[0] ~arg2[0,0] ~arg2[1] ~arg2[1,0] ~p[] ~p[1] ~p[1,3] ~x[1,2] ~xs[1,3] ~y[1,1] ~ys[1,1] ~p(1)
  (arg3) <- (do
    guard $ arg2 == []
    arg3 <- pure []
    pure (arg3)
   ) <|> (do
    (x:xs) <- pure arg2
    (ys) <- map_p2ioio p xs
    (y) <- p x
    arg3 <- pure (y:ys)
    pure (arg3)
   )
  pure (arg3)

map_p2oioi = \p arg3 -> do
  -- solution: arg2[] arg2[0] arg2[0,0] arg2[1] arg2[1,0] x[1,2] xs[1,3] y[1,1] ys[1,1] p(1) ~arg3[] ~arg3[0] ~arg3[0,1] ~arg3[1] ~arg3[1,1] ~p[] ~p[1] ~p[1,3] ~x[1,0] ~xs[1,0] ~y[1,2] ~ys[1,3] ~p(2)
  (arg2) <- (do
    arg2 <- pure []
    guard $ arg3 == []
    pure (arg2)
   ) <|> (do
    (y:ys) <- pure arg3
    (xs) <- map_p2oioi p ys
    (x) <- p y
    arg2 <- pure (x:xs)
    pure (arg2)
   )
  pure (arg2)

map_p2oooo = \p -> do
  -- solution: arg2[] arg2[0] arg2[0,0] arg2[1] arg2[1,0] arg3[] arg3[0] arg3[0,1] arg3[1] arg3[1,1] x[1,2] xs[1,3] y[1,2] ys[1,3] p(1) p(2) ~p[] ~p[1] ~p[1,3] ~x[1,0] ~xs[1,0] ~y[1,1] ~ys[1,1]
  (arg2,arg3) <- (do
    arg2 <- pure []
    arg3 <- pure []
    pure (arg2,arg3)
   ) <|> (do
    (xs,ys) <- map_p2oooo p
    (x,y) <- p 
    arg2 <- pure (x:xs)
    arg3 <- pure (y:ys)
    pure (arg2,arg3)
   )
  pure (arg2,arg3)

{- succs/2
succs xs ys :- ((map p xs ys, (p x y :- (succ x y)))).
constraints:
~(p[0,0] & p[0,1])
(p[0,0] | p[0,1])
((x[0,1,0,0] & ~y[0,1,0,0]) | ((~x[0,1,0,0] & y[0,1,0,0]) | (~x[0,1,0,0] & ~y[0,1,0,0])))
((~p[0,0] & (p(1) & (p(2) & (xs[0,0] & ys[0,0])))) | ((~p[0,0] & (p(1) & (~p(2) & (xs[0,0] & ~ys[0,0])))) | ((~p[0,0] & (~p(1) & (p(2) & (~xs[0,0] & ys[0,0])))) | (~p[0,0] & (~p(1) & (~p(2) & (~xs[0,0] & ~ys[0,0])))))))
(x[0,1,0] <-> x[0,1,0,0])
(xs[] <-> xs[0])
(xs[0] <-> xs[0,0])
(y[0,1,0] <-> y[0,1,0,0])
(ys[] <-> ys[0])
(ys[0] <-> ys[0,0])
(p(1) <-> x[0,1,0])
(p(2) <-> y[0,1,0])
1
-}
succs_ii = \xs ys -> once $ do
  -- solution: p[0,1] ~p[0,0] ~x[0,1,0] ~x[0,1,0,0] ~xs[] ~xs[0] ~xs[0,0] ~y[0,1,0] ~y[0,1,0,0] ~ys[] ~ys[0] ~ys[0,0] ~p(1) ~p(2)
  () <- (do
    let p =
          \x y -> do
            () <- (do
              () <- succ_ii x y
              pure ()
             )
            pure ()
    () <- map_p2iiii p xs ys
    pure ()
   )
  pure ()

succs_io = \xs -> do
  -- solution: p[0,1] y[0,1,0] y[0,1,0,0] ys[] ys[0] ys[0,0] p(2) ~p[0,0] ~x[0,1,0] ~x[0,1,0,0] ~xs[] ~xs[0] ~xs[0,0] ~p(1)
  (ys) <- (do
    let p =
          \x -> do
            (y) <- (do
              (y) <- succ_io x
              pure (y)
             )
            pure (y)
    (ys) <- map_p2ioio p xs
    pure (ys)
   )
  pure (ys)

succs_oi = \ys -> do
  -- solution: p[0,1] x[0,1,0] x[0,1,0,0] xs[] xs[0] xs[0,0] p(1) ~p[0,0] ~y[0,1,0] ~y[0,1,0,0] ~ys[] ~ys[0] ~ys[0,0] ~p(2)
  (xs) <- (do
    let p =
          \y -> do
            (x) <- (do
              (x) <- succ_oi y
              pure (x)
             )
            pure (x)
    (xs) <- map_p2oioi p ys
    pure (xs)
   )
  pure (xs)

{- filter/3
filter p arg2 arg3 :- ((arg2 = [], arg3 = []); (arg2 = h0:t, h0 = h, if (p h) then (filter p t t', ts = h1:t', h1 = h) else (filter p t ts), arg3 = ts)).
constraints:
~h[1,2]
~h[1,2,0,0]
~h[1,2,1,2]
~p[]
~(arg2[1,0] & h0[1,0])
~(arg3[1,3] & ts[1,3])
~(h[1,1] & h[1,2])
~(h0[1,0] & h0[1,1])
~(h0[1,1] & h[1,1])
~(h1[1,2,1,1] & h1[1,2,1,2])
~(h1[1,2,1,2] & h[1,2,1,2])
~(t[1,0] & t[1,2])
~(t'[1,2,1,0] & t'[1,2,1,1])
~(ts[1,2] & ts[1,3])
~(ts[1,2,1,1] & h1[1,2,1,1])
(h[1,1] | h[1,2])
(h0[1,0] | h0[1,1])
(h1[1,2,1,1] | h1[1,2,1,2])
(t[1,0] | t[1,2])
(t'[1,2,1,0] | t'[1,2,1,1])
(ts[1,2] | ts[1,3])
(arg2[] <-> arg2[0])
(arg2[] <-> arg2[1])
(arg2[0] <-> arg2[0,0])
(arg2[1] <-> arg2[1,0])
(arg3[] <-> arg3[0])
(arg3[] <-> arg3[1])
(arg3[0] <-> arg3[0,1])
(arg3[1] <-> arg3[1,3])
(h[1,2,0,0] <-> p(1))
(h0[1,0] <-> t[1,0])
(h1[1,2,1,1] <-> t'[1,2,1,1])
(p[] <-> p[1])
(p[1] <-> p[1,2])
(p[1,2] <-> (p[1,2,1] | p[1,2,2]))
(p[1,2,1] <-> p[1,2,1,0])
(p[1,2,1] <-> p[1,2,2])
(p[1,2,1,0] <-> p[])
(p[1,2,2] <-> p[1,2,2,0])
(p[1,2,2,0] <-> p[])
(t[1,2] <-> (t[1,2,1] | t[1,2,2]))
(t[1,2,1] <-> t[1,2,1,0])
(t[1,2,1] <-> t[1,2,2])
(t[1,2,1,0] <-> arg2[])
(t[1,2,2] <-> t[1,2,2,0])
(t[1,2,2,0] <-> arg2[])
(t'[1,2,1,0] <-> arg3[])
(ts[1,2] <-> (ts[1,2,1] | ts[1,2,2]))
(ts[1,2,1] <-> ts[1,2,1,1])
(ts[1,2,1] <-> ts[1,2,2])
(ts[1,2,2] <-> ts[1,2,2,0])
(ts[1,2,2,0] <-> arg3[])
1
-}
filter_p1iii = \p arg2 arg3 -> once $ do
  -- solution: h[1,1] h0[1,0] h1[1,2,1,1] t[1,0] t'[1,2,1,1] ts[1,3] ~arg2[] ~arg2[0] ~arg2[0,0] ~arg2[1] ~arg2[1,0] ~arg3[] ~arg3[0] ~arg3[0,1] ~arg3[1] ~arg3[1,3] ~h[1,2] ~h[1,2,0,0] ~h[1,2,1,2] ~h0[1,1] ~h1[1,2,1,2] ~p[] ~p[1] ~p[1,2] ~p[1,2,1] ~p[1,2,1,0] ~p[1,2,2] ~p[1,2,2,0] ~t[1,2] ~t[1,2,1] ~t[1,2,1,0] ~t[1,2,2] ~t[1,2,2,0] ~t'[1,2,1,0] ~ts[1,2] ~ts[1,2,1] ~ts[1,2,1,1] ~ts[1,2,2] ~ts[1,2,2,0] ~p(1)
  () <- (do
    guard $ arg2 == []
    guard $ arg3 == []
    pure ()
   ) <|> (do
    ts <- pure arg3
    (h0:t) <- pure arg2
    h <- pure h0
    () <- ifte ((do
      () <- p h
      pure ()
     )) (\() -> (do
      (h1:t') <- pure ts
      guard $ h1 == h
      () <- filter_p1iii p t t'
      pure ()
     )) ((do
      () <- filter_p1iii p t ts
      pure ()
     ))
    pure ()
   )
  pure ()

filter_p1iio = \p arg2 -> do
  -- solution: arg3[] arg3[0] arg3[0,1] arg3[1] arg3[1,3] h[1,1] h0[1,0] h1[1,2,1,2] t[1,0] t'[1,2,1,0] ts[1,2] ts[1,2,1] ts[1,2,1,1] ts[1,2,2] ts[1,2,2,0] ~arg2[] ~arg2[0] ~arg2[0,0] ~arg2[1] ~arg2[1,0] ~h[1,2] ~h[1,2,0,0] ~h[1,2,1,2] ~h0[1,1] ~h1[1,2,1,1] ~p[] ~p[1] ~p[1,2] ~p[1,2,1] ~p[1,2,1,0] ~p[1,2,2] ~p[1,2,2,0] ~t[1,2] ~t[1,2,1] ~t[1,2,1,0] ~t[1,2,2] ~t[1,2,2,0] ~t'[1,2,1,1] ~ts[1,3] ~p(1)
  (arg3) <- (do
    guard $ arg2 == []
    arg3 <- pure []
    pure (arg3)
   ) <|> (do
    (h0:t) <- pure arg2
    h <- pure h0
    (ts) <- ifte ((do
      () <- p h
      pure ()
     )) (\() -> (do
      h1 <- pure h
      (t') <- filter_p1iio p t
      ts <- pure (h1:t')
      pure (ts)
     )) ((do
      (ts) <- filter_p1iio p t
      pure (ts)
     ))
    arg3 <- pure ts
    pure (arg3)
   )
  pure (arg3)

{- evens/2
evens xs ys :- ((filter p xs ys, (p x :- (even x)))).
constraints:
~x[0,1,0,0]
~(p[0,0] & p[0,1])
(p[0,0] | p[0,1])
((~p[0,0] & (~p(1) & (~xs[0,0] & ys[0,0]))) | (~p[0,0] & (~p(1) & (~xs[0,0] & ~ys[0,0]))))
(x[0,1,0] <-> x[0,1,0,0])
(xs[] <-> xs[0])
(xs[0] <-> xs[0,0])
(ys[] <-> ys[0])
(ys[0] <-> ys[0,0])
(p(1) <-> x[0,1,0])
1
-}
evens_ii = \xs ys -> once $ do
  -- solution: p[0,1] ~p[0,0] ~x[0,1,0] ~x[0,1,0,0] ~xs[] ~xs[0] ~xs[0,0] ~ys[] ~ys[0] ~ys[0,0] ~p(1)
  () <- (do
    let p =
          \x -> do
            () <- (do
              () <- even_i x
              pure ()
             )
            pure ()
    () <- filter_p1iii p xs ys
    pure ()
   )
  pure ()

evens_io = \xs -> do
  -- solution: p[0,1] ys[] ys[0] ys[0,0] ~p[0,0] ~x[0,1,0] ~x[0,1,0,0] ~xs[] ~xs[0] ~xs[0,0] ~p(1)
  (ys) <- (do
    let p =
          \x -> do
            () <- (do
              () <- even_i x
              pure ()
             )
            pure ()
    (ys) <- filter_p1iio p xs
    pure (ys)
   )
  pure (ys)

{- foldl/4
foldl p arg2 a arg4 :- ((arg2 = [], arg4 = a); (arg2 = h:t, p h a a', foldl p t a' a'', arg4 = a'')).
constraints:
~p[]
~(a'[1,1] & a'[1,2])
~(a''[1,2] & a''[1,3])
~(arg2[1,0] & h[1,0])
~(arg4[0,1] & a[0,1])
~(arg4[1,3] & a''[1,3])
~(h[1,0] & h[1,1])
~(t[1,0] & t[1,2])
(a'[1,1] | a'[1,2])
(a''[1,2] | a''[1,3])
(h[1,0] | h[1,1])
(t[1,0] | t[1,2])
(a[] <-> a[0])
(a[] <-> a[1])
(a[0] <-> a[0,1])
(a[1] <-> a[1,1])
(a[1,1] <-> p(2))
(a'[1,1] <-> p(3))
(a'[1,2] <-> a[])
(a''[1,2] <-> arg4[])
(arg2[] <-> arg2[0])
(arg2[] <-> arg2[1])
(arg2[0] <-> arg2[0,0])
(arg2[1] <-> arg2[1,0])
(arg4[] <-> arg4[0])
(arg4[] <-> arg4[1])
(arg4[0] <-> arg4[0,1])
(arg4[1] <-> arg4[1,3])
(h[1,0] <-> t[1,0])
(h[1,1] <-> p(1))
(p[] <-> p[1])
(p[1] <-> p[1,2])
(p[1,2] <-> p[])
(t[1,2] <-> arg2[])
1
-}
foldl_p3iioiii = \p arg2 a arg4 -> once $ do
  -- solution: a'[1,1] a''[1,3] h[1,0] t[1,0] p(3) ~a[] ~a[0] ~a[0,1] ~a[1] ~a[1,1] ~a'[1,2] ~a''[1,2] ~arg2[] ~arg2[0] ~arg2[0,0] ~arg2[1] ~arg2[1,0] ~arg4[] ~arg4[0] ~arg4[0,1] ~arg4[1] ~arg4[1,3] ~h[1,1] ~p[] ~p[1] ~p[1,2] ~t[1,2] ~p(1) ~p(2)
  () <- (do
    guard $ arg4 == a
    guard $ arg2 == []
    pure ()
   ) <|> (do
    a'' <- pure arg4
    (h:t) <- pure arg2
    (a') <- p h a
    () <- foldl_p3iioiii p t a' a''
    pure ()
   )
  pure ()

foldl_p3iioiio = \p arg2 a -> do
  -- solution: a'[1,1] a''[1,2] arg4[] arg4[0] arg4[0,1] arg4[1] arg4[1,3] h[1,0] t[1,0] p(3) ~a[] ~a[0] ~a[0,1] ~a[1] ~a[1,1] ~a'[1,2] ~a''[1,3] ~arg2[] ~arg2[0] ~arg2[0,0] ~arg2[1] ~arg2[1,0] ~h[1,1] ~p[] ~p[1] ~p[1,2] ~t[1,2] ~p(1) ~p(2)
  (arg4) <- (do
    arg4 <- pure a
    guard $ arg2 == []
    pure (arg4)
   ) <|> (do
    (h:t) <- pure arg2
    (a') <- p h a
    (a'') <- foldl_p3iioiio p t a'
    arg4 <- pure a''
    pure (arg4)
   )
  pure (arg4)

foldl_p3ioiioi = \p arg2 arg4 -> do
  -- solution: a[] a[0] a[0,1] a[1] a[1,1] a'[1,2] a''[1,3] h[1,0] t[1,0] p(2) ~a'[1,1] ~a''[1,2] ~arg2[] ~arg2[0] ~arg2[0,0] ~arg2[1] ~arg2[1,0] ~arg4[] ~arg4[0] ~arg4[0,1] ~arg4[1] ~arg4[1,3] ~h[1,1] ~p[] ~p[1] ~p[1,2] ~t[1,2] ~p(1) ~p(3)
  (a) <- (do
    a <- pure arg4
    guard $ arg2 == []
    pure (a)
   ) <|> (do
    a'' <- pure arg4
    (h:t) <- pure arg2
    (a') <- foldl_p3ioiioi p t a''
    (a) <- p h a'
    pure (a)
   )
  pure (a)

foldl_p3oiooii = \p a arg4 -> do
  -- solution: a'[1,1] a''[1,3] arg2[] arg2[0] arg2[0,0] arg2[1] arg2[1,0] h[1,1] t[1,2] p(1) p(3) ~a[] ~a[0] ~a[0,1] ~a[1] ~a[1,1] ~a'[1,2] ~a''[1,2] ~arg4[] ~arg4[0] ~arg4[0,1] ~arg4[1] ~arg4[1,3] ~h[1,0] ~p[] ~p[1] ~p[1,2] ~t[1,0] ~p(2)
  (arg2) <- (do
    guard $ arg4 == a
    arg2 <- pure []
    pure (arg2)
   ) <|> (do
    a'' <- pure arg4
    (h,a') <- p a
    (t) <- foldl_p3oiooii p a' a''
    arg2 <- pure (h:t)
    pure (arg2)
   )
  pure (arg2)

foldl_p3oiooio = \p a -> do
  -- solution: a'[1,1] a''[1,2] arg2[] arg2[0] arg2[0,0] arg2[1] arg2[1,0] arg4[] arg4[0] arg4[0,1] arg4[1] arg4[1,3] h[1,1] t[1,2] p(1) p(3) ~a[] ~a[0] ~a[0,1] ~a[1] ~a[1,1] ~a'[1,2] ~a''[1,3] ~h[1,0] ~p[] ~p[1] ~p[1,2] ~t[1,0] ~p(2)
  (arg2,arg4) <- (do
    arg4 <- pure a
    arg2 <- pure []
    pure (arg2,arg4)
   ) <|> (do
    (h,a') <- p a
    (t,a'') <- foldl_p3oiooio p a'
    arg4 <- pure a''
    arg2 <- pure (h:t)
    pure (arg2,arg4)
   )
  pure (arg2,arg4)

foldl_p3ooiooi = \p arg4 -> do
  -- solution: a[] a[0] a[0,1] a[1] a[1,1] a'[1,2] a''[1,3] arg2[] arg2[0] arg2[0,0] arg2[1] arg2[1,0] h[1,1] t[1,2] p(1) p(2) ~a'[1,1] ~a''[1,2] ~arg4[] ~arg4[0] ~arg4[0,1] ~arg4[1] ~arg4[1,3] ~h[1,0] ~p[] ~p[1] ~p[1,2] ~t[1,0] ~p(3)
  (a,arg2) <- (do
    a <- pure arg4
    arg2 <- pure []
    pure (a,arg2)
   ) <|> (do
    a'' <- pure arg4
    (t,a') <- foldl_p3ooiooi p a''
    (h,a) <- p a'
    arg2 <- pure (h:t)
    pure (a,arg2)
   )
  pure (arg2,a)

{- sum/3
sum xs z r :- ((foldl p xs z r, (p x a a' :- (plus x a a')))).
constraints:
~(p[0,0] & p[0,1])
(p[0,0] | p[0,1])
((x[0,1,0,0] & (~a[0,1,0,0] & ~a'[0,1,0,0])) | ((~x[0,1,0,0] & (a[0,1,0,0] & ~a'[0,1,0,0])) | (~x[0,1,0,0] & (~a[0,1,0,0] & a'[0,1,0,0]))))
((~p[0,0] & (p(1) & (p(2) & (~p(3) & (xs[0,0] & (z[0,0] & ~r[0,0])))))) | ((~p[0,0] & (p(1) & (~p(2) & (p(3) & (xs[0,0] & (~z[0,0] & r[0,0])))))) | ((~p[0,0] & (p(1) & (~p(2) & (p(3) & (xs[0,0] & (~z[0,0] & ~r[0,0])))))) | ((~p[0,0] & (~p(1) & (p(2) & (~p(3) & (~xs[0,0] & (z[0,0] & ~r[0,0])))))) | ((~p[0,0] & (~p(1) & (~p(2) & (p(3) & (~xs[0,0] & (~z[0,0] & r[0,0])))))) | (~p[0,0] & (~p(1) & (~p(2) & (p(3) & (~xs[0,0] & (~z[0,0] & ~r[0,0])))))))))))
(a[0,1,0] <-> a[0,1,0,0])
(a'[0,1,0] <-> a'[0,1,0,0])
(r[] <-> r[0])
(r[0] <-> r[0,0])
(x[0,1,0] <-> x[0,1,0,0])
(xs[] <-> xs[0])
(xs[0] <-> xs[0,0])
(z[] <-> z[0])
(z[0] <-> z[0,0])
(p(1) <-> x[0,1,0])
(p(2) <-> a[0,1,0])
(p(3) <-> a'[0,1,0])
1
-}
sum_iii = \xs z r -> once $ do
  -- solution: a'[0,1,0] a'[0,1,0,0] p[0,1] p(3) ~a[0,1,0] ~a[0,1,0,0] ~p[0,0] ~r[] ~r[0] ~r[0,0] ~x[0,1,0] ~x[0,1,0,0] ~xs[] ~xs[0] ~xs[0,0] ~z[] ~z[0] ~z[0,0] ~p(1) ~p(2)
  () <- (do
    let p =
          \x a -> do
            (a') <- (do
              (a') <- plus_iio x a
              pure (a')
             )
            pure (a')
    () <- foldl_p3iioiii p xs z r
    pure ()
   )
  pure ()

sum_iio = \xs z -> do
  -- solution: a'[0,1,0] a'[0,1,0,0] p[0,1] r[] r[0] r[0,0] p(3) ~a[0,1,0] ~a[0,1,0,0] ~p[0,0] ~x[0,1,0] ~x[0,1,0,0] ~xs[] ~xs[0] ~xs[0,0] ~z[] ~z[0] ~z[0,0] ~p(1) ~p(2)
  (r) <- (do
    let p =
          \x a -> do
            (a') <- (do
              (a') <- plus_iio x a
              pure (a')
             )
            pure (a')
    (r) <- foldl_p3iioiio p xs z
    pure (r)
   )
  pure (r)

sum_ioi = \xs r -> do
  -- solution: a[0,1,0] a[0,1,0,0] p[0,1] z[] z[0] z[0,0] p(2) ~a'[0,1,0] ~a'[0,1,0,0] ~p[0,0] ~r[] ~r[0] ~r[0,0] ~x[0,1,0] ~x[0,1,0,0] ~xs[] ~xs[0] ~xs[0,0] ~p(1) ~p(3)
  (z) <- (do
    let p =
          \x a' -> do
            (a) <- (do
              (a) <- plus_ioi x a'
              pure (a)
             )
            pure (a)
    (z) <- foldl_p3ioiioi p xs r
    pure (z)
   )
  pure (z)

{- split/3
split xs z r :- ((foldl p xs z r, (p x a a' :- (a = x:a')))).
constraints:
~(a[0,1,0,0] & x[0,1,0,0])
~(p[0,0] & p[0,1])
(p[0,0] | p[0,1])
((~p[0,0] & (p(1) & (p(2) & (~p(3) & (xs[0,0] & (z[0,0] & ~r[0,0])))))) | ((~p[0,0] & (p(1) & (~p(2) & (p(3) & (xs[0,0] & (~z[0,0] & r[0,0])))))) | ((~p[0,0] & (p(1) & (~p(2) & (p(3) & (xs[0,0] & (~z[0,0] & ~r[0,0])))))) | ((~p[0,0] & (~p(1) & (p(2) & (~p(3) & (~xs[0,0] & (z[0,0] & ~r[0,0])))))) | ((~p[0,0] & (~p(1) & (~p(2) & (p(3) & (~xs[0,0] & (~z[0,0] & r[0,0])))))) | (~p[0,0] & (~p(1) & (~p(2) & (p(3) & (~xs[0,0] & (~z[0,0] & ~r[0,0])))))))))))
(a[0,1,0] <-> a[0,1,0,0])
(a'[0,1,0] <-> a'[0,1,0,0])
(r[] <-> r[0])
(r[0] <-> r[0,0])
(x[0,1,0] <-> x[0,1,0,0])
(x[0,1,0,0] <-> a'[0,1,0,0])
(xs[] <-> xs[0])
(xs[0] <-> xs[0,0])
(z[] <-> z[0])
(z[0] <-> z[0,0])
(p(1) <-> x[0,1,0])
(p(2) <-> a[0,1,0])
(p(3) <-> a'[0,1,0])
1
-}
split_ioi = \xs r -> do
  -- solution: a[0,1,0] a[0,1,0,0] p[0,1] z[] z[0] z[0,0] p(2) ~a'[0,1,0] ~a'[0,1,0,0] ~p[0,0] ~r[] ~r[0] ~r[0,0] ~x[0,1,0] ~x[0,1,0,0] ~xs[] ~xs[0] ~xs[0,0] ~p(1) ~p(3)
  (z) <- (do
    let p =
          \x a' -> do
            (a) <- (do
              a <- pure (x:a')
              pure (a)
             )
            pure (a)
    (z) <- foldl_p3ioiioi p xs r
    pure (z)
   )
  pure (z)

split_oii = \z r -> do
  -- solution: a'[0,1,0] a'[0,1,0,0] p[0,1] x[0,1,0] x[0,1,0,0] xs[] xs[0] xs[0,0] p(1) p(3) ~a[0,1,0] ~a[0,1,0,0] ~p[0,0] ~r[] ~r[0] ~r[0,0] ~z[] ~z[0] ~z[0,0] ~p(2)
  (xs) <- (do
    let p =
          \a -> do
            (a',x) <- (do
              (x:a') <- pure a
              pure (a',x)
             )
            pure (x,a')
    (xs) <- foldl_p3oiooii p z r
    pure (xs)
   )
  pure (xs)

split_oio = \z -> do
  -- solution: a'[0,1,0] a'[0,1,0,0] p[0,1] r[] r[0] r[0,0] x[0,1,0] x[0,1,0,0] xs[] xs[0] xs[0,0] p(1) p(3) ~a[0,1,0] ~a[0,1,0,0] ~p[0,0] ~z[] ~z[0] ~z[0,0] ~p(2)
  (r,xs) <- (do
    let p =
          \a -> do
            (a',x) <- (do
              (x:a') <- pure a
              pure (a',x)
             )
            pure (x,a')
    (xs,r) <- foldl_p3oiooio p z
    pure (r,xs)
   )
  pure (xs,r)

{- splitr/3
splitr xs z r :- ((foldl p xs z r, (p x a a' :- (a' = x:a)))).
constraints:
~(a'[0,1,0,0] & x[0,1,0,0])
~(p[0,0] & p[0,1])
(p[0,0] | p[0,1])
((~p[0,0] & (p(1) & (p(2) & (~p(3) & (xs[0,0] & (z[0,0] & ~r[0,0])))))) | ((~p[0,0] & (p(1) & (~p(2) & (p(3) & (xs[0,0] & (~z[0,0] & r[0,0])))))) | ((~p[0,0] & (p(1) & (~p(2) & (p(3) & (xs[0,0] & (~z[0,0] & ~r[0,0])))))) | ((~p[0,0] & (~p(1) & (p(2) & (~p(3) & (~xs[0,0] & (z[0,0] & ~r[0,0])))))) | ((~p[0,0] & (~p(1) & (~p(2) & (p(3) & (~xs[0,0] & (~z[0,0] & r[0,0])))))) | (~p[0,0] & (~p(1) & (~p(2) & (p(3) & (~xs[0,0] & (~z[0,0] & ~r[0,0])))))))))))
(a[0,1,0] <-> a[0,1,0,0])
(a'[0,1,0] <-> a'[0,1,0,0])
(r[] <-> r[0])
(r[0] <-> r[0,0])
(x[0,1,0] <-> x[0,1,0,0])
(x[0,1,0,0] <-> a[0,1,0,0])
(xs[] <-> xs[0])
(xs[0] <-> xs[0,0])
(z[] <-> z[0])
(z[0] <-> z[0,0])
(p(1) <-> x[0,1,0])
(p(2) <-> a[0,1,0])
(p(3) <-> a'[0,1,0])
1
-}
splitr_iii = \xs z r -> once $ do
  -- solution: a'[0,1,0] a'[0,1,0,0] p[0,1] p(3) ~a[0,1,0] ~a[0,1,0,0] ~p[0,0] ~r[] ~r[0] ~r[0,0] ~x[0,1,0] ~x[0,1,0,0] ~xs[] ~xs[0] ~xs[0,0] ~z[] ~z[0] ~z[0,0] ~p(1) ~p(2)
  () <- (do
    let p =
          \x a -> do
            (a') <- (do
              a' <- pure (x:a)
              pure (a')
             )
            pure (a')
    () <- foldl_p3iioiii p xs z r
    pure ()
   )
  pure ()

splitr_iio = \xs z -> do
  -- solution: a'[0,1,0] a'[0,1,0,0] p[0,1] r[] r[0] r[0,0] p(3) ~a[0,1,0] ~a[0,1,0,0] ~p[0,0] ~x[0,1,0] ~x[0,1,0,0] ~xs[] ~xs[0] ~xs[0,0] ~z[] ~z[0] ~z[0,0] ~p(1) ~p(2)
  (r) <- (do
    let p =
          \x a -> do
            (a') <- (do
              a' <- pure (x:a)
              pure (a')
             )
            pure (a')
    (r) <- foldl_p3iioiio p xs z
    pure (r)
   )
  pure (r)

splitr_ooi = \r -> do
  -- solution: a[0,1,0] a[0,1,0,0] p[0,1] x[0,1,0] x[0,1,0,0] xs[] xs[0] xs[0,0] z[] z[0] z[0,0] p(1) p(2) ~a'[0,1,0] ~a'[0,1,0,0] ~p[0,0] ~r[] ~r[0] ~r[0,0] ~p(3)
  (xs,z) <- (do
    let p =
          \a' -> do
            (a,x) <- (do
              (x:a) <- pure a'
              pure (a,x)
             )
            pure (x,a)
    (xs,z) <- foldl_p3ooiooi p r
    pure (xs,z)
   )
  pure (xs,z)
