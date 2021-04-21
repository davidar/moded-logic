{-# LANGUAGE NoMonomorphismRestriction #-}
module Append where

import Control.Applicative
import Control.Monad.Logic
import Control.Monad.Logic.Moded.Prelude
import Data.List
import Data.MemoTrie

{- append/3
append arg1 b arg3 :- ((arg1 = [], arg3 = b); (arg1 = h0:t, h0 = h, arg3 = h1:tb, h1 = h, append t b tb)).
constraints:
~(arg1[1,0] & h0[1,0])
~(arg3[0,1] & b[0,1])
~(arg3[1,2] & h1[1,2])
~(h[1,1] & h[1,3])
~(h0[1,0] & h0[1,1])
~(h0[1,1] & h[1,1])
~(h1[1,2] & h1[1,3])
~(h1[1,3] & h[1,3])
~(t[1,0] & t[1,4])
~(tb[1,2] & tb[1,4])
(h[1,1] | h[1,3])
(h0[1,0] | h0[1,1])
(h1[1,2] | h1[1,3])
(t[1,0] | t[1,4])
(tb[1,2] | tb[1,4])
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg1[0] <-> arg1[0,0])
(arg1[1] <-> arg1[1,0])
(arg3[] <-> arg3[0])
(arg3[] <-> arg3[1])
(arg3[0] <-> arg3[0,1])
(arg3[1] <-> arg3[1,2])
(b[] <-> b[0])
(b[] <-> b[1])
(b[0] <-> b[0,1])
(b[1] <-> b[1,4])
(b[1,4] <-> b[])
(h0[1,0] <-> t[1,0])
(h1[1,2] <-> tb[1,2])
(t[1,4] <-> arg1[])
(tb[1,4] <-> arg3[])
1
-}
append_iii = \arg1 b arg3 -> once $ do
  -- solution: h[1,1] h0[1,0] h1[1,2] t[1,0] tb[1,2] ~arg1[] ~arg1[0] ~arg1[0,0] ~arg1[1] ~arg1[1,0] ~arg3[] ~arg3[0] ~arg3[0,1] ~arg3[1] ~arg3[1,2] ~b[] ~b[0] ~b[0,1] ~b[1] ~b[1,4] ~h[1,3] ~h0[1,1] ~h1[1,3] ~t[1,4] ~tb[1,4]
  -- cost: 1
  () <- (do
    guard $ arg3 == b
    guard $ arg1 == []
    pure ()
   ) <|> (do
    (h0:t) <- pure arg1
    h <- pure h0
    (h1:tb) <- pure arg3
    guard $ h1 == h
    () <- append_iii t b tb
    pure ()
   )
  pure ()

append_iio = \arg1 b -> do
  -- solution: arg3[] arg3[0] arg3[0,1] arg3[1] arg3[1,2] h[1,1] h0[1,0] h1[1,3] t[1,0] tb[1,4] ~arg1[] ~arg1[0] ~arg1[0,0] ~arg1[1] ~arg1[1,0] ~b[] ~b[0] ~b[0,1] ~b[1] ~b[1,4] ~h[1,3] ~h0[1,1] ~h1[1,2] ~t[1,4] ~tb[1,2]
  -- cost: 2
  (arg3) <- (do
    arg3 <- pure b
    guard $ arg1 == []
    pure (arg3)
   ) <|> (do
    (h0:t) <- pure arg1
    h <- pure h0
    h1 <- pure h
    (tb) <- append_iio t b
    arg3 <- pure (h1:tb)
    pure (arg3)
   )
  pure (arg3)

append_ioi = \arg1 arg3 -> do
  -- solution: b[] b[0] b[0,1] b[1] b[1,4] h[1,1] h0[1,0] h1[1,2] t[1,0] tb[1,2] ~arg1[] ~arg1[0] ~arg1[0,0] ~arg1[1] ~arg1[1,0] ~arg3[] ~arg3[0] ~arg3[0,1] ~arg3[1] ~arg3[1,2] ~h[1,3] ~h0[1,1] ~h1[1,3] ~t[1,4] ~tb[1,4]
  -- cost: 2
  (b) <- (do
    b <- pure arg3
    guard $ arg1 == []
    pure (b)
   ) <|> (do
    (h0:t) <- pure arg1
    h <- pure h0
    (h1:tb) <- pure arg3
    guard $ h1 == h
    (b) <- append_ioi t tb
    pure (b)
   )
  pure (b)

append_oii = \b arg3 -> do
  -- solution: arg1[] arg1[0] arg1[0,0] arg1[1] arg1[1,0] h[1,3] h0[1,1] h1[1,2] t[1,4] tb[1,2] ~arg3[] ~arg3[0] ~arg3[0,1] ~arg3[1] ~arg3[1,2] ~b[] ~b[0] ~b[0,1] ~b[1] ~b[1,4] ~h[1,1] ~h0[1,0] ~h1[1,3] ~t[1,0] ~tb[1,4]
  -- cost: 2
  (arg1) <- (do
    guard $ arg3 == b
    arg1 <- pure []
    pure (arg1)
   ) <|> (do
    (h1:tb) <- pure arg3
    h <- pure h1
    h0 <- pure h
    (t) <- append_oii b tb
    arg1 <- pure (h0:t)
    pure (arg1)
   )
  pure (arg1)

append_ooi = \arg3 -> do
  -- solution: arg1[] arg1[0] arg1[0,0] arg1[1] arg1[1,0] b[] b[0] b[0,1] b[1] b[1,4] h[1,3] h0[1,1] h1[1,2] t[1,4] tb[1,2] ~arg3[] ~arg3[0] ~arg3[0,1] ~arg3[1] ~arg3[1,2] ~h[1,1] ~h0[1,0] ~h1[1,3] ~t[1,0] ~tb[1,4]
  -- cost: 3
  (arg1,b) <- (do
    b <- pure arg3
    arg1 <- pure []
    pure (arg1,b)
   ) <|> (do
    (h1:tb) <- pure arg3
    h <- pure h1
    h0 <- pure h
    (t,b) <- append_ooi tb
    arg1 <- pure (h0:t)
    pure (arg1,b)
   )
  pure (arg1,b)

{- append3/4
append3 a b c abc :- ((append a b ab, append ab c abc)).
constraints:
~(ab[0,0] & ab[0,1])
(ab[0,0] | ab[0,1])
((a[0,0] & (b[0,0] & ~ab[0,0])) | ((a[0,0] & (~b[0,0] & ~ab[0,0])) | ((~a[0,0] & (b[0,0] & ~ab[0,0])) | ((~a[0,0] & (~b[0,0] & ab[0,0])) | (~a[0,0] & (~b[0,0] & ~ab[0,0]))))))
((ab[0,1] & (c[0,1] & ~abc[0,1])) | ((ab[0,1] & (~c[0,1] & ~abc[0,1])) | ((~ab[0,1] & (c[0,1] & ~abc[0,1])) | ((~ab[0,1] & (~c[0,1] & abc[0,1])) | (~ab[0,1] & (~c[0,1] & ~abc[0,1]))))))
(a[] <-> a[0])
(a[0] <-> a[0,0])
(abc[] <-> abc[0])
(abc[0] <-> abc[0,1])
(b[] <-> b[0])
(b[0] <-> b[0,0])
(c[] <-> c[0])
(c[0] <-> c[0,1])
1
-}
append3_iiii = \a b c abc -> once $ do
  -- solution: ab[0,0] ~a[] ~a[0] ~a[0,0] ~ab[0,1] ~abc[] ~abc[0] ~abc[0,1] ~b[] ~b[0] ~b[0,0] ~c[] ~c[0] ~c[0,1]
  -- cost: 3
  () <- (do
    (ab) <- append_iio a b
    () <- append_iii ab c abc
    pure ()
   )
  pure ()

append3_iiio = \a b c -> do
  -- solution: ab[0,0] abc[] abc[0] abc[0,1] ~a[] ~a[0] ~a[0,0] ~ab[0,1] ~b[] ~b[0] ~b[0,0] ~c[] ~c[0] ~c[0,1]
  -- cost: 4
  (abc) <- (do
    (ab) <- append_iio a b
    (abc) <- append_iio ab c
    pure (abc)
   )
  pure (abc)

append3_iioi = \a b abc -> do
  -- solution: ab[0,0] c[] c[0] c[0,1] ~a[] ~a[0] ~a[0,0] ~ab[0,1] ~abc[] ~abc[0] ~abc[0,1] ~b[] ~b[0] ~b[0,0]
  -- cost: 4
  (c) <- (do
    (ab) <- append_iio a b
    (c) <- append_ioi ab abc
    pure (c)
   )
  pure (c)

append3_ioii = \a c abc -> do
  -- solution: ab[0,1] b[] b[0] b[0,0] ~a[] ~a[0] ~a[0,0] ~ab[0,0] ~abc[] ~abc[0] ~abc[0,1] ~c[] ~c[0] ~c[0,1]
  -- cost: 4
  (b) <- (do
    (ab) <- append_oii c abc
    (b) <- append_ioi a ab
    pure (b)
   )
  pure (b)

append3_iooi = \a abc -> do
  -- solution: ab[0,1] b[] b[0] b[0,0] c[] c[0] c[0,1] ~a[] ~a[0] ~a[0,0] ~ab[0,0] ~abc[] ~abc[0] ~abc[0,1]
  -- cost: 5
  (b,c) <- (do
    (ab,c) <- append_ooi abc
    (b) <- append_ioi a ab
    pure (b,c)
   )
  pure (b,c)

append3_oiii = \b c abc -> do
  -- solution: a[] a[0] a[0,0] ab[0,1] ~ab[0,0] ~abc[] ~abc[0] ~abc[0,1] ~b[] ~b[0] ~b[0,0] ~c[] ~c[0] ~c[0,1]
  -- cost: 4
  (a) <- (do
    (ab) <- append_oii c abc
    (a) <- append_oii b ab
    pure (a)
   )
  pure (a)

append3_oioi = \b abc -> do
  -- solution: a[] a[0] a[0,0] ab[0,1] c[] c[0] c[0,1] ~ab[0,0] ~abc[] ~abc[0] ~abc[0,1] ~b[] ~b[0] ~b[0,0]
  -- cost: 5
  (a,c) <- (do
    (ab,c) <- append_ooi abc
    (a) <- append_oii b ab
    pure (a,c)
   )
  pure (a,c)

append3_ooii = \c abc -> do
  -- solution: a[] a[0] a[0,0] ab[0,1] b[] b[0] b[0,0] ~ab[0,0] ~abc[] ~abc[0] ~abc[0,1] ~c[] ~c[0] ~c[0,1]
  -- cost: 5
  (a,b) <- (do
    (ab) <- append_oii c abc
    (a,b) <- append_ooi ab
    pure (a,b)
   )
  pure (a,b)

append3_oooi = \abc -> do
  -- solution: a[] a[0] a[0,0] ab[0,1] b[] b[0] b[0,0] c[] c[0] c[0,1] ~ab[0,0] ~abc[] ~abc[0] ~abc[0,1]
  -- cost: 6
  (a,b,c) <- (do
    (ab,c) <- append_ooi abc
    (a,b) <- append_ooi ab
    pure (a,b,c)
   )
  pure (a,b,c)

{- reverse/2
reverse arg1 arg2 :- ((arg1 = [], arg2 = []); (arg1 = h0:t, h0 = h, reverse t r, append r data1 l, data0 = [], data1 = h1:data0, h1 = h, arg2 = l)).
constraints:
~(arg1[1,0] & h0[1,0])
~(arg2[1,7] & l[1,7])
~(data0[1,4] & data0[1,5])
~(data1[1,3] & data1[1,5])
~(data1[1,5] & h1[1,5])
~(h[1,1] & h[1,6])
~(h0[1,0] & h0[1,1])
~(h0[1,1] & h[1,1])
~(h1[1,5] & h1[1,6])
~(h1[1,6] & h[1,6])
~(l[1,3] & l[1,7])
~(r[1,2] & r[1,3])
~(t[1,0] & t[1,2])
(data0[1,4] | data0[1,5])
(data1[1,3] | data1[1,5])
(h[1,1] | h[1,6])
(h0[1,0] | h0[1,1])
(h1[1,5] | h1[1,6])
(l[1,3] | l[1,7])
(r[1,2] | r[1,3])
(t[1,0] | t[1,2])
((r[1,3] & (data1[1,3] & ~l[1,3])) | ((r[1,3] & (~data1[1,3] & ~l[1,3])) | ((~r[1,3] & (data1[1,3] & ~l[1,3])) | ((~r[1,3] & (~data1[1,3] & l[1,3])) | (~r[1,3] & (~data1[1,3] & ~l[1,3]))))))
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg1[0] <-> arg1[0,0])
(arg1[1] <-> arg1[1,0])
(arg2[] <-> arg2[0])
(arg2[] <-> arg2[1])
(arg2[0] <-> arg2[0,1])
(arg2[1] <-> arg2[1,7])
(h0[1,0] <-> t[1,0])
(h1[1,5] <-> data0[1,5])
(r[1,2] <-> arg2[])
(t[1,2] <-> arg1[])
1
-}
reverse_ii = \arg1 arg2 -> once $ do
  -- solution: data0[1,4] data1[1,5] h[1,1] h0[1,0] h1[1,6] l[1,7] r[1,3] t[1,0] ~arg1[] ~arg1[0] ~arg1[0,0] ~arg1[1] ~arg1[1,0] ~arg2[] ~arg2[0] ~arg2[0,1] ~arg2[1] ~arg2[1,7] ~data0[1,5] ~data1[1,3] ~h[1,6] ~h0[1,1] ~h1[1,5] ~l[1,3] ~r[1,2] ~t[1,2]
  -- cost: 3
  () <- (do
    guard $ arg1 == []
    guard $ arg2 == []
    pure ()
   ) <|> (do
    l <- pure arg2
    (h0:t) <- pure arg1
    h <- pure h0
    h1 <- pure h
    data0 <- pure []
    data1 <- pure (h1:data0)
    (r) <- append_oii data1 l
    () <- reverse_ii t r
    pure ()
   )
  pure ()

reverse_io = \arg1 -> do
  -- solution: arg2[] arg2[0] arg2[0,1] arg2[1] arg2[1,7] data0[1,4] data1[1,5] h[1,1] h0[1,0] h1[1,6] l[1,3] r[1,2] t[1,0] ~arg1[] ~arg1[0] ~arg1[0,0] ~arg1[1] ~arg1[1,0] ~data0[1,5] ~data1[1,3] ~h[1,6] ~h0[1,1] ~h1[1,5] ~l[1,7] ~r[1,3] ~t[1,2]
  -- cost: 4
  (arg2) <- (do
    guard $ arg1 == []
    arg2 <- pure []
    pure (arg2)
   ) <|> (do
    (h0:t) <- pure arg1
    h <- pure h0
    h1 <- pure h
    data0 <- pure []
    data1 <- pure (h1:data0)
    (r) <- reverse_io t
    (l) <- append_iio r data1
    arg2 <- pure l
    pure (arg2)
   )
  pure (arg2)

reverse_oi = \arg2 -> do
  -- solution: arg1[] arg1[0] arg1[0,0] arg1[1] arg1[1,0] data0[1,5] data1[1,3] h[1,6] h0[1,1] h1[1,5] l[1,7] r[1,3] t[1,2] ~arg2[] ~arg2[0] ~arg2[0,1] ~arg2[1] ~arg2[1,7] ~data0[1,4] ~data1[1,5] ~h[1,1] ~h0[1,0] ~h1[1,6] ~l[1,3] ~r[1,2] ~t[1,0]
  -- cost: 5
  (arg1) <- (do
    arg1 <- pure []
    guard $ arg2 == []
    pure (arg1)
   ) <|> (do
    l <- pure arg2
    (r,data1) <- append_ooi l
    (h1:data0) <- pure data1
    h <- pure h1
    h0 <- pure h
    guard $ data0 == []
    (t) <- reverse_oi r
    arg1 <- pure (h0:t)
    pure (arg1)
   )
  pure (arg1)

{- palindrome/1
palindrome a :- ((reverse a0 a1, a0 = a, a1 = a)).
constraints:
~(a[0,1] & a[0,2])
~(a0[0,0] & a0[0,1])
~(a0[0,1] & a[0,1])
~(a1[0,0] & a1[0,2])
~(a1[0,2] & a[0,2])
(a0[0,0] | a0[0,1])
(a1[0,0] | a1[0,2])
((a0[0,0] & ~a1[0,0]) | ((~a0[0,0] & a1[0,0]) | (~a0[0,0] & ~a1[0,0])))
(a[] <-> a[0])
(a[0] <-> (a[0,1] | a[0,2]))
1
-}
--mode ordering failure, cyclic dependency: [0] reverse a0::o a1::i -> [1] a0::i = a::o -> [2] a1::o = a::i
--mode ordering failure, cyclic dependency: [0] reverse a0::i a1::o -> [2] a1::i = a::o -> [1] a0::o = a::i
palindrome_i = \a -> once $ do
  -- solution: a0[0,1] a1[0,2] ~a[] ~a[0] ~a[0,1] ~a[0,2] ~a0[0,0] ~a1[0,0]
  -- cost: 1
  () <- (do
    a0 <- pure a
    a1 <- pure a
    () <- reverse_ii a0 a1
    pure ()
   )
  pure ()

{- duplicate/2
duplicate a b :- ((append a0 a1 b, a0 = a, a1 = a)).
constraints:
~(a[0,1] & a[0,2])
~(a0[0,0] & a0[0,1])
~(a0[0,1] & a[0,1])
~(a1[0,0] & a1[0,2])
~(a1[0,2] & a[0,2])
(a0[0,0] | a0[0,1])
(a1[0,0] | a1[0,2])
((a0[0,0] & (a1[0,0] & ~b[0,0])) | ((a0[0,0] & (~a1[0,0] & ~b[0,0])) | ((~a0[0,0] & (a1[0,0] & ~b[0,0])) | ((~a0[0,0] & (~a1[0,0] & b[0,0])) | (~a0[0,0] & (~a1[0,0] & ~b[0,0]))))))
(a[] <-> a[0])
(a[0] <-> (a[0,1] | a[0,2]))
(b[] <-> b[0])
(b[0] <-> b[0,0])
1
-}
--mode ordering failure, cyclic dependency: [0] append a0::o a1::i b::i -> [1] a0::i = a::o -> [2] a1::o = a::i
--mode ordering failure, cyclic dependency: [0] append a0::i a1::o b::i -> [2] a1::i = a::o -> [1] a0::o = a::i
duplicate_ii = \a b -> once $ do
  -- solution: a0[0,1] a1[0,2] ~a[] ~a[0] ~a[0,1] ~a[0,2] ~a0[0,0] ~a1[0,0] ~b[] ~b[0] ~b[0,0]
  -- cost: 1
  () <- (do
    a0 <- pure a
    a1 <- pure a
    () <- append_iii a0 a1 b
    pure ()
   )
  pure ()

duplicate_io = \a -> do
  -- solution: a0[0,1] a1[0,2] b[] b[0] b[0,0] ~a[] ~a[0] ~a[0,1] ~a[0,2] ~a0[0,0] ~a1[0,0]
  -- cost: 2
  (b) <- (do
    a0 <- pure a
    a1 <- pure a
    (b) <- append_iio a0 a1
    pure (b)
   )
  pure (b)

duplicate_oi = \b -> do
  -- solution: a[] a[0] a[0,1] a0[0,0] a1[0,0] ~a[0,2] ~a0[0,1] ~a1[0,2] ~b[] ~b[0] ~b[0,0]
  -- cost: 3
  (a) <- (do
    (a0,a1) <- append_ooi b
    a <- pure a0
    guard $ a1 == a
    pure (a)
   )
  pure (a)

{- classify/2
classify xs r :- ((if (palindrome xs) then (r = Just data0, data0 = []) else (if (duplicate h xs) then (r = Just h) else (r = Nothing)))).
constraints:
h[0,0,2,0,0]
~h[0,0,2,0,1,0]
~xs[0,0,0,0]
~xs[0,0,2]
~xs[0,0,2,0]
~xs[0,0,2,0,0,0]
~(data0[0,0,1,0] & data0[0,0,1,1])
~(r[0,0,1,0] & data0[0,0,1,0])
~(r[0,0,2,0,1,0] & h[0,0,2,0,1,0])
(data0[0,0,1,0] | data0[0,0,1,1])
((h[0,0,2,0,0,0] & ~xs[0,0,2,0,0,0]) | ((~h[0,0,2,0,0,0] & xs[0,0,2,0,0,0]) | (~h[0,0,2,0,0,0] & ~xs[0,0,2,0,0,0])))
(h[0,0,2,0,0] <-> h[0,0,2,0,0,0])
(r[] <-> r[0])
(r[0] <-> r[0,0])
(r[0,0] <-> (r[0,0,1] | r[0,0,2]))
(r[0,0,1] <-> r[0,0,1,0])
(r[0,0,1] <-> r[0,0,2])
(r[0,0,2] <-> r[0,0,2,0])
(r[0,0,2,0] <-> (r[0,0,2,0,1] | r[0,0,2,0,2]))
(r[0,0,2,0,1] <-> r[0,0,2,0,1,0])
(r[0,0,2,0,1] <-> r[0,0,2,0,2])
(r[0,0,2,0,2] <-> r[0,0,2,0,2,0])
(xs[] <-> xs[0])
(xs[0] <-> xs[0,0])
(xs[0,0] <-> xs[0,0,2])
(xs[0,0,2] <-> xs[0,0,2,0])
1
-}
classify_ii = \xs r -> once $ do
  -- solution: data0[0,0,1,0] h[0,0,2,0,0] h[0,0,2,0,0,0] ~data0[0,0,1,1] ~h[0,0,2,0,1,0] ~r[] ~r[0] ~r[0,0] ~r[0,0,1] ~r[0,0,1,0] ~r[0,0,2] ~r[0,0,2,0] ~r[0,0,2,0,1] ~r[0,0,2,0,1,0] ~r[0,0,2,0,2] ~r[0,0,2,0,2,0] ~xs[] ~xs[0] ~xs[0,0] ~xs[0,0,0,0] ~xs[0,0,2] ~xs[0,0,2,0] ~xs[0,0,2,0,0,0]
  -- cost: 3
  () <- (do
    () <- ifte ((do
      () <- palindrome_i xs
      pure ()
     )) (\() -> (do
      (Just data0) <- pure r
      guard $ data0 == []
      pure ()
     )) ((do
      () <- ifte ((do
        (h) <- duplicate_oi xs
        pure (h)
       )) (\(h) -> (do
        guard $ r == (Just h)
        pure ()
       )) ((do
        guard $ r == Nothing
        pure ()
       ))
      pure ()
     ))
    pure ()
   )
  pure ()

classify_io = \xs -> do
  -- solution: data0[0,0,1,1] h[0,0,2,0,0] h[0,0,2,0,0,0] r[] r[0] r[0,0] r[0,0,1] r[0,0,1,0] r[0,0,2] r[0,0,2,0] r[0,0,2,0,1] r[0,0,2,0,1,0] r[0,0,2,0,2] r[0,0,2,0,2,0] ~data0[0,0,1,0] ~h[0,0,2,0,1,0] ~xs[] ~xs[0] ~xs[0,0] ~xs[0,0,0,0] ~xs[0,0,2] ~xs[0,0,2,0] ~xs[0,0,2,0,0,0]
  -- cost: 3
  (r) <- (do
    (r) <- ifte ((do
      () <- palindrome_i xs
      pure ()
     )) (\() -> (do
      data0 <- pure []
      r <- pure (Just data0)
      pure (r)
     )) ((do
      (r) <- ifte ((do
        (h) <- duplicate_oi xs
        pure (h)
       )) (\(h) -> (do
        r <- pure (Just h)
        pure (r)
       )) ((do
        r <- pure Nothing
        pure (r)
       ))
      pure (r)
     ))
    pure (r)
   )
  pure (r)

{- delete/3
delete arg1 arg2 arg3 :- ((arg2 = h0:t1, h0 = h, t1 = t, arg1 = h, arg3 = t); (arg2 = h2:t3, h2 = h, t3 = t, arg3 = h4:r, h4 = h, delete x t r, arg1 = x)).
constraints:
~(arg1[0,3] & h[0,3])
~(arg1[1,6] & x[1,6])
~(arg2[0,0] & h0[0,0])
~(arg2[1,0] & h2[1,0])
~(arg3[0,4] & t[0,4])
~(arg3[1,3] & h4[1,3])
~(h[0,1] & h[0,3])
~(h[1,1] & h[1,4])
~(h0[0,0] & h0[0,1])
~(h0[0,1] & h[0,1])
~(h2[1,0] & h2[1,1])
~(h2[1,1] & h[1,1])
~(h4[1,3] & h4[1,4])
~(h4[1,4] & h[1,4])
~(r[1,3] & r[1,5])
~(t[0,2] & t[0,4])
~(t[1,2] & t[1,5])
~(t1[0,0] & t1[0,2])
~(t1[0,2] & t[0,2])
~(t3[1,0] & t3[1,2])
~(t3[1,2] & t[1,2])
~(x[1,5] & x[1,6])
(h[0,1] | h[0,3])
(h[1,1] | h[1,4])
(h0[0,0] | h0[0,1])
(h2[1,0] | h2[1,1])
(h4[1,3] | h4[1,4])
(r[1,3] | r[1,5])
(t[0,2] | t[0,4])
(t[1,2] | t[1,5])
(t1[0,0] | t1[0,2])
(t3[1,0] | t3[1,2])
(x[1,5] | x[1,6])
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg1[0] <-> arg1[0,3])
(arg1[1] <-> arg1[1,6])
(arg2[] <-> arg2[0])
(arg2[] <-> arg2[1])
(arg2[0] <-> arg2[0,0])
(arg2[1] <-> arg2[1,0])
(arg3[] <-> arg3[0])
(arg3[] <-> arg3[1])
(arg3[0] <-> arg3[0,4])
(arg3[1] <-> arg3[1,3])
(h0[0,0] <-> t1[0,0])
(h2[1,0] <-> t3[1,0])
(h4[1,3] <-> r[1,3])
(r[1,5] <-> arg3[])
(t[1,5] <-> arg2[])
(x[1,5] <-> arg1[])
1
-}
delete_iii = \arg1 arg2 arg3 -> once $ do
  -- solution: h[0,1] h[1,1] h0[0,0] h2[1,0] h4[1,3] r[1,3] t[0,2] t[1,2] t1[0,0] t3[1,0] x[1,6] ~arg1[] ~arg1[0] ~arg1[0,3] ~arg1[1] ~arg1[1,6] ~arg2[] ~arg2[0] ~arg2[0,0] ~arg2[1] ~arg2[1,0] ~arg3[] ~arg3[0] ~arg3[0,4] ~arg3[1] ~arg3[1,3] ~h[0,3] ~h[1,4] ~h0[0,1] ~h2[1,1] ~h4[1,4] ~r[1,5] ~t[0,4] ~t[1,5] ~t1[0,2] ~t3[1,2] ~x[1,5]
  -- cost: 1
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
    () <- delete_iii x t r
    pure ()
   )
  pure ()

delete_iio = \arg1 arg2 -> do
  -- solution: arg3[] arg3[0] arg3[0,4] arg3[1] arg3[1,3] h[0,1] h[1,1] h0[0,0] h2[1,0] h4[1,4] r[1,5] t[0,2] t[1,2] t1[0,0] t3[1,0] x[1,6] ~arg1[] ~arg1[0] ~arg1[0,3] ~arg1[1] ~arg1[1,6] ~arg2[] ~arg2[0] ~arg2[0,0] ~arg2[1] ~arg2[1,0] ~h[0,3] ~h[1,4] ~h0[0,1] ~h2[1,1] ~h4[1,3] ~r[1,3] ~t[0,4] ~t[1,5] ~t1[0,2] ~t3[1,2] ~x[1,5]
  -- cost: 2
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
    (r) <- delete_iio x t
    arg3 <- pure (h4:r)
    pure (arg3)
   )
  pure (arg3)

delete_ioi = \arg1 arg3 -> do
  -- solution: arg2[] arg2[0] arg2[0,0] arg2[1] arg2[1,0] h[0,3] h[1,4] h0[0,1] h2[1,1] h4[1,3] r[1,3] t[0,4] t[1,5] t1[0,2] t3[1,2] x[1,6] ~arg1[] ~arg1[0] ~arg1[0,3] ~arg1[1] ~arg1[1,6] ~arg3[] ~arg3[0] ~arg3[0,4] ~arg3[1] ~arg3[1,3] ~h[0,1] ~h[1,1] ~h0[0,0] ~h2[1,0] ~h4[1,4] ~r[1,5] ~t[0,2] ~t[1,2] ~t1[0,0] ~t3[1,0] ~x[1,5]
  -- cost: 2
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
    (t) <- delete_ioi x r
    t3 <- pure t
    arg2 <- pure (h2:t3)
    pure (arg2)
   )
  pure (arg2)

delete_oii = \arg2 arg3 -> do
  -- solution: arg1[] arg1[0] arg1[0,3] arg1[1] arg1[1,6] h[0,1] h[1,1] h0[0,0] h2[1,0] h4[1,3] r[1,3] t[0,2] t[1,2] t1[0,0] t3[1,0] x[1,5] ~arg2[] ~arg2[0] ~arg2[0,0] ~arg2[1] ~arg2[1,0] ~arg3[] ~arg3[0] ~arg3[0,4] ~arg3[1] ~arg3[1,3] ~h[0,3] ~h[1,4] ~h0[0,1] ~h2[1,1] ~h4[1,4] ~r[1,5] ~t[0,4] ~t[1,5] ~t1[0,2] ~t3[1,2] ~x[1,6]
  -- cost: 2
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
    (x) <- delete_oii t r
    arg1 <- pure x
    pure (arg1)
   )
  pure (arg1)

delete_oio = \arg2 -> do
  -- solution: arg1[] arg1[0] arg1[0,3] arg1[1] arg1[1,6] arg3[] arg3[0] arg3[0,4] arg3[1] arg3[1,3] h[0,1] h[1,1] h0[0,0] h2[1,0] h4[1,4] r[1,5] t[0,2] t[1,2] t1[0,0] t3[1,0] x[1,5] ~arg2[] ~arg2[0] ~arg2[0,0] ~arg2[1] ~arg2[1,0] ~h[0,3] ~h[1,4] ~h0[0,1] ~h2[1,1] ~h4[1,3] ~r[1,3] ~t[0,4] ~t[1,5] ~t1[0,2] ~t3[1,2] ~x[1,6]
  -- cost: 3
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
    (x,r) <- delete_oio t
    arg1 <- pure x
    arg3 <- pure (h4:r)
    pure (arg1,arg3)
   )
  pure (arg1,arg3)

{- perm/2
perm arg1 arg2 :- ((arg1 = [], arg2 = []); (arg2 = h:t, delete h xs ys, perm ys t, arg1 = xs)).
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
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg1[0] <-> arg1[0,0])
(arg1[1] <-> arg1[1,3])
(arg2[] <-> arg2[0])
(arg2[] <-> arg2[1])
(arg2[0] <-> arg2[0,1])
(arg2[1] <-> arg2[1,0])
(h[1,0] <-> t[1,0])
(t[1,2] <-> arg2[])
(ys[1,2] <-> arg1[])
1
-}
perm_ii = \arg1 arg2 -> once $ do
  -- solution: h[1,0] t[1,0] xs[1,3] ys[1,1] ~arg1[] ~arg1[0] ~arg1[0,0] ~arg1[1] ~arg1[1,3] ~arg2[] ~arg2[0] ~arg2[0,1] ~arg2[1] ~arg2[1,0] ~h[1,1] ~t[1,2] ~xs[1,1] ~ys[1,2]
  -- cost: 3
  () <- (do
    guard $ arg1 == []
    guard $ arg2 == []
    pure ()
   ) <|> (do
    xs <- pure arg1
    (h:t) <- pure arg2
    (ys) <- delete_iio h xs
    () <- perm_ii ys t
    pure ()
   )
  pure ()

perm_io = \arg1 -> do
  -- solution: arg2[] arg2[0] arg2[0,1] arg2[1] arg2[1,0] h[1,1] t[1,2] xs[1,3] ys[1,1] ~arg1[] ~arg1[0] ~arg1[0,0] ~arg1[1] ~arg1[1,3] ~h[1,0] ~t[1,0] ~xs[1,1] ~ys[1,2]
  -- cost: 5
  (arg2) <- (do
    guard $ arg1 == []
    arg2 <- pure []
    pure (arg2)
   ) <|> (do
    xs <- pure arg1
    (h,ys) <- delete_oio xs
    (t) <- perm_io ys
    arg2 <- pure (h:t)
    pure (arg2)
   )
  pure (arg2)

perm_oi = \arg2 -> do
  -- solution: arg1[] arg1[0] arg1[0,0] arg1[1] arg1[1,3] h[1,0] t[1,0] xs[1,1] ys[1,2] ~arg2[] ~arg2[0] ~arg2[0,1] ~arg2[1] ~arg2[1,0] ~h[1,1] ~t[1,2] ~xs[1,3] ~ys[1,1]
  -- cost: 4
  (arg1) <- (do
    arg1 <- pure []
    guard $ arg2 == []
    pure (arg1)
   ) <|> (do
    (h:t) <- pure arg2
    (ys) <- perm_oi t
    (xs) <- delete_ioi h ys
    arg1 <- pure xs
    pure (arg1)
   )
  pure (arg1)
