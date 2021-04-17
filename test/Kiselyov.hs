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
nat_i = \arg1 -> do
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
  pure (arg1)

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

{- insert/3
insert e arg2 arg3 :- ((arg3 = e:l, arg2 = l); (arg2 = h0:t, h0 = h, arg3 = h1:t', h1 = h, insert e t t')).
constraints:
~(arg2[0,1] & l[0,1])
~(arg2[1,0] & h0[1,0])
~(arg3[0,0] & e[0,0])
~(arg3[1,2] & h1[1,2])
~(h[1,1] & h[1,3])
~(h0[1,0] & h0[1,1])
~(h0[1,1] & h[1,1])
~(h1[1,2] & h1[1,3])
~(h1[1,3] & h[1,3])
~(l[0,0] & l[0,1])
~(t[1,0] & t[1,4])
~(t'[1,2] & t'[1,4])
(h[1,1] | h[1,3])
(h0[1,0] | h0[1,1])
(h1[1,2] | h1[1,3])
(l[0,0] | l[0,1])
(t[1,0] | t[1,4])
(t'[1,2] | t'[1,4])
(arg2[] <-> arg2[0])
(arg2[] <-> arg2[1])
(arg2[0] <-> arg2[0,1])
(arg2[1] <-> arg2[1,0])
(arg3[] <-> arg3[0])
(arg3[] <-> arg3[1])
(arg3[0] <-> arg3[0,0])
(arg3[1] <-> arg3[1,2])
(e[] <-> e[0])
(e[] <-> e[1])
(e[0] <-> e[0,0])
(e[0,0] <-> l[0,0])
(e[1] <-> e[1,4])
(e[1,4] <-> e[])
(h0[1,0] <-> t[1,0])
(h1[1,2] <-> t'[1,2])
(t[1,4] <-> arg2[])
(t'[1,4] <-> arg3[])
1
-}
insert_iii = \e arg2 arg3 -> do
  -- solution: h[1,1] h0[1,0] h1[1,2] l[0,1] t[1,0] t'[1,2] ~arg2[] ~arg2[0] ~arg2[0,1] ~arg2[1] ~arg2[1,0] ~arg3[] ~arg3[0] ~arg3[0,0] ~arg3[1] ~arg3[1,2] ~e[] ~e[0] ~e[0,0] ~e[1] ~e[1,4] ~h[1,3] ~h0[1,1] ~h1[1,3] ~l[0,0] ~t[1,4] ~t'[1,4]
  () <- (do
    l <- pure arg2
    guard $ arg3 == (e:l)
    pure ()
   ) <|> (do
    (h0:t) <- pure arg2
    h <- pure h0
    (h1:t') <- pure arg3
    guard $ h1 == h
    () <- insert_iii e t t'
    pure ()
   )
  pure ()

insert_iio = \e arg2 -> do
  -- solution: arg3[] arg3[0] arg3[0,0] arg3[1] arg3[1,2] h[1,1] h0[1,0] h1[1,3] l[0,1] t[1,0] t'[1,4] ~arg2[] ~arg2[0] ~arg2[0,1] ~arg2[1] ~arg2[1,0] ~e[] ~e[0] ~e[0,0] ~e[1] ~e[1,4] ~h[1,3] ~h0[1,1] ~h1[1,2] ~l[0,0] ~t[1,4] ~t'[1,2]
  (arg3) <- (do
    l <- pure arg2
    arg3 <- pure (e:l)
    pure (arg3)
   ) <|> (do
    (h0:t) <- pure arg2
    h <- pure h0
    h1 <- pure h
    (t') <- insert_iio e t
    arg3 <- pure (h1:t')
    pure (arg3)
   )
  pure (arg3)

insert_oii = \arg2 arg3 -> do
  -- solution: e[] e[0] e[0,0] e[1] e[1,4] h[1,1] h0[1,0] h1[1,2] l[0,0] t[1,0] t'[1,2] ~arg2[] ~arg2[0] ~arg2[0,1] ~arg2[1] ~arg2[1,0] ~arg3[] ~arg3[0] ~arg3[0,0] ~arg3[1] ~arg3[1,2] ~h[1,3] ~h0[1,1] ~h1[1,3] ~l[0,1] ~t[1,4] ~t'[1,4]
  (e) <- (do
    (e:l) <- pure arg3
    guard $ arg2 == l
    pure (e)
   ) <|> (do
    (h0:t) <- pure arg2
    h <- pure h0
    (h1:t') <- pure arg3
    guard $ h1 == h
    (e) <- insert_oii t t'
    pure (e)
   )
  pure (e)

insert_ooi = \arg3 -> do
  -- solution: arg2[] arg2[0] arg2[0,1] arg2[1] arg2[1,0] e[] e[0] e[0,0] e[1] e[1,4] h[1,3] h0[1,1] h1[1,2] l[0,0] t[1,4] t'[1,2] ~arg3[] ~arg3[0] ~arg3[0,0] ~arg3[1] ~arg3[1,2] ~h[1,1] ~h0[1,0] ~h1[1,3] ~l[0,1] ~t[1,0] ~t'[1,4]
  (arg2,e) <- (do
    (e:l) <- pure arg3
    arg2 <- pure l
    pure (arg2,e)
   ) <|> (do
    (h1:t') <- pure arg3
    h <- pure h1
    h0 <- pure h
    (e,t) <- insert_ooi t'
    arg2 <- pure (h0:t)
    pure (arg2,e)
   )
  pure (e,arg2)

{- permute/2
permute arg1 arg2 :- ((arg1 = [], arg2 = []); (arg1 = h:t, permute t t', insert h t' r, arg2 = r)).
constraints:
~(arg1[1,0] & h[1,0])
~(arg2[1,3] & r[1,3])
~(h[1,0] & h[1,2])
~(r[1,2] & r[1,3])
~(t[1,0] & t[1,1])
~(t'[1,1] & t'[1,2])
(h[1,0] | h[1,2])
(r[1,2] | r[1,3])
(t[1,0] | t[1,1])
(t'[1,1] | t'[1,2])
((h[1,2] & (t'[1,2] & ~r[1,2])) | ((h[1,2] & (~t'[1,2] & ~r[1,2])) | ((~h[1,2] & (~t'[1,2] & r[1,2])) | (~h[1,2] & (~t'[1,2] & ~r[1,2])))))
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg1[0] <-> arg1[0,0])
(arg1[1] <-> arg1[1,0])
(arg2[] <-> arg2[0])
(arg2[] <-> arg2[1])
(arg2[0] <-> arg2[0,1])
(arg2[1] <-> arg2[1,3])
(h[1,0] <-> t[1,0])
(t[1,1] <-> arg1[])
(t'[1,1] <-> arg2[])
1
-}
permute_io = \arg1 -> do
  -- solution: arg2[] arg2[0] arg2[0,1] arg2[1] arg2[1,3] h[1,0] r[1,2] t[1,0] t'[1,1] ~arg1[] ~arg1[0] ~arg1[0,0] ~arg1[1] ~arg1[1,0] ~h[1,2] ~r[1,3] ~t[1,1] ~t'[1,2]
  (arg2) <- (do
    guard $ arg1 == []
    arg2 <- pure []
    pure (arg2)
   ) <|> (do
    (h:t) <- pure arg1
    (t') <- permute_io t
    (r) <- insert_iio h t'
    arg2 <- pure r
    pure (arg2)
   )
  pure (arg2)

permute_oi = \arg2 -> do
  -- solution: arg1[] arg1[0] arg1[0,0] arg1[1] arg1[1,0] h[1,2] r[1,3] t[1,1] t'[1,2] ~arg2[] ~arg2[0] ~arg2[0,1] ~arg2[1] ~arg2[1,3] ~h[1,0] ~r[1,2] ~t[1,0] ~t'[1,1]
  (arg1) <- (do
    arg1 <- pure []
    guard $ arg2 == []
    pure (arg1)
   ) <|> (do
    r <- pure arg2
    (h,t') <- insert_ooi r
    (t) <- permute_oi t'
    arg1 <- pure (h:t)
    pure (arg1)
   )
  pure (arg1)

{- sorted/1
sorted arg1 :- ((arg1 = []); (arg1 = _:data0, data0 = []); (arg1 = a:data1, data1 = b0:r1, b0 = b, r1 = r, (<=) a b, sorted data2, data2 = b2:r3, b2 = b, r3 = r)).
constraints:
data0[1,0]
~arg1[1,0]
~(a[2,0] & a[2,4])
~(arg1[2,0] & a[2,0])
~(b[2,2] & b[2,4])
~(b[2,2] & b[2,7])
~(b[2,4] & b[2,7])
~(b0[2,1] & b0[2,2])
~(b0[2,2] & b[2,2])
~(b2[2,6] & b2[2,7])
~(b2[2,7] & b[2,7])
~(data0[1,0] & data0[1,1])
~(data1[2,0] & data1[2,1])
~(data1[2,1] & b0[2,1])
~(data2[2,5] & data2[2,6])
~(data2[2,6] & b2[2,6])
~(r[2,3] & r[2,8])
~(r1[2,1] & r1[2,3])
~(r1[2,3] & r[2,3])
~(r3[2,6] & r3[2,8])
~(r3[2,8] & r[2,8])
(~a[2,4] & ~b[2,4])
(a[2,0] | a[2,4])
(b[2,2] | (b[2,4] | b[2,7]))
(b0[2,1] | b0[2,2])
(b2[2,6] | b2[2,7])
(data0[1,0] | data0[1,1])
(data1[2,0] | data1[2,1])
(data2[2,5] | data2[2,6])
(r[2,3] | r[2,8])
(r1[2,1] | r1[2,3])
(r3[2,6] | r3[2,8])
(a[2,0] <-> data1[2,0])
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg1[] <-> arg1[2])
(arg1[0] <-> arg1[0,0])
(arg1[1] <-> arg1[1,0])
(arg1[2] <-> arg1[2,0])
(b0[2,1] <-> r1[2,1])
(b2[2,6] <-> r3[2,6])
(data2[2,5] <-> arg1[])
1
-}
sorted_i = \arg1 -> do
  -- solution: a[2,0] b[2,2] b0[2,1] b2[2,7] data0[1,0] data1[2,0] data2[2,6] r[2,3] r1[2,1] r3[2,8] ~a[2,4] ~arg1[] ~arg1[0] ~arg1[0,0] ~arg1[1] ~arg1[1,0] ~arg1[2] ~arg1[2,0] ~b[2,4] ~b[2,7] ~b0[2,2] ~b2[2,6] ~data0[1,1] ~data1[2,1] ~data2[2,5] ~r[2,8] ~r1[2,3] ~r3[2,6]
  () <- (do
    guard $ arg1 == []
    pure ()
   ) <|> (do
    (_:data0) <- pure arg1
    guard $ data0 == []
    pure ()
   ) <|> (do
    (a:data1) <- pure arg1
    (b0:r1) <- pure data1
    b <- pure b0
    b2 <- pure b
    r <- pure r1
    r3 <- pure r
    data2 <- pure (b2:r3)
    guard $ (<=) a b
    () <- sorted_i data2
    pure ()
   )
  pure ()

{- suffix/2
suffix arg1 arg2 :- ((arg1 = l, arg2 = l); (arg1 = _:t, suffix t r, arg2 = r)).
constraints:
t[1,0]
~arg1[1,0]
~(arg1[0,0] & l[0,0])
~(arg2[0,1] & l[0,1])
~(arg2[1,2] & r[1,2])
~(l[0,0] & l[0,1])
~(r[1,1] & r[1,2])
~(t[1,0] & t[1,1])
(l[0,0] | l[0,1])
(r[1,1] | r[1,2])
(t[1,0] | t[1,1])
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg1[0] <-> arg1[0,0])
(arg1[1] <-> arg1[1,0])
(arg2[] <-> arg2[0])
(arg2[] <-> arg2[1])
(arg2[0] <-> arg2[0,1])
(arg2[1] <-> arg2[1,2])
(r[1,1] <-> arg2[])
(t[1,1] <-> arg1[])
1
-}
suffix_ii = \arg1 arg2 -> do
  -- solution: l[0,0] r[1,2] t[1,0] ~arg1[] ~arg1[0] ~arg1[0,0] ~arg1[1] ~arg1[1,0] ~arg2[] ~arg2[0] ~arg2[0,1] ~arg2[1] ~arg2[1,2] ~l[0,1] ~r[1,1] ~t[1,1]
  () <- (do
    l <- pure arg1
    guard $ arg2 == l
    pure ()
   ) <|> (do
    r <- pure arg2
    (_:t) <- pure arg1
    () <- suffix_ii t r
    pure ()
   )
  pure ()

suffix_io = \arg1 -> do
  -- solution: arg2[] arg2[0] arg2[0,1] arg2[1] arg2[1,2] l[0,0] r[1,1] t[1,0] ~arg1[] ~arg1[0] ~arg1[0,0] ~arg1[1] ~arg1[1,0] ~l[0,1] ~r[1,2] ~t[1,1]
  (arg2) <- (do
    l <- pure arg1
    arg2 <- pure l
    pure (arg2)
   ) <|> (do
    (_:t) <- pure arg1
    (r) <- suffix_io t
    arg2 <- pure r
    pure (arg2)
   )
  pure (arg2)

{- prefix/2
prefix arg1 arg2 :- ((arg2 = []); (arg1 = h0:t, h0 = h, arg2 = h1:t', h1 = h, prefix t t')).
constraints:
~arg1[]
~(arg1[1,0] & h0[1,0])
~(arg2[1,2] & h1[1,2])
~(h[1,1] & h[1,3])
~(h0[1,0] & h0[1,1])
~(h0[1,1] & h[1,1])
~(h1[1,2] & h1[1,3])
~(h1[1,3] & h[1,3])
~(t[1,0] & t[1,4])
~(t'[1,2] & t'[1,4])
(h[1,1] | h[1,3])
(h0[1,0] | h0[1,1])
(h1[1,2] | h1[1,3])
(t[1,0] | t[1,4])
(t'[1,2] | t'[1,4])
(arg1[] <-> arg1[1])
(arg1[1] <-> arg1[1,0])
(arg2[] <-> arg2[0])
(arg2[] <-> arg2[1])
(arg2[0] <-> arg2[0,0])
(arg2[1] <-> arg2[1,2])
(h0[1,0] <-> t[1,0])
(h1[1,2] <-> t'[1,2])
(t[1,4] <-> arg1[])
(t'[1,4] <-> arg2[])
1
-}
prefix_ii = \arg1 arg2 -> do
  -- solution: h[1,1] h0[1,0] h1[1,2] t[1,0] t'[1,2] ~arg1[] ~arg1[1] ~arg1[1,0] ~arg2[] ~arg2[0] ~arg2[0,0] ~arg2[1] ~arg2[1,2] ~h[1,3] ~h0[1,1] ~h1[1,3] ~t[1,4] ~t'[1,4]
  () <- (do
    guard $ arg2 == []
    pure ()
   ) <|> (do
    (h0:t) <- pure arg1
    h <- pure h0
    (h1:t') <- pure arg2
    guard $ h1 == h
    () <- prefix_ii t t'
    pure ()
   )
  pure ()

prefix_io = \arg1 -> do
  -- solution: arg2[] arg2[0] arg2[0,0] arg2[1] arg2[1,2] h[1,1] h0[1,0] h1[1,3] t[1,0] t'[1,4] ~arg1[] ~arg1[1] ~arg1[1,0] ~h[1,3] ~h0[1,1] ~h1[1,2] ~t[1,4] ~t'[1,2]
  (arg2) <- (do
    arg2 <- pure []
    pure (arg2)
   ) <|> (do
    (h0:t) <- pure arg1
    h <- pure h0
    h1 <- pure h
    (t') <- prefix_io t
    arg2 <- pure (h1:t')
    pure (arg2)
   )
  pure (arg2)

{- length/2
length arg1 arg2 :- ((arg1 = [], arg2 = 0); (arg1 = _:t, length t n, succ n n', arg2 = n')).
constraints:
t[1,0]
~arg1[1,0]
~(arg2[1,3] & n'[1,3])
~(n[1,1] & n[1,2])
~(n'[1,2] & n'[1,3])
~(t[1,0] & t[1,1])
(n[1,1] | n[1,2])
(n'[1,2] | n'[1,3])
(t[1,0] | t[1,1])
((n[1,2] & ~n'[1,2]) | ((~n[1,2] & n'[1,2]) | (~n[1,2] & ~n'[1,2])))
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg1[0] <-> arg1[0,0])
(arg1[1] <-> arg1[1,0])
(arg2[] <-> arg2[0])
(arg2[] <-> arg2[1])
(arg2[0] <-> arg2[0,1])
(arg2[1] <-> arg2[1,3])
(n[1,1] <-> arg2[])
(t[1,1] <-> arg1[])
1
-}
length_ii = \arg1 arg2 -> do
  -- solution: n[1,2] n'[1,3] t[1,0] ~arg1[] ~arg1[0] ~arg1[0,0] ~arg1[1] ~arg1[1,0] ~arg2[] ~arg2[0] ~arg2[0,1] ~arg2[1] ~arg2[1,3] ~n[1,1] ~n'[1,2] ~t[1,1]
  () <- (do
    guard $ arg2 == 0
    guard $ arg1 == []
    pure ()
   ) <|> (do
    n' <- pure arg2
    (_:t) <- pure arg1
    (n) <- succ_oi n'
    () <- length_ii t n
    pure ()
   )
  pure ()

length_io = \arg1 -> do
  -- solution: arg2[] arg2[0] arg2[0,1] arg2[1] arg2[1,3] n[1,1] n'[1,2] t[1,0] ~arg1[] ~arg1[0] ~arg1[0,0] ~arg1[1] ~arg1[1,0] ~n[1,2] ~n'[1,3] ~t[1,1]
  (arg2) <- (do
    arg2 <- pure 0
    guard $ arg1 == []
    pure (arg2)
   ) <|> (do
    (_:t) <- pure arg1
    (n) <- length_io t
    (n') <- succ_io n
    arg2 <- pure n'
    pure (arg2)
   )
  pure (arg2)

{- pythag/3
pythag i j k :- ((nat i, (>) i data0, data0 = 0, nat j, (>) j data1, data1 = 0, nat k, (>) k data2, data2 = 0, (<) i j, timesInt i0 i1 ii, i0 = i, i1 = i, timesInt j2 j3 jj, j2 = j, j3 = j, timesInt k4 k5 kk, k4 = k, k5 = k, plus ii jj kk)).
constraints:
~(data0[0,1] & data0[0,2])
~(data1[0,4] & data1[0,5])
~(data2[0,7] & data2[0,8])
~(i[0,0] & i[0,1])
~(i[0,0] & i[0,9])
~(i[0,0] & i[0,11])
~(i[0,0] & i[0,12])
~(i[0,1] & i[0,9])
~(i[0,1] & i[0,11])
~(i[0,1] & i[0,12])
~(i[0,9] & i[0,11])
~(i[0,9] & i[0,12])
~(i[0,11] & i[0,12])
~(i0[0,10] & i0[0,11])
~(i0[0,11] & i[0,11])
~(i1[0,10] & i1[0,12])
~(i1[0,12] & i[0,12])
~(ii[0,10] & ii[0,19])
~(j[0,3] & j[0,4])
~(j[0,3] & j[0,9])
~(j[0,3] & j[0,14])
~(j[0,3] & j[0,15])
~(j[0,4] & j[0,9])
~(j[0,4] & j[0,14])
~(j[0,4] & j[0,15])
~(j[0,9] & j[0,14])
~(j[0,9] & j[0,15])
~(j[0,14] & j[0,15])
~(j2[0,13] & j2[0,14])
~(j2[0,14] & j[0,14])
~(j3[0,13] & j3[0,15])
~(j3[0,15] & j[0,15])
~(jj[0,13] & jj[0,19])
~(k[0,6] & k[0,7])
~(k[0,6] & k[0,17])
~(k[0,6] & k[0,18])
~(k[0,7] & k[0,17])
~(k[0,7] & k[0,18])
~(k[0,17] & k[0,18])
~(k4[0,16] & k4[0,17])
~(k4[0,17] & k[0,17])
~(k5[0,16] & k5[0,18])
~(k5[0,18] & k[0,18])
~(kk[0,16] & kk[0,19])
(~i[0,1] & ~data0[0,1])
(~i[0,9] & ~j[0,9])
(~j[0,4] & ~data1[0,4])
(~k[0,7] & ~data2[0,7])
(data0[0,1] | data0[0,2])
(data1[0,4] | data1[0,5])
(data2[0,7] | data2[0,8])
(i[0,0] | ~i[0,0])
(i0[0,10] | i0[0,11])
(i1[0,10] | i1[0,12])
(ii[0,10] | ii[0,19])
(j[0,3] | ~j[0,3])
(j2[0,13] | j2[0,14])
(j3[0,13] | j3[0,15])
(jj[0,13] | jj[0,19])
(k[0,6] | ~k[0,6])
(k4[0,16] | k4[0,17])
(k5[0,16] | k5[0,18])
(kk[0,16] | kk[0,19])
((i0[0,10] & (~i1[0,10] & ~ii[0,10])) | ((~i0[0,10] & (i1[0,10] & ~ii[0,10])) | (~i0[0,10] & (~i1[0,10] & ii[0,10]))))
((ii[0,19] & (~jj[0,19] & ~kk[0,19])) | ((~ii[0,19] & (jj[0,19] & ~kk[0,19])) | (~ii[0,19] & (~jj[0,19] & kk[0,19]))))
((j2[0,13] & (~j3[0,13] & ~jj[0,13])) | ((~j2[0,13] & (j3[0,13] & ~jj[0,13])) | (~j2[0,13] & (~j3[0,13] & jj[0,13]))))
((k4[0,16] & (~k5[0,16] & ~kk[0,16])) | ((~k4[0,16] & (k5[0,16] & ~kk[0,16])) | (~k4[0,16] & (~k5[0,16] & kk[0,16]))))
(i[] <-> i[0])
(i[0] <-> (i[0,0] | (i[0,1] | (i[0,9] | (i[0,11] | i[0,12])))))
(j[] <-> j[0])
(j[0] <-> (j[0,3] | (j[0,4] | (j[0,9] | (j[0,14] | j[0,15])))))
(k[] <-> k[0])
(k[0] <-> (k[0,6] | (k[0,7] | (k[0,17] | k[0,18]))))
1
-}
-- mode ordering failure, cyclic dependency: [10] timesInt i0::i i1::o ii::i -> [12] i1::i = i::o -> [11] i0::o = i::i
pythag_iii = \i j k -> do
  -- solution: data0[0,2] data1[0,5] data2[0,8] i0[0,10] i1[0,12] ii[0,19] j2[0,14] j3[0,15] jj[0,13] k4[0,17] k5[0,18] kk[0,16] ~data0[0,1] ~data1[0,4] ~data2[0,7] ~i[] ~i[0] ~i[0,0] ~i[0,1] ~i[0,9] ~i[0,11] ~i[0,12] ~i0[0,11] ~i1[0,10] ~ii[0,10] ~j[] ~j[0] ~j[0,3] ~j[0,4] ~j[0,9] ~j[0,14] ~j[0,15] ~j2[0,13] ~j3[0,13] ~jj[0,19] ~k[] ~k[0] ~k[0,6] ~k[0,7] ~k[0,17] ~k[0,18] ~k4[0,16] ~k5[0,16] ~kk[0,19]
  () <- (do
    i1 <- pure i
    j2 <- pure j
    j3 <- pure j
    k4 <- pure k
    k5 <- pure k
    data0 <- pure 0
    data1 <- pure 0
    data2 <- pure 0
    guard $ (<) i j
    guard $ (>) i data0
    guard $ (>) j data1
    guard $ (>) k data2
    () <- nat_i i
    () <- nat_i j
    () <- nat_i k
    (jj) <- timesInt_iio j2 j3
    (kk) <- timesInt_iio k4 k5
    (ii) <- plus_oii jj kk
    (i0) <- timesInt_oii i1 ii
    guard $ i0 == i
    pure ()
   )
  pure ()

pythag_iio = \i j -> do
  -- solution: data0[0,2] data1[0,5] data2[0,8] i0[0,10] i1[0,12] ii[0,19] j2[0,14] j3[0,15] jj[0,13] k[] k[0] k[0,6] k4[0,17] k5[0,18] kk[0,16] ~data0[0,1] ~data1[0,4] ~data2[0,7] ~i[] ~i[0] ~i[0,0] ~i[0,1] ~i[0,9] ~i[0,11] ~i[0,12] ~i0[0,11] ~i1[0,10] ~ii[0,10] ~j[] ~j[0] ~j[0,3] ~j[0,4] ~j[0,9] ~j[0,14] ~j[0,15] ~j2[0,13] ~j3[0,13] ~jj[0,19] ~k[0,7] ~k[0,17] ~k[0,18] ~k4[0,16] ~k5[0,16] ~kk[0,19]
  (k) <- (do
    i1 <- pure i
    j2 <- pure j
    j3 <- pure j
    data0 <- pure 0
    data1 <- pure 0
    data2 <- pure 0
    guard $ (<) i j
    guard $ (>) i data0
    guard $ (>) j data1
    () <- nat_i i
    () <- nat_i j
    (k) <- nat_o 
    k4 <- pure k
    k5 <- pure k
    guard $ (>) k data2
    (jj) <- timesInt_iio j2 j3
    (kk) <- timesInt_iio k4 k5
    (ii) <- plus_oii jj kk
    (i0) <- timesInt_oii i1 ii
    guard $ i0 == i
    pure (k)
   )
  pure (k)

pythag_ioi = \i k -> do
  -- solution: data0[0,2] data1[0,5] data2[0,8] i0[0,10] i1[0,12] ii[0,19] j[] j[0] j[0,3] j2[0,14] j3[0,15] jj[0,13] k4[0,17] k5[0,18] kk[0,16] ~data0[0,1] ~data1[0,4] ~data2[0,7] ~i[] ~i[0] ~i[0,0] ~i[0,1] ~i[0,9] ~i[0,11] ~i[0,12] ~i0[0,11] ~i1[0,10] ~ii[0,10] ~j[0,4] ~j[0,9] ~j[0,14] ~j[0,15] ~j2[0,13] ~j3[0,13] ~jj[0,19] ~k[] ~k[0] ~k[0,6] ~k[0,7] ~k[0,17] ~k[0,18] ~k4[0,16] ~k5[0,16] ~kk[0,19]
  (j) <- (do
    i1 <- pure i
    k4 <- pure k
    k5 <- pure k
    data0 <- pure 0
    data1 <- pure 0
    data2 <- pure 0
    guard $ (>) i data0
    guard $ (>) k data2
    () <- nat_i i
    () <- nat_i k
    (j) <- nat_o 
    j2 <- pure j
    j3 <- pure j
    guard $ (<) i j
    guard $ (>) j data1
    (jj) <- timesInt_iio j2 j3
    (kk) <- timesInt_iio k4 k5
    (ii) <- plus_oii jj kk
    (i0) <- timesInt_oii i1 ii
    guard $ i0 == i
    pure (j)
   )
  pure (j)

pythag_ioo = \i -> do
  -- solution: data0[0,2] data1[0,5] data2[0,8] i0[0,10] i1[0,12] ii[0,19] j[] j[0] j[0,3] j2[0,14] j3[0,15] jj[0,13] k[] k[0] k[0,6] k4[0,17] k5[0,18] kk[0,16] ~data0[0,1] ~data1[0,4] ~data2[0,7] ~i[] ~i[0] ~i[0,0] ~i[0,1] ~i[0,9] ~i[0,11] ~i[0,12] ~i0[0,11] ~i1[0,10] ~ii[0,10] ~j[0,4] ~j[0,9] ~j[0,14] ~j[0,15] ~j2[0,13] ~j3[0,13] ~jj[0,19] ~k[0,7] ~k[0,17] ~k[0,18] ~k4[0,16] ~k5[0,16] ~kk[0,19]
  (j,k) <- (do
    i1 <- pure i
    data0 <- pure 0
    data1 <- pure 0
    data2 <- pure 0
    guard $ (>) i data0
    () <- nat_i i
    (j) <- nat_o 
    j2 <- pure j
    j3 <- pure j
    guard $ (<) i j
    guard $ (>) j data1
    (k) <- nat_o 
    k4 <- pure k
    k5 <- pure k
    guard $ (>) k data2
    (jj) <- timesInt_iio j2 j3
    (kk) <- timesInt_iio k4 k5
    (ii) <- plus_oii jj kk
    (i0) <- timesInt_oii i1 ii
    guard $ i0 == i
    pure (j,k)
   )
  pure (j,k)

pythag_oii = \j k -> do
  -- solution: data0[0,2] data1[0,5] data2[0,8] i[] i[0] i[0,0] i0[0,10] i1[0,12] ii[0,19] j2[0,14] j3[0,15] jj[0,13] k4[0,17] k5[0,18] kk[0,16] ~data0[0,1] ~data1[0,4] ~data2[0,7] ~i[0,1] ~i[0,9] ~i[0,11] ~i[0,12] ~i0[0,11] ~i1[0,10] ~ii[0,10] ~j[] ~j[0] ~j[0,3] ~j[0,4] ~j[0,9] ~j[0,14] ~j[0,15] ~j2[0,13] ~j3[0,13] ~jj[0,19] ~k[] ~k[0] ~k[0,6] ~k[0,7] ~k[0,17] ~k[0,18] ~k4[0,16] ~k5[0,16] ~kk[0,19]
  (i) <- (do
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
    i1 <- pure i
    guard $ (<) i j
    guard $ (>) i data0
    (jj) <- timesInt_iio j2 j3
    (kk) <- timesInt_iio k4 k5
    (ii) <- plus_oii jj kk
    (i0) <- timesInt_oii i1 ii
    guard $ i0 == i
    pure (i)
   )
  pure (i)

pythag_oio = \j -> do
  -- solution: data0[0,2] data1[0,5] data2[0,8] i[] i[0] i[0,0] i0[0,10] i1[0,12] ii[0,19] j2[0,14] j3[0,15] jj[0,13] k[] k[0] k[0,6] k4[0,17] k5[0,18] kk[0,16] ~data0[0,1] ~data1[0,4] ~data2[0,7] ~i[0,1] ~i[0,9] ~i[0,11] ~i[0,12] ~i0[0,11] ~i1[0,10] ~ii[0,10] ~j[] ~j[0] ~j[0,3] ~j[0,4] ~j[0,9] ~j[0,14] ~j[0,15] ~j2[0,13] ~j3[0,13] ~jj[0,19] ~k[0,7] ~k[0,17] ~k[0,18] ~k4[0,16] ~k5[0,16] ~kk[0,19]
  (i,k) <- (do
    j2 <- pure j
    j3 <- pure j
    data0 <- pure 0
    data1 <- pure 0
    data2 <- pure 0
    guard $ (>) j data1
    () <- nat_i j
    (i) <- nat_o 
    i1 <- pure i
    guard $ (<) i j
    guard $ (>) i data0
    (k) <- nat_o 
    k4 <- pure k
    k5 <- pure k
    guard $ (>) k data2
    (jj) <- timesInt_iio j2 j3
    (kk) <- timesInt_iio k4 k5
    (ii) <- plus_oii jj kk
    (i0) <- timesInt_oii i1 ii
    guard $ i0 == i
    pure (i,k)
   )
  pure (i,k)

pythag_ooi = \k -> do
  -- solution: data0[0,2] data1[0,5] data2[0,8] i[] i[0] i[0,0] i0[0,10] i1[0,12] ii[0,19] j[] j[0] j[0,3] j2[0,14] j3[0,15] jj[0,13] k4[0,17] k5[0,18] kk[0,16] ~data0[0,1] ~data1[0,4] ~data2[0,7] ~i[0,1] ~i[0,9] ~i[0,11] ~i[0,12] ~i0[0,11] ~i1[0,10] ~ii[0,10] ~j[0,4] ~j[0,9] ~j[0,14] ~j[0,15] ~j2[0,13] ~j3[0,13] ~jj[0,19] ~k[] ~k[0] ~k[0,6] ~k[0,7] ~k[0,17] ~k[0,18] ~k4[0,16] ~k5[0,16] ~kk[0,19]
  (i,j) <- (do
    k4 <- pure k
    k5 <- pure k
    data0 <- pure 0
    data1 <- pure 0
    data2 <- pure 0
    guard $ (>) k data2
    () <- nat_i k
    (i) <- nat_o 
    i1 <- pure i
    guard $ (>) i data0
    (j) <- nat_o 
    j2 <- pure j
    j3 <- pure j
    guard $ (<) i j
    guard $ (>) j data1
    (jj) <- timesInt_iio j2 j3
    (kk) <- timesInt_iio k4 k5
    (ii) <- plus_oii jj kk
    (i0) <- timesInt_oii i1 ii
    guard $ i0 == i
    pure (i,j)
   )
  pure (i,j)

pythag_ooo = do
  -- solution: data0[0,2] data1[0,5] data2[0,8] i[] i[0] i[0,0] i0[0,10] i1[0,12] ii[0,19] j[] j[0] j[0,3] j2[0,14] j3[0,15] jj[0,13] k[] k[0] k[0,6] k4[0,17] k5[0,18] kk[0,16] ~data0[0,1] ~data1[0,4] ~data2[0,7] ~i[0,1] ~i[0,9] ~i[0,11] ~i[0,12] ~i0[0,11] ~i1[0,10] ~ii[0,10] ~j[0,4] ~j[0,9] ~j[0,14] ~j[0,15] ~j2[0,13] ~j3[0,13] ~jj[0,19] ~k[0,7] ~k[0,17] ~k[0,18] ~k4[0,16] ~k5[0,16] ~kk[0,19]
  (i,j,k) <- (do
    data0 <- pure 0
    data1 <- pure 0
    data2 <- pure 0
    (i) <- nat_o 
    i1 <- pure i
    guard $ (>) i data0
    (j) <- nat_o 
    j2 <- pure j
    j3 <- pure j
    guard $ (<) i j
    guard $ (>) j data1
    (k) <- nat_o 
    k4 <- pure k
    k5 <- pure k
    guard $ (>) k data2
    (jj) <- timesInt_iio j2 j3
    (kk) <- timesInt_iio k4 k5
    (ii) <- plus_oii jj kk
    (i0) <- timesInt_oii i1 ii
    guard $ i0 == i
    pure (i,j,k)
   )
  pure (i,j,k)

{- triang/2
triang n r :- ((succ n n', times n n' nn', div nn' data0 r, data0 = 2)).
constraints:
~(data0[0,2] & data0[0,3])
~(n[0,0] & n[0,1])
~(n'[0,0] & n'[0,1])
~(nn'[0,1] & nn'[0,2])
(data0[0,2] | data0[0,3])
(n'[0,0] | n'[0,1])
(nn'[0,1] | nn'[0,2])
((n[0,0] & ~n'[0,0]) | ((~n[0,0] & n'[0,0]) | (~n[0,0] & ~n'[0,0])))
((n[0,1] & (~n'[0,1] & ~nn'[0,1])) | ((~n[0,1] & (n'[0,1] & ~nn'[0,1])) | (~n[0,1] & (~n'[0,1] & nn'[0,1]))))
((~nn'[0,2] & (~data0[0,2] & r[0,2])) | (~nn'[0,2] & (~data0[0,2] & ~r[0,2])))
(n[] <-> n[0])
(n[0] <-> (n[0,0] | n[0,1]))
(r[] <-> r[0])
(r[0] <-> r[0,2])
1
-}
triang_ii = \n r -> do
  -- solution: data0[0,3] n'[0,0] nn'[0,1] ~data0[0,2] ~n[] ~n[0] ~n[0,0] ~n[0,1] ~n'[0,1] ~nn'[0,2] ~r[] ~r[0] ~r[0,2]
  () <- (do
    data0 <- pure 2
    (n') <- succ_io n
    (nn') <- times_iio n n'
    () <- div_iii nn' data0 r
    pure ()
   )
  pure ()

triang_io = \n -> do
  -- solution: data0[0,3] n'[0,0] nn'[0,1] r[] r[0] r[0,2] ~data0[0,2] ~n[] ~n[0] ~n[0,0] ~n[0,1] ~n'[0,1] ~nn'[0,2]
  (r) <- (do
    data0 <- pure 2
    (n') <- succ_io n
    (nn') <- times_iio n n'
    (r) <- div_iio nn' data0
    pure (r)
   )
  pure (r)

{- ptriang/1
ptriang k :- ((elem k data2, data0 = 1, data1 = 30, data2 = .. data0 data1, elem i data4, data3 = 1, data4 = .. data3 k, elem j data6, data5 = 1, data6 = .. data5 i, triang i ti, triang j tj, triang k tk, plus ti tj tk)).
constraints:
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
~(i[0,4] & i[0,9])
~(i[0,4] & i[0,10])
~(i[0,9] & i[0,10])
~(j[0,7] & j[0,11])
~(k[0,0] & k[0,6])
~(k[0,0] & k[0,12])
~(k[0,6] & k[0,12])
~(ti[0,10] & ti[0,13])
~(tj[0,11] & tj[0,13])
~(tk[0,12] & tk[0,13])
(i[0,4] & ~data4[0,4])
(j[0,7] & ~data6[0,7])
(k[0,0] & ~data2[0,0])
(data0[0,1] | data0[0,3])
(data1[0,2] | data1[0,3])
(data2[0,0] | data2[0,3])
(data3[0,5] | data3[0,6])
(data4[0,4] | data4[0,6])
(data5[0,8] | data5[0,9])
(data6[0,7] | data6[0,9])
(i[0,4] | (i[0,9] | i[0,10]))
(j[0,7] | j[0,11])
(ti[0,10] | ti[0,13])
(tj[0,11] | tj[0,13])
(tk[0,12] | tk[0,13])
((ti[0,13] & (~tj[0,13] & ~tk[0,13])) | ((~ti[0,13] & (tj[0,13] & ~tk[0,13])) | (~ti[0,13] & (~tj[0,13] & tk[0,13]))))
((~i[0,10] & ti[0,10]) | (~i[0,10] & ~ti[0,10]))
((~j[0,11] & tj[0,11]) | (~j[0,11] & ~tj[0,11]))
((~k[0,12] & tk[0,12]) | (~k[0,12] & ~tk[0,12]))
(data0[0,3] <-> data1[0,3])
(data3[0,6] <-> k[0,6])
(data5[0,9] <-> i[0,9])
(k[] <-> k[0])
(k[0] <-> (k[0,0] | (k[0,6] | k[0,12])))
1
-}
ptriang_o = choose . nub . observeAll $ do
  -- solution: data0[0,1] data1[0,2] data2[0,3] data3[0,5] data4[0,6] data5[0,8] data6[0,9] i[0,4] j[0,7] k[] k[0] k[0,0] ti[0,10] tj[0,11] tk[0,13] ~data0[0,3] ~data1[0,3] ~data2[0,0] ~data3[0,6] ~data4[0,4] ~data5[0,9] ~data6[0,7] ~i[0,9] ~i[0,10] ~j[0,11] ~k[0,6] ~k[0,12] ~ti[0,13] ~tj[0,13] ~tk[0,12]
  (k) <- (do
    data0 <- pure 1
    data3 <- pure 1
    data5 <- pure 1
    data1 <- pure 30
    data2 <- pure [data0..data1]
    (k) <- elem_oi data2
    data4 <- pure [data3..k]
    (i) <- elem_oi data4
    data6 <- pure [data5..i]
    (j) <- elem_oi data6
    (ti) <- triang_io i
    (tj) <- triang_io j
    (tk) <- plus_iio ti tj
    () <- triang_ii k tk
    pure (k)
   )
  pure (k)

{- stepN/2
stepN arg1 arg2 :- ((arg1 = 0, arg2 = 0); ((>) n' data0, data0 = 0, succ n n', stepN n i, succ i i', elem r data2, data1 = [], data2 = i:i':data1, arg1 = n', arg2 = r)).
constraints:
~(arg1[1,8] & n'[1,8])
~(arg2[1,9] & r[1,9])
~(data0[1,0] & data0[1,1])
~(data1[1,6] & data1[1,7])
~(data2[1,5] & data2[1,7])
~(data2[1,7] & i[1,7])
~(i[1,3] & i[1,4])
~(i[1,3] & i[1,7])
~(i[1,4] & i[1,7])
~(i'[1,4] & i'[1,7])
~(n[1,2] & n[1,3])
~(n'[1,0] & n'[1,2])
~(n'[1,0] & n'[1,8])
~(n'[1,2] & n'[1,8])
~(r[1,5] & r[1,9])
(r[1,5] & ~data2[1,5])
(~n'[1,0] & ~data0[1,0])
(data0[1,0] | data0[1,1])
(data1[1,6] | data1[1,7])
(data2[1,5] | data2[1,7])
(i[1,3] | (i[1,4] | i[1,7]))
(i'[1,4] | i'[1,7])
(n[1,2] | n[1,3])
(n'[1,0] | (n'[1,2] | n'[1,8]))
(r[1,5] | r[1,9])
((i[1,4] & ~i'[1,4]) | ((~i[1,4] & i'[1,4]) | (~i[1,4] & ~i'[1,4])))
((n[1,2] & ~n'[1,2]) | ((~n[1,2] & n'[1,2]) | (~n[1,2] & ~n'[1,2])))
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg1[0] <-> arg1[0,0])
(arg1[1] <-> arg1[1,8])
(arg2[] <-> arg2[0])
(arg2[] <-> arg2[1])
(arg2[0] <-> arg2[0,1])
(arg2[1] <-> arg2[1,9])
(i[1,3] <-> arg2[])
(i[1,7] <-> data1[1,7])
(i[1,7] <-> i'[1,7])
(n[1,3] <-> arg1[])
1
-}
stepN_io = \arg1 -> choose . nub . observeAll $ do
  -- solution: arg2[] arg2[0] arg2[0,1] arg2[1] arg2[1,9] data0[1,1] data1[1,6] data2[1,7] i[1,3] i'[1,4] n[1,2] n'[1,8] r[1,5] ~arg1[] ~arg1[0] ~arg1[0,0] ~arg1[1] ~arg1[1,8] ~data0[1,0] ~data1[1,7] ~data2[1,5] ~i[1,4] ~i[1,7] ~i'[1,7] ~n[1,3] ~n'[1,0] ~n'[1,2] ~r[1,9]
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
  -- solution: arg1[] arg1[0] arg1[0,0] arg1[1] arg1[1,8] arg2[] arg2[0] arg2[0,1] arg2[1] arg2[1,9] data0[1,1] data1[1,6] data2[1,7] i[1,3] i'[1,4] n[1,3] n'[1,2] r[1,5] ~data0[1,0] ~data1[1,7] ~data2[1,5] ~i[1,4] ~i[1,7] ~i'[1,7] ~n[1,2] ~n'[1,0] ~n'[1,8] ~r[1,9]
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
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg1[] <-> arg1[2])
(arg1[0] <-> arg1[0,0])
(arg1[1] <-> arg1[1,0])
(arg1[2] <-> arg1[2,0])
-}
test_i = \arg1 -> do
  -- solution: ~arg1[] ~arg1[0] ~arg1[0,0] ~arg1[1] ~arg1[1,0] ~arg1[2] ~arg1[2,0]
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
  -- solution: arg1[] arg1[0] arg1[0,0] arg1[1] arg1[1,0] arg1[2] arg1[2,0]
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
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg1[0] <-> arg1[0,0])
(arg1[1] <-> arg1[1,3])
(m[1,0] <-> arg1[])
1
-}
odds_i = \arg1 -> do
  -- solution: data0[1,2] m[1,1] n[1,3] ~arg1[] ~arg1[0] ~arg1[0,0] ~arg1[1] ~arg1[1,3] ~data0[1,1] ~m[1,0] ~n[1,1]
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
  -- solution: arg1[] arg1[0] arg1[0,0] arg1[1] arg1[1,3] data0[1,2] m[1,0] n[1,1] ~data0[1,1] ~m[1,1] ~n[1,3]
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
even_i = \n -> do
  -- solution: data0[0,1] data1[0,0] ~data0[0,0] ~data1[0,2] ~n[] ~n[0] ~n[0,0]
  () <- (do
    data0 <- pure 2
    (data1) <- mod_iio n data0
    guard $ data1 == 0
    pure ()
   )
  pure ()

{- oddsTest/1
oddsTest x :- ((even x, ((odds x); (test x)))).
constraints:
~x[0,0]
~(x[0,0] & x[0,1])
(x[0,1,0,0] | ~x[0,1,0,0])
(x[0,1,1,0] | ~x[0,1,1,0])
(x[] <-> x[0])
(x[0] <-> (x[0,0] | x[0,1]))
(x[0,1] <-> x[0,1,0])
(x[0,1] <-> x[0,1,1])
(x[0,1,0] <-> x[0,1,0,0])
(x[0,1,1] <-> x[0,1,1,0])
-}
oddsTest_i = \x -> do
  -- solution: ~x[] ~x[0] ~x[0,0] ~x[0,1] ~x[0,1,0] ~x[0,1,0,0] ~x[0,1,1] ~x[0,1,1,0]
  () <- (do
    () <- even_i x
    () <- (do
      () <- odds_i x
      pure ()
     ) <|> (do
      () <- test_i x
      pure ()
     )
    pure ()
   )
  pure ()

oddsTest_o = do
  -- solution: x[] x[0] x[0,1] x[0,1,0] x[0,1,0,0] x[0,1,1] x[0,1,1,0] ~x[0,0]
  (x) <- (do
    (x) <- (do
      (x) <- odds_o 
      pure (x)
     ) <|> (do
      (x) <- test_o 
      pure (x)
     )
    () <- even_i x
    pure (x)
   )
  pure (x)

{- oddsPlus/2
oddsPlus n x :- ((odds a, plus a n x)).
constraints:
~(a[0,0] & a[0,1])
(a[0,0] | a[0,1])
(a[0,0] | ~a[0,0])
((a[0,1] & (~n[0,1] & ~x[0,1])) | ((~a[0,1] & (n[0,1] & ~x[0,1])) | (~a[0,1] & (~n[0,1] & x[0,1]))))
(n[] <-> n[0])
(n[0] <-> n[0,1])
(x[] <-> x[0])
(x[0] <-> x[0,1])
1
-}
oddsPlus_ii = \n x -> do
  -- solution: a[0,1] ~a[0,0] ~n[] ~n[0] ~n[0,1] ~x[] ~x[0] ~x[0,1]
  () <- (do
    (a) <- plus_oii n x
    () <- odds_i a
    pure ()
   )
  pure ()

oddsPlus_io = \n -> do
  -- solution: a[0,0] x[] x[0] x[0,1] ~a[0,1] ~n[] ~n[0] ~n[0,1]
  (x) <- (do
    (a) <- odds_o 
    (x) <- plus_iio a n
    pure (x)
   )
  pure (x)

oddsPlus_oi = \x -> do
  -- solution: a[0,0] n[] n[0] n[0,1] ~a[0,1] ~x[] ~x[0] ~x[0,1]
  (n) <- (do
    (a) <- odds_o 
    (n) <- plus_ioi a x
    pure (n)
   )
  pure (n)

{- oddsPlusTest/1
oddsPlusTest x :- ((oddsPlus n x, even x, ((n = 0); (n = 1)))).
constraints:
~x[0,1]
~(n[0,0] & n[0,2])
~(x[0,0] & x[0,1])
(n[0,0] | n[0,2])
((n[0,0] & ~x[0,0]) | ((~n[0,0] & x[0,0]) | (~n[0,0] & ~x[0,0])))
(n[0,2] <-> n[0,2,0])
(n[0,2] <-> n[0,2,1])
(n[0,2,0] <-> n[0,2,0,0])
(n[0,2,1] <-> n[0,2,1,0])
(x[] <-> x[0])
(x[0] <-> (x[0,0] | x[0,1]))
1
-}
oddsPlusTest_i = \x -> do
  -- solution: n[0,0] ~n[0,2] ~n[0,2,0] ~n[0,2,0,0] ~n[0,2,1] ~n[0,2,1,0] ~x[] ~x[0] ~x[0,0] ~x[0,1]
  () <- (do
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
  -- solution: n[0,2] n[0,2,0] n[0,2,0,0] n[0,2,1] n[0,2,1,0] x[] x[0] x[0,0] ~n[0,0] ~x[0,1]
  (x) <- (do
    (n) <- (do
      n <- pure 0
      pure (n)
     ) <|> (do
      n <- pure 1
      pure (n)
     )
    (x) <- oddsPlus_io n
    () <- even_i x
    pure (x)
   )
  pure (x)

{- oddsPrime/1
oddsPrime n :- ((odds n, (>) n data0, data0 = 1, succ n' n, if (elem d data2, data1 = 1, data2 = .. data1 n', (>) d data3, data3 = 1, mod n d data4, data4 = 0) then (empty) else ())).
constraints:
~n[0,4]
~n[0,4,0,5]
~n'[0,4]
~n'[0,4,0,2]
~(d[0,4,0,0] & d[0,4,0,3])
~(d[0,4,0,0] & d[0,4,0,5])
~(d[0,4,0,3] & d[0,4,0,5])
~(data0[0,1] & data0[0,2])
~(data1[0,4,0,1] & data1[0,4,0,2])
~(data2[0,4,0,0] & data2[0,4,0,2])
~(data2[0,4,0,2] & data1[0,4,0,2])
~(data3[0,4,0,3] & data3[0,4,0,4])
~(data4[0,4,0,5] & data4[0,4,0,6])
~(n[0,0] & n[0,1])
~(n[0,0] & n[0,3])
~(n[0,0] & n[0,4])
~(n[0,1] & n[0,3])
~(n[0,1] & n[0,4])
~(n[0,3] & n[0,4])
~(n'[0,3] & n'[0,4])
(d[0,4,0,0] & ~data2[0,4,0,0])
(~d[0,4,0,3] & ~data3[0,4,0,3])
(~n[0,1] & ~data0[0,1])
(d[0,4,0,0] | (d[0,4,0,3] | d[0,4,0,5]))
(data0[0,1] | data0[0,2])
(data1[0,4,0,1] | data1[0,4,0,2])
(data2[0,4,0,0] | data2[0,4,0,2])
(data3[0,4,0,3] | data3[0,4,0,4])
(data4[0,4,0,5] | data4[0,4,0,6])
(n[0,0] | ~n[0,0])
(n'[0,3] | n'[0,4])
((n'[0,3] & ~n[0,3]) | ((~n'[0,3] & n[0,3]) | (~n'[0,3] & ~n[0,3])))
((~n[0,4,0,5] & (~d[0,4,0,5] & data4[0,4,0,5])) | (~n[0,4,0,5] & (~d[0,4,0,5] & ~data4[0,4,0,5])))
(data1[0,4,0,2] <-> n'[0,4,0,2])
(n[] <-> n[0])
(n[0] <-> (n[0,0] | (n[0,1] | (n[0,3] | n[0,4]))))
1
-}
oddsPrime_i = \n -> do
  -- solution: d[0,4,0,0] data0[0,2] data1[0,4,0,1] data2[0,4,0,2] data3[0,4,0,4] data4[0,4,0,5] n'[0,3] ~d[0,4,0,3] ~d[0,4,0,5] ~data0[0,1] ~data1[0,4,0,2] ~data2[0,4,0,0] ~data3[0,4,0,3] ~data4[0,4,0,6] ~n[] ~n[0] ~n[0,0] ~n[0,1] ~n[0,3] ~n[0,4] ~n[0,4,0,5] ~n'[0,4] ~n'[0,4,0,2]
  () <- (do
    data0 <- pure 1
    guard $ (>) n data0
    () <- odds_i n
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
  -- solution: d[0,4,0,0] data0[0,2] data1[0,4,0,1] data2[0,4,0,2] data3[0,4,0,4] data4[0,4,0,5] n[] n[0] n[0,0] n'[0,3] ~d[0,4,0,3] ~d[0,4,0,5] ~data0[0,1] ~data1[0,4,0,2] ~data2[0,4,0,0] ~data3[0,4,0,3] ~data4[0,4,0,6] ~n[0,1] ~n[0,3] ~n[0,4] ~n[0,4,0,5] ~n'[0,4] ~n'[0,4,0,2]
  (n) <- (do
    data0 <- pure 1
    (n) <- odds_o 
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
    pure (n)
   )
  pure (n)

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

{- oddsPrimeIO/1
oddsPrimeIO n :- ((odds n, (>) n data0, data0 = 1, if (nontrivialDivisor n d, print d) then (empty) else ())).
constraints:
~d[0,3,0,1]
~n[0,3]
~n[0,3,0,0]
~(d[0,3,0,0] & d[0,3,0,1])
~(data0[0,1] & data0[0,2])
~(n[0,0] & n[0,1])
~(n[0,0] & n[0,3])
~(n[0,1] & n[0,3])
(~n[0,1] & ~data0[0,1])
(~n[0,3,0,0] & d[0,3,0,0])
(d[0,3,0,0] | d[0,3,0,1])
(data0[0,1] | data0[0,2])
(n[0,0] | ~n[0,0])
(n[] <-> n[0])
(n[0] <-> (n[0,0] | (n[0,1] | n[0,3])))
1
-}
oddsPrimeIO_i = \n -> do
  -- solution: d[0,3,0,0] data0[0,2] ~d[0,3,0,1] ~data0[0,1] ~n[] ~n[0] ~n[0,0] ~n[0,1] ~n[0,3] ~n[0,3,0,0]
  () <- (do
    data0 <- pure 1
    guard $ (>) n data0
    () <- odds_i n
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
  -- solution: d[0,3,0,0] data0[0,2] n[] n[0] n[0,0] ~d[0,3,0,1] ~data0[0,1] ~n[0,1] ~n[0,3] ~n[0,3,0,0]
  (n) <- (do
    data0 <- pure 1
    (n) <- odds_o 
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
    pure (n)
   )
  pure (n)

{- bogosort/2
bogosort l p :- ((permute l p, sorted p)).
constraints:
~p[0,1]
~(p[0,0] & p[0,1])
((l[0,0] & ~p[0,0]) | (~l[0,0] & p[0,0]))
(l[] <-> l[0])
(l[0] <-> l[0,0])
(p[] <-> p[0])
(p[0] <-> (p[0,0] | p[0,1]))
1
-}
bogosort_io = \l -> do
  -- solution: p[] p[0] p[0,0] ~l[] ~l[0] ~l[0,0] ~p[0,1]
  (p) <- (do
    (p) <- permute_io l
    () <- sorted_i p
    pure (p)
   )
  pure (p)

bogosort_oi = \p -> do
  -- solution: l[] l[0] l[0,0] ~p[] ~p[0] ~p[0,0] ~p[0,1]
  (l) <- (do
    () <- sorted_i p
    (l) <- permute_oi p
    pure (l)
   )
  pure (l)

{- tcomp_ex1/1
tcomp_ex1 r :- ((if (((i = 2); (i = 1); (i = 3)), ((j = 0); (j = 1)), i = j) then (r = Just i) else (r = Nothing))).
constraints:
i[0,0,0]
~i[0,0,1,0]
~(i[0,0,0,0] & i[0,0,0,2])
~(i[0,0,0,2] & j[0,0,0,2])
~(j[0,0,0,1] & j[0,0,0,2])
~(r[0,0,1,0] & i[0,0,1,0])
(j[0,0,0,1] | j[0,0,0,2])
(i[0,0,0] <-> (i[0,0,0,0] | i[0,0,0,2]))
(i[0,0,0,0] <-> i[0,0,0,0,0])
(i[0,0,0,0] <-> i[0,0,0,0,1])
(i[0,0,0,0] <-> i[0,0,0,0,2])
(i[0,0,0,0,0] <-> i[0,0,0,0,0,0])
(i[0,0,0,0,1] <-> i[0,0,0,0,1,0])
(i[0,0,0,0,2] <-> i[0,0,0,0,2,0])
(j[0,0,0,1] <-> j[0,0,0,1,0])
(j[0,0,0,1] <-> j[0,0,0,1,1])
(j[0,0,0,1,0] <-> j[0,0,0,1,0,0])
(j[0,0,0,1,1] <-> j[0,0,0,1,1,0])
(r[] <-> r[0])
(r[0] <-> r[0,0])
(r[0,0] <-> (r[0,0,1] | r[0,0,2]))
(r[0,0,1] <-> r[0,0,1,0])
(r[0,0,1] <-> r[0,0,2])
(r[0,0,2] <-> r[0,0,2,0])
1
-}
tcomp_ex1_i = \r -> do
  -- solution: i[0,0,0] i[0,0,0,0] i[0,0,0,0,0] i[0,0,0,0,0,0] i[0,0,0,0,1] i[0,0,0,0,1,0] i[0,0,0,0,2] i[0,0,0,0,2,0] j[0,0,0,1] j[0,0,0,1,0] j[0,0,0,1,0,0] j[0,0,0,1,1] j[0,0,0,1,1,0] ~i[0,0,0,2] ~i[0,0,1,0] ~j[0,0,0,2] ~r[] ~r[0] ~r[0,0] ~r[0,0,1] ~r[0,0,1,0] ~r[0,0,2] ~r[0,0,2,0]
  () <- (do
    () <- ifte ((do
      (j) <- (do
        j <- pure 0
        pure (j)
       ) <|> (do
        j <- pure 1
        pure (j)
       )
      (i) <- (do
        i <- pure 2
        pure (i)
       ) <|> (do
        i <- pure 1
        pure (i)
       ) <|> (do
        i <- pure 3
        pure (i)
       )
      guard $ i == j
      pure (i)
     )) (\(i) -> (do
      guard $ r == (Just i)
      pure ()
     )) ((do
      guard $ r == Nothing
      pure ()
     ))
    pure ()
   )
  pure ()

tcomp_ex1_o = do
  -- solution: i[0,0,0] i[0,0,0,0] i[0,0,0,0,0] i[0,0,0,0,0,0] i[0,0,0,0,1] i[0,0,0,0,1,0] i[0,0,0,0,2] i[0,0,0,0,2,0] j[0,0,0,1] j[0,0,0,1,0] j[0,0,0,1,0,0] j[0,0,0,1,1] j[0,0,0,1,1,0] r[] r[0] r[0,0] r[0,0,1] r[0,0,1,0] r[0,0,2] r[0,0,2,0] ~i[0,0,0,2] ~i[0,0,1,0] ~j[0,0,0,2]
  (r) <- (do
    (r) <- ifte ((do
      (j) <- (do
        j <- pure 0
        pure (j)
       ) <|> (do
        j <- pure 1
        pure (j)
       )
      (i) <- (do
        i <- pure 2
        pure (i)
       ) <|> (do
        i <- pure 1
        pure (i)
       ) <|> (do
        i <- pure 3
        pure (i)
       )
      guard $ i == j
      pure (i)
     )) (\(i) -> (do
      r <- pure (Just i)
      pure (r)
     )) ((do
      r <- pure Nothing
      pure (r)
     ))
    pure (r)
   )
  pure (r)

{- findI/3
findI pat str i :- ((suffix str t, prefix t pat, length t m, length str n, plus i m n)).
constraints:
~(m[0,2] & m[0,4])
~(n[0,3] & n[0,4])
~(str[0,0] & str[0,3])
~(t[0,0] & t[0,1])
~(t[0,0] & t[0,2])
~(t[0,1] & t[0,2])
(m[0,2] | m[0,4])
(n[0,3] | n[0,4])
(t[0,0] | (t[0,1] | t[0,2]))
((i[0,4] & (~m[0,4] & ~n[0,4])) | ((~i[0,4] & (m[0,4] & ~n[0,4])) | (~i[0,4] & (~m[0,4] & n[0,4]))))
((~str[0,0] & t[0,0]) | (~str[0,0] & ~t[0,0]))
((~str[0,3] & n[0,3]) | (~str[0,3] & ~n[0,3]))
((~t[0,1] & pat[0,1]) | (~t[0,1] & ~pat[0,1]))
((~t[0,2] & m[0,2]) | (~t[0,2] & ~m[0,2]))
(i[] <-> i[0])
(i[0] <-> i[0,4])
(pat[] <-> pat[0])
(pat[0] <-> pat[0,1])
(str[] <-> str[0])
(str[0] <-> (str[0,0] | str[0,3]))
1
-}
findI_iii = \pat str i -> do
  -- solution: m[0,2] n[0,4] t[0,0] ~i[] ~i[0] ~i[0,4] ~m[0,4] ~n[0,3] ~pat[] ~pat[0] ~pat[0,1] ~str[] ~str[0] ~str[0,0] ~str[0,3] ~t[0,1] ~t[0,2]
  () <- (do
    (t) <- suffix_io str
    () <- prefix_ii t pat
    (m) <- length_io t
    (n) <- plus_iio i m
    () <- length_ii str n
    pure ()
   )
  pure ()

findI_iio = \pat str -> do
  -- solution: i[] i[0] i[0,4] m[0,2] n[0,3] t[0,0] ~m[0,4] ~n[0,4] ~pat[] ~pat[0] ~pat[0,1] ~str[] ~str[0] ~str[0,0] ~str[0,3] ~t[0,1] ~t[0,2]
  (i) <- (do
    (n) <- length_io str
    (t) <- suffix_io str
    () <- prefix_ii t pat
    (m) <- length_io t
    (i) <- plus_oii m n
    pure (i)
   )
  pure (i)

findI_oii = \str i -> do
  -- solution: m[0,2] n[0,4] pat[] pat[0] pat[0,1] t[0,0] ~i[] ~i[0] ~i[0,4] ~m[0,4] ~n[0,3] ~str[] ~str[0] ~str[0,0] ~str[0,3] ~t[0,1] ~t[0,2]
  (pat) <- (do
    (t) <- suffix_io str
    (m) <- length_io t
    (n) <- plus_iio i m
    () <- length_ii str n
    (pat) <- prefix_io t
    pure (pat)
   )
  pure (pat)

findI_oio = \str -> do
  -- solution: i[] i[0] i[0,4] m[0,2] n[0,3] pat[] pat[0] pat[0,1] t[0,0] ~m[0,4] ~n[0,4] ~str[] ~str[0] ~str[0,0] ~str[0,3] ~t[0,1] ~t[0,2]
  (i,pat) <- (do
    (n) <- length_io str
    (t) <- suffix_io str
    (m) <- length_io t
    (i) <- plus_oii m n
    (pat) <- prefix_io t
    pure (i,pat)
   )
  pure (pat,i)
