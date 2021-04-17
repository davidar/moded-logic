{-# LANGUAGE NoMonomorphismRestriction #-}
module Primes where

import Control.Applicative
import Control.Monad.Logic
import Control.Monad.Logic.Moded.Prelude
import Data.List
import Data.MemoTrie

{- integers/3
integers low high result :- ((if ((<=) low high) then (succ low m, integers m high rest, result = low:rest) else (result = []))).
constraints:
~high[0,0]
~high[0,0,0,0]
~high[0,0,1,1]
~low[0,0]
~low[0,0,0,0]
~(low[0,0,1,0] & low[0,0,1,2])
~(m[0,0,1,0] & m[0,0,1,1])
~(rest[0,0,1,1] & rest[0,0,1,2])
~(result[0,0,1,2] & low[0,0,1,2])
~(low[0,0,1,0] | low[0,0,1,2])
(~low[0,0,0,0] & ~high[0,0,0,0])
(m[0,0,1,0] | m[0,0,1,1])
(rest[0,0,1,1] | rest[0,0,1,2])
((low[0,0,1,0] & ~m[0,0,1,0]) | ((~low[0,0,1,0] & m[0,0,1,0]) | (~low[0,0,1,0] & ~m[0,0,1,0])))
(high[] <-> high[0])
(high[0] <-> high[0,0])
(high[0,0,1,1] <-> high[])
(low[] <-> low[0])
(low[0] <-> low[0,0])
(low[0,0,1,2] <-> rest[0,0,1,2])
(m[0,0,1,1] <-> low[])
(rest[0,0,1,1] <-> result[])
(result[] <-> result[0])
(result[0] <-> result[0,0])
(result[0,0] <-> (result[0,0,1] | result[0,0,2]))
(result[0,0,1] <-> result[0,0,1,2])
(result[0,0,1] <-> result[0,0,2])
(result[0,0,2] <-> result[0,0,2,0])
1
-}
integers_iio = \low high -> do
  -- solution: m[0,0,1,0] rest[0,0,1,1] result[] result[0] result[0,0] result[0,0,1] result[0,0,1,2] result[0,0,2] result[0,0,2,0] ~high[] ~high[0] ~high[0,0] ~high[0,0,0,0] ~high[0,0,1,1] ~low[] ~low[0] ~low[0,0] ~low[0,0,0,0] ~low[0,0,1,0] ~low[0,0,1,2] ~m[0,0,1,1] ~rest[0,0,1,2]
  (result) <- (do
    (result) <- ifte ((do
      guard $ (<=) low high
      pure ()
     )) (\() -> (do
      (m) <- succ_io low
      (rest) <- integers_iio m high
      result <- pure (low:rest)
      pure (result)
     )) ((do
      result <- pure []
      pure (result)
     ))
    pure (result)
   )
  pure (result)

{- remove/3
remove arg1 arg2 arg3 :- ((arg2 = [], arg3 = []); (arg2 = j0:js, j0 = j, mod j p m, remove p js njs, if (m = 0) then (result = njs) else (result = j1:njs, j1 = j), arg1 = p, arg3 = result)).
constraints:
~arg1[]
~j[1,4,2]
~m[1,4]
~m[1,4,0,0]
~(arg1[1,5] & p[1,5])
~(arg2[1,0] & j0[1,0])
~(arg3[1,6] & result[1,6])
~(j[1,1] & j[1,2])
~(j[1,1] & j[1,4])
~(j[1,2] & j[1,4])
~(j0[1,0] & j0[1,1])
~(j0[1,1] & j[1,1])
~(j1[1,4,2,0] & j1[1,4,2,1])
~(j1[1,4,2,1] & j[1,4,2,1])
~(js[1,0] & js[1,3])
~(m[1,2] & m[1,4])
~(njs[1,3] & njs[1,4])
~(p[1,2] & p[1,3])
~(p[1,2] & p[1,5])
~(p[1,3] & p[1,5])
~(result[1,4] & result[1,6])
~(result[1,4,1,0] & njs[1,4,1,0])
~(result[1,4,2,0] & j1[1,4,2,0])
(j[1,1] | (j[1,2] | j[1,4]))
(j0[1,0] | j0[1,1])
(j1[1,4,2,0] | j1[1,4,2,1])
(js[1,0] | js[1,3])
(m[1,2] | m[1,4])
(njs[1,3] | njs[1,4])
(p[1,2] | (p[1,3] | p[1,5]))
(result[1,4] | result[1,6])
((~j[1,2] & (~p[1,2] & m[1,2])) | (~j[1,2] & (~p[1,2] & ~m[1,2])))
(arg1[] <-> arg1[1])
(arg1[1] <-> arg1[1,5])
(arg2[] <-> arg2[0])
(arg2[] <-> arg2[1])
(arg2[0] <-> arg2[0,0])
(arg2[1] <-> arg2[1,0])
(arg3[] <-> arg3[0])
(arg3[] <-> arg3[1])
(arg3[0] <-> arg3[0,1])
(arg3[1] <-> arg3[1,6])
(j[1,4] <-> j[1,4,2])
(j[1,4,2] <-> j[1,4,2,1])
(j0[1,0] <-> js[1,0])
(j1[1,4,2,0] <-> njs[1,4,2,0])
(js[1,3] <-> arg2[])
(njs[1,3] <-> arg3[])
(njs[1,4] <-> (njs[1,4,1] | njs[1,4,2]))
(njs[1,4,1] <-> njs[1,4,1,0])
(njs[1,4,1] <-> njs[1,4,2])
(njs[1,4,2] <-> njs[1,4,2,0])
(p[1,3] <-> arg1[])
(result[1,4] <-> (result[1,4,1] | result[1,4,2]))
(result[1,4,1] <-> result[1,4,1,0])
(result[1,4,1] <-> result[1,4,2])
(result[1,4,2] <-> result[1,4,2,0])
1
-}
remove_iii = \arg1 arg2 arg3 -> do
  -- solution: j[1,1] j0[1,0] j1[1,4,2,0] js[1,0] m[1,2] njs[1,4] njs[1,4,1] njs[1,4,1,0] njs[1,4,2] njs[1,4,2,0] p[1,5] result[1,6] ~arg1[] ~arg1[1] ~arg1[1,5] ~arg2[] ~arg2[0] ~arg2[0,0] ~arg2[1] ~arg2[1,0] ~arg3[] ~arg3[0] ~arg3[0,1] ~arg3[1] ~arg3[1,6] ~j[1,2] ~j[1,4] ~j[1,4,2] ~j[1,4,2,1] ~j0[1,1] ~j1[1,4,2,1] ~js[1,3] ~m[1,4] ~m[1,4,0,0] ~njs[1,3] ~p[1,2] ~p[1,3] ~result[1,4] ~result[1,4,1] ~result[1,4,1,0] ~result[1,4,2] ~result[1,4,2,0]
  () <- (do
    guard $ arg2 == []
    guard $ arg3 == []
    pure ()
   ) <|> (do
    p <- pure arg1
    result <- pure arg3
    (j0:js) <- pure arg2
    j <- pure j0
    (m) <- mod_iio j p
    (njs) <- ifte ((do
      guard $ m == 0
      pure ()
     )) (\() -> (do
      njs <- pure result
      pure (njs)
     )) ((do
      (j1:njs) <- pure result
      guard $ j1 == j
      pure (njs)
     ))
    () <- remove_iii p js njs
    pure ()
   )
  pure ()

remove_iio = \arg1 arg2 -> do
  -- solution: arg3[] arg3[0] arg3[0,1] arg3[1] arg3[1,6] j[1,1] j0[1,0] j1[1,4,2,1] js[1,0] m[1,2] njs[1,3] p[1,5] result[1,4] result[1,4,1] result[1,4,1,0] result[1,4,2] result[1,4,2,0] ~arg1[] ~arg1[1] ~arg1[1,5] ~arg2[] ~arg2[0] ~arg2[0,0] ~arg2[1] ~arg2[1,0] ~j[1,2] ~j[1,4] ~j[1,4,2] ~j[1,4,2,1] ~j0[1,1] ~j1[1,4,2,0] ~js[1,3] ~m[1,4] ~m[1,4,0,0] ~njs[1,4] ~njs[1,4,1] ~njs[1,4,1,0] ~njs[1,4,2] ~njs[1,4,2,0] ~p[1,2] ~p[1,3] ~result[1,6]
  (arg3) <- (do
    guard $ arg2 == []
    arg3 <- pure []
    pure (arg3)
   ) <|> (do
    p <- pure arg1
    (j0:js) <- pure arg2
    j <- pure j0
    (m) <- mod_iio j p
    (njs) <- remove_iio p js
    (result) <- ifte ((do
      guard $ m == 0
      pure ()
     )) (\() -> (do
      result <- pure njs
      pure (result)
     )) ((do
      j1 <- pure j
      result <- pure (j1:njs)
      pure (result)
     ))
    arg3 <- pure result
    pure (arg3)
   )
  pure (arg3)

{- sift/2
sift arg1 arg2 :- ((arg1 = [], arg2 = []); (arg1 = p0:js, p0 = p, arg2 = p1:ps, p1 = p, remove p js new, sift new ps)).
constraints:
~(arg1[1,0] & p0[1,0])
~(arg2[1,2] & p1[1,2])
~(js[1,0] & js[1,4])
~(new[1,4] & new[1,5])
~(p[1,1] & p[1,3])
~(p[1,1] & p[1,4])
~(p[1,3] & p[1,4])
~(p0[1,0] & p0[1,1])
~(p0[1,1] & p[1,1])
~(p1[1,2] & p1[1,3])
~(p1[1,3] & p[1,3])
~(ps[1,2] & ps[1,5])
(js[1,0] | js[1,4])
(new[1,4] | new[1,5])
(p[1,1] | (p[1,3] | p[1,4]))
(p0[1,0] | p0[1,1])
(p1[1,2] | p1[1,3])
(ps[1,2] | ps[1,5])
((~p[1,4] & (~js[1,4] & new[1,4])) | (~p[1,4] & (~js[1,4] & ~new[1,4])))
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg1[0] <-> arg1[0,0])
(arg1[1] <-> arg1[1,0])
(arg2[] <-> arg2[0])
(arg2[] <-> arg2[1])
(arg2[0] <-> arg2[0,1])
(arg2[1] <-> arg2[1,2])
(new[1,5] <-> arg1[])
(p0[1,0] <-> js[1,0])
(p1[1,2] <-> ps[1,2])
(ps[1,5] <-> arg2[])
1
-}
sift_ii = \arg1 arg2 -> do
  -- solution: js[1,0] new[1,4] p[1,1] p0[1,0] p1[1,2] ps[1,2] ~arg1[] ~arg1[0] ~arg1[0,0] ~arg1[1] ~arg1[1,0] ~arg2[] ~arg2[0] ~arg2[0,1] ~arg2[1] ~arg2[1,2] ~js[1,4] ~new[1,5] ~p[1,3] ~p[1,4] ~p0[1,1] ~p1[1,3] ~ps[1,5]
  () <- (do
    guard $ arg1 == []
    guard $ arg2 == []
    pure ()
   ) <|> (do
    (p0:js) <- pure arg1
    p <- pure p0
    (p1:ps) <- pure arg2
    guard $ p1 == p
    (new) <- remove_iio p js
    () <- sift_ii new ps
    pure ()
   )
  pure ()

sift_io = \arg1 -> do
  -- solution: arg2[] arg2[0] arg2[0,1] arg2[1] arg2[1,2] js[1,0] new[1,4] p[1,1] p0[1,0] p1[1,3] ps[1,5] ~arg1[] ~arg1[0] ~arg1[0,0] ~arg1[1] ~arg1[1,0] ~js[1,4] ~new[1,5] ~p[1,3] ~p[1,4] ~p0[1,1] ~p1[1,2] ~ps[1,2]
  (arg2) <- (do
    guard $ arg1 == []
    arg2 <- pure []
    pure (arg2)
   ) <|> (do
    (p0:js) <- pure arg1
    p <- pure p0
    p1 <- pure p
    (new) <- remove_iio p js
    (ps) <- sift_io new
    arg2 <- pure (p1:ps)
    pure (arg2)
   )
  pure (arg2)

{- primes/2
primes limit ps :- ((integers data0 limit js, data0 = 2, sift js ps)).
constraints:
~(data0[0,0] & data0[0,1])
~(js[0,0] & js[0,2])
(~data0[0,0] & (~limit[0,0] & js[0,0]))
(data0[0,0] | data0[0,1])
(js[0,0] | js[0,2])
((~js[0,2] & ps[0,2]) | (~js[0,2] & ~ps[0,2]))
(limit[] <-> limit[0])
(limit[0] <-> limit[0,0])
(ps[] <-> ps[0])
(ps[0] <-> ps[0,2])
1
-}
primes_ii = \limit ps -> do
  -- solution: data0[0,1] js[0,0] ~data0[0,0] ~js[0,2] ~limit[] ~limit[0] ~limit[0,0] ~ps[] ~ps[0] ~ps[0,2]
  () <- (do
    data0 <- pure 2
    (js) <- integers_iio data0 limit
    () <- sift_ii js ps
    pure ()
   )
  pure ()

primes_io = \limit -> do
  -- solution: data0[0,1] js[0,0] ps[] ps[0] ps[0,2] ~data0[0,0] ~js[0,2] ~limit[] ~limit[0] ~limit[0,0]
  (ps) <- (do
    data0 <- pure 2
    (js) <- integers_iio data0 limit
    (ps) <- sift_io js
    pure (ps)
   )
  pure (ps)
