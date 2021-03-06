{-# OPTIONS_GHC -F -pgmF=moded-logic-pp #-}
module Sort where

partition [] _ [] []
partition (h:t) p lo hi :-
  if h <= p
  then partition t p lo1 hi, lo = (h:lo1)
  else partition t p lo hi1, hi = (h:hi1)

qsort [] r r
qsort (x:xs) r r0 :-
  partition xs x ys zs
  qsort zs r1 r0
  qsort ys r (x:r1)

sort list sorted :- qsort list sorted []
