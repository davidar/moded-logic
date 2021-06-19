{-# OPTIONS_GHC -F -pgmF=moded-logic-pp #-}
module Primes where

integers low high result :-
  if low <= high
  then succ low m, integers m high rest, result = (low:rest)
  else result = []

remove _ [] []
remove p (j:js) result :-
  mod j p m
  remove p js njs
  if m = 0 then result = njs else result = (j:njs)

sift [] []
sift (p:js) (p:ps) :- remove p js new, sift new ps

primes limit ps :- integers 2 limit js, sift js ps
