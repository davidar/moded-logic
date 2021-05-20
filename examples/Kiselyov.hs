{-# OPTIONS_GHC -F -pgmF=horn-preprocessor #-}
module Kiselyov where

nat 0
nat n' :- nat n, succ n n'

elem x (x:_)
elem x (_:xs) :- elem x xs

insert e l (e:l)
insert e (h:t) (h:t') :- insert e t t'

permute [] []
permute (h:t) r :- permute t t', insert h t' r

sorted []
sorted [_]
sorted (a:b:r) :- a <= b, sorted (b:r)

suffix l l
suffix (_:t) r :- suffix t r

prefix _ []
prefix (h:t) (h:t') :- prefix t t'

length [] 0
length (_:t) n' :- length t n, succ n n'

#inline apply
apply f p y :- p x, f x y

id x x

-- http://okmij.org/ftp/Computation/monads.html#fair-bt-stream
pythag i j k :-
  nat i, i > 0, nat j, j > 0, nat k, k > 0, i < j
  timesInt i i ii, timesInt j j jj, timesInt k k kk
  plus ii jj kk

-- http://okmij.org/ftp/Haskell/set-monad.html
triang n r :- succ n n', timesInt n n' nn', div nn' 2 r

#nub ptriang
ptriang k :-
  elem k [1..30], elem i [1..k], elem j [1..i]
  triang i ti, triang j tj, triang k tk
  plus ti tj tk

#nub stepN
stepN 0 0
stepN n' r :- n' > 0, succ n n', stepN n i, succ i i', elem r [i,i']

-- http://okmij.org/ftp/papers/LogicT.pdf
test 10
test 20
test 30

odds 1
odds n :- odds m, plus 2 m n

even n :- mod n 2 0

oddsTest = (| (| odds | test |), even |)

oddsPlus n x :- odds a, plus a n x

oddsPlusTest = (| oddsPlus (| 0 | 1 |), even |)

oddsPrime n :-
  odds n, n > 1, succ n' n
  not (elem d [1..n'], d > 1, mod n d 0)

nontrivialDivisor n d :- succ n' n, elem d [2..n'], mod n d 0

oddsPrimeIO n :-
  odds n, n > 1
  not (nontrivialDivisor n d, print d)

bogosort l p :- permute l p, sorted p

-- http://okmij.org/ftp/continuations/generators.html#logicT
equal p q = (| p, q |)

tcomp i j k = equal (| i | j | k |) (| 0 | 1 |)

tcomp_ex1 r :-
  if tcomp (id 2) (id 1) (id 3) i
  then r = Just i else r = Nothing

findI pat str i :-
  suffix str t, prefix t pat
  length t m, length str n, plus i m n
