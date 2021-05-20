{-# OPTIONS_GHC -F -pgmF=horn-preprocessor #-}
module Euler where

#type nat Integer
nat 0
nat n' :- nat n, succ n n'

oddNat 1
oddNat n' :- oddNat n, plus n 2 n'

even x :- mod x 2 0

elem x (x:_)
elem x (_:xs) :- elem x xs
elem' xs x :- elem x xs

span _ [] [] []
span p (x:xs) ys zs :-
  if p x
  then span p xs yt zs, ys = (x:yt)
  else ys = [], zs = (x:xs)

takeWhile p xs ys :- span p xs ys _

reverseDL [] xs xs
reverseDL (h:t) rest r :- reverseDL t (h:rest) r
reverse s r :- reverseDL s [] r

all _ []
all p (h:t) :- p h, all p t

all' _ [] _
all' p (h:t) r :- p h r, all' p t r

multiple y x :- mod x y 0
divisor x y :- mod x y 0

#inline apply
apply f p y :- p x, f x y

#inline apply2
apply2 f p q z :- p x, q y, f x y z

read s x :- show x s

id x x

#nub euler1
euler1 = (| (elem' [0..999]), multiple (| 3 | 5 |) |)

euler1' = sum <$> observeAll euler1

#memo fib
#mode fib In Out
fib 0 0
fib 1 1
fib k fk :- k > 1, succ i j, succ j k, fib i fi, fib j fj, plus fi fj fk

fib' = (| fib nat |)

euler2 = sum <$> takeWhile (< 1000000) <$> observeAll (| fib', even |)

nontrivialDivisor n d :- succ n' n, elem d [2..n'], divisor n d

primeSlow n :- nat n, n > 1, not (nontrivialDivisor n _)

factor n (p:ps) f :-
  if timesInt p p pp, pp > n then id n f
  else if divMod n p d 0 then (| (id p) | (factor d (p:ps)) |) f
  else factor n ps f

#memo prime
prime 2
prime p :-
  oddNat p, p > 2
  observeAll prime primes
  not (factor p primes d, p /= d)

primeFactor n = factor n <$> observeAll prime

euler3 n = maximum <$> observeAll (primeFactor n)

palindrome s :- reverse s s

euler4 = (| timesInt (elem' [10..99]) (elem' [10..99]), read palindrome |)

euler4' = maximum <$> observeAll euler4

euler5 = (| nat, (> 0), (all' multiple [1..5]) |)
