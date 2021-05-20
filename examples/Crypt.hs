{-# OPTIONS_GHC -F -pgmF=horn-preprocessor #-}
#module Crypt where

sumDigits [] [] carry cs :-
  if carry = 0 then cs = [] else cs = [carry]
sumDigits [] (b:bs) carry (c:cs) :-
  if carry = 0 then c = b, cs = bs else
  plus b carry x
  divMod x 10 carry' c
  sumDigits [] bs carry' cs
sumDigits (a:as) [] carry (c:cs) :-
  if carry = 0 then c = a, cs = as else
  plus a carry x
  divMod x 10 carry' c
  sumDigits [] as carry' cs
sumDigits (a:as) (b:bs) carry (c:cs) :-
  sum [a, b, carry] x
  divMod x 10 carry' c
  sumDigits as bs carry' cs

mulDigits (a:as) d carry (b:bs) :-
  timesInt a d ad
  plus ad carry x
  divMod x 10 carry' b
  mulDigits as d carry' bs
mulDigits [] _ carry [c,c'] :-
  divMod carry 10 c' c

zeros []
zeros (z:zs) :- z = 0, zeros zs

oddDigit 1
oddDigit 3
oddDigit 5
oddDigit 7
oddDigit 9

evenDigit 0
evenDigit 2
evenDigit 4
evenDigit 6
evenDigit 8

crypt [a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p] :-
  oddDigit a, evenDigit b, evenDigit c
  evenDigit d, d > 0, evenDigit e
  mulDigits [c,b,a] e 0 (i:h:g:f:x)
  evenDigit f, f > 0, oddDigit g, evenDigit h, evenDigit i
  zeros x
  mulDigits [c,b,a] d 0 (l:k:j:y)
  evenDigit j, j > 0, oddDigit k, evenDigit l
  zeros y
  sumDigits [i,h,g,f] [0,l,k,j] 0 (p:o:n:m:z)
  oddDigit m, oddDigit n, evenDigit o, evenDigit p
  zeros z
