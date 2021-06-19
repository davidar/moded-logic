{-# OPTIONS_GHC -F -pgmF=moded-logic-pp #-}
module HigherOrder where

even n :- mod n 2 0

map _ [] []
map p (x:xs) (y:ys) :- p x y, map p xs ys

succs xs ys :- map succ xs ys

filter _ [] []
filter p (h:t) ts :-
  if p h
  then filter p t t', ts = (h:t')
  else filter p t ts

evens xs ys :- filter even xs ys

foldl _ [] a a
foldl p (h:t) a a'' :- p h a a', foldl p t a' a''

sum xs z r :- foldl plus xs z r
split xs z r :- foldl (\x a a' :- a = (x:a')) xs z r
splitr xs z r :- foldl (\x a a' :- a' = (x:a)) xs z r

closure p x y :- p x y
closure p x y :- p x z, closure p z y

smaller 1 2
smaller 2 3
smallerTransitive x y :- closure smaller x y

compose f g a z :- g a b, f b z
composeTest a z :- compose (times 2) (plus 1) a z

inlineTest y :- (p x :- x = y), p 7
