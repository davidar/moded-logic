{-# OPTIONS_GHC -F -pgmF=horn-preprocessor #-}
module Append where

append [] b b
append (h:t) b (h:tb) :- append t b tb

append3 a b c abc :-
  append a b ab, append ab c abc

reverse [] []
reverse (h:t) l :- reverse t r, append r [h] l

palindrome a :- reverse a a
duplicate a b :- append a a b
classify xs r :- if palindrome xs then r = Just []
            else if duplicate h xs then r = Just h
            else r = Nothing

delete h (h:t) t
delete x (h:t) (h:r) :- delete x t r
perm [] []
perm xs (h:t) :- delete h xs ys, perm ys t

last xs x :- append _ [x] xs

id x x
