{-# OPTIONS_GHC -F -pgmF=moded-logic-pp #-}
module Queens where

qdelete h (h:t) t
qdelete x (h:t) (h:r) :- qdelete x t r
qperm [] []
qperm xs (h:t) :- qdelete h xs ys, qperm ys t

nodiag _ _ []
nodiag b d (h:t) :-
  plus hmb b h
  plus bmh h b
  succ d d1
  if d = hmb then empty
  else if d = bmh then empty
  else nodiag b d1 t

safe []
safe (h:t) :- nodiag h 1 t, safe t

queens1 dat out :- qperm dat out, safe out

cqueens [] _ []
cqueens xs history (q:m) :-
  xs = (_:_)
  qdelete q xs r
  nodiag q 1 history
  cqueens r (q:history) m

queens2 dat out :- cqueens dat [] out
