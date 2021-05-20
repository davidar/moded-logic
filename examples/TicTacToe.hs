{-# OPTIONS_GHC -F -pgmF=horn-preprocessor #-}
module TicTacToe where

elem x (x:_)
elem x (_:xs) :- elem x xs

-- https://github.com/Kakadu/LogicT-demos/blob/master/TicTacToe.hs
boardSize 3
marksForWin 3

data Mark = X | O
data Location = Loc Int Int
data Entry = Entry Location Mark
data Direction = N | NE | E | SE | S | SW | W | NW

direction N S
direction NE SW
direction E W
direction SE NW

move N  (Loc x y) (Loc x  y') :- succ y y'
move NE (Loc x y) (Loc x' y') :- succ x x', succ y y'
move E  (Loc x y) (Loc x' y)  :- succ x x'
move SE (Loc x y) (Loc x' y') :- succ x x', succ y' y
move S  (Loc x y) (Loc x  y') :- succ y' y
move SW (Loc x y) (Loc x' y') :- succ x' x, succ y' y
move W  (Loc x y) (Loc x' y)  :- succ x' x
move NW (Loc x y) (Loc x' y') :- succ x' x, succ y y'

location (Loc x y) :-
  boardSize n
  x >= 0, y >= 0, x < n, y < n

loop board dir m n loc loc' rn rloc :-
  if location loc'
     elem (Entry loc' m) board
  then succ n n'
       move dir loc' loc''
       loop board dir m n' loc' loc'' rn rloc
  else rn = n
       rloc = loc

extendLocation board dir m loc = loop board dir m 0 loc loc' :- move dir loc loc'

cluster board m loc dir1 dir2 n end :-
  extendLocation board dir1 m loc n1 end
  extendLocation board dir2 m loc n2 _
  plus n1 n2 n', succ n' n
