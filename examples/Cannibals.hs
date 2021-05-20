{-# OPTIONS_GHC -F -pgmF=horn-preprocessor #-}
module Cannibals where

elem x (x:_)
elem x (_:xs) :- elem x xs

append [] b b
append (h:t) b (h:tb) :- append t b tb

#inline compose
compose f g a z :- g a b, f b z

-- https://github.com/Kakadu/LogicT-demos/blob/master/MCPT.hs
data State = State Int Int Int Int Int Int
data Action = F Int Int | B Int Int
data Search = Search State [State] [Action]

final (State 0 0 _ _ _ _)

action (F 1 0)
action (F 0 1)
action (F 2 0)
action (F 0 2)
action (F 1 1)
action (B 1 0)
action (B 0 1)
action (B 2 0)
action (B 0 2)
action (B 1 1)

check (State m1 c1 _ m2 c2 _) :-
  m1 >= 0, m2 >= 0, c1 >= 0, c2 >= 0
  (| 0 | (>= c1) |) m1
  (| 0 | (>= c2) |) m2

move (State m1 c1 b1 m2 c2 b2) (F mm cm) s :-
  b1 > 0
  plus mm m1' m1
  plus cm c1' c1
  succ b1' b1
  plus mm m2 m2'
  plus cm c2 c2'
  succ b2 b2'
  s = State m1' c1' b1' m2' c2' b2'
  check s
move (State m1 c1 b1 m2 c2 b2) (B mm cm) s :-
  b2 > 0
  plus mm m1 m1'
  plus cm c1 c1'
  succ b1 b1'
  plus mm m2' m2
  plus cm c2' c2
  succ b2' b2
  s = State m1' c1' b1' m2' c2' b2'
  check s

appendShow x = append s :- show x s

showMove c a s = append "Tentative move: " . appendShow c . append " -" . appendShow a . append "-> " . appendShow s

solve (Search current seen actions) r :-
  action a
  move current a s
  not (elem s seen)
  showMove current a s [] msg
  putStrLn msg
  news = Search s (s:seen) (a:actions)
  if final s then r = news else solve news r
