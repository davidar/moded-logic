{-# LANGUAGE QuasiQuotes, OverloadedStrings, TypeApplications, DataKinds, ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-type-defaults -Wno-unticked-promoted-constructors #-}

import qualified Append
import qualified Cannibals
import Cannibals (Action(..))
import qualified DCG
import qualified Euler
import qualified HigherOrder
import qualified Kiselyov
import qualified Primes
import qualified Queens
import qualified Sort

import Control.Applicative (Alternative(..))
import Control.Exception (IOException, catch)
import Control.Monad (forM_, guard, when)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Logic (observe, observeMany, observeManyT, observeAll, observeAllT)
import qualified Control.Monad.Stream as Stream
import Control.Monad.Logic.Moded.AST (Prog, Var)
import Control.Monad.Logic.Moded.Codegen (compile)
import Control.Monad.Logic.Moded.Mode (Mode(..))
import Control.Monad.Logic.Moded.Parse (logic, rule)
import qualified Control.Monad.Logic.Moded.Prelude as MPrelude
import Control.Monad.Logic.Moded.Preprocess (combineDefs, superhomogeneous, simp)
import Control.Monad.Logic.Moded.Procedure (call)
import qualified Data.List as List
import Data.Maybe (isJust)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import System.Environment (lookupEnv)
import Test.Hspec (describe, hspec, it)
import Test.Hspec.Expectations.Pretty (shouldBe, shouldReturn, shouldSatisfy)
import Text.Megaparsec (parse)

programAppend :: Prog Var Var
programAppend = [logic|
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

id x x
|]

programHigherOrder :: Prog Var Var
programHigherOrder = [logic|
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
|]

programPrimes :: Prog Var Var
programPrimes = [logic|
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
|]

programSort :: Prog Var Var
programSort = [logic|
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
|]

programQueens :: Prog Var Var
programQueens = [logic|
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
|]

programCrypt :: Prog Var Var
programCrypt = [logic|
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
  times a d ad
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
|]

programKiselyov :: Prog Var Var
programKiselyov = [logic|
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

oddsTest x :- (odds x; test x), even x

oddsPlus n x :- odds a, plus a n x

oddsPlusTest x :- (n = 0; n = 1), oddsPlus n x, even x

oddsPrime n :-
  odds n, n > 1, succ n' n
  not (elem d [1..n'], d > 1, mod n d 0)

nontrivialDivisor n d :- succ n' n, elem d [2..n'], mod n d 0

oddsPrimeIO n :-
  odds n, n > 1
  not (nontrivialDivisor n d, print d)

bogosort l p :- permute l p, sorted p

-- http://okmij.org/ftp/continuations/generators.html#logicT
tcomp_ex1 r :-
  if (i = 2; i = 1; i = 3), (j = 0; j = 1), i = j
  then r = Just i else r = Nothing

findI pat str i :-
  suffix str t, prefix t pat
  length t m, length str n, plus i m n
|]

programDCG :: Prog Var Var
programDCG = [logic|
append [] b b
append (h:t) b (h:tb) :- append t b tb

#inline compose
compose f g a z :- g a b, f b z

#data Tree = S Tree Tree | NP String String | VP String Tree

det "the"
det "a"
noun "cat"
noun "bat"
verb "eats"

np (NP d n) = append d . append " " . append n :- det d, noun n
vp (VP v n) = append v . append " " . np n :- verb v
sentence (S n v) = np n . append " " . vp v
|]

programEuler :: Prog Var Var
programEuler = [logic|
#type nat Integer
nat 0
nat n' :- nat n, succ n n'

oddNat 1
oddNat n' :- oddNat n, plus n 2 n'

even x :- mod x 2 0

elem x (x:_)
elem x (_:xs) :- elem x xs

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

multiple x y :- mod x y 0

#inline apply
apply f p y :- p x, f x y

#nub euler1
euler1 x :- elem x [0..999], multiple x y, (y = 3; y = 5)

euler1' = sum <$> observeAll euler1

#memo fib
#mode fib In Out
fib 0 0
fib 1 1
fib k fk :- k > 1, succ i j, succ j k, fib i fi, fib j fj, plus fi fj fk

fib' = fib <$> nat

euler2 = sum <$> takeWhile (\x :- x < 1000000) <$> observeAll (\x :- fib' x, even x)

nontrivialDivisor n d :- succ n' n, elem d [2..n'], multiple n d

primeSlow n :- nat n, n > 1, not (nontrivialDivisor n _)

factor n (p:ps) f :-
  if timesInt p p pp, pp > n then f = n
  else if divMod n p d 0 then (f = p; factor d (p:ps) f)
  else factor n ps f

#memo prime
prime 2
prime p :-
  oddNat p, p > 2
  observeAll prime primes
  not (factor p primes d, p /= d)

primeFactor n = factor n <$> observeAll prime

euler3 n = maximum <$> observeAll (primeFactor n)

euler4 n :-
  elem x [10..99], elem y [10..99], timesInt x y n
  show n s, reverse s s

euler4' = maximum <$> observeAll euler4

euler5 n :- nat n, n > 0, all (multiple n) [1..5]
|]

-- https://github.com/Kakadu/LogicT-demos/blob/master/MCPT.hs
programCannibals :: Prog Var Var
programCannibals = [logic|
elem x (x:_)
elem x (_:xs) :- elem x xs

append [] b b
append (h:t) b (h:tb) :- append t b tb

#inline compose
compose f g a z :- g a b, f b z

#data State = State Int Int Int Int Int Int
#data Action = F Int Int | B Int Int
#data Search = Search State [State] [Action]

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
  (m1 = 0; c1 <= m1)
  (m2 = 0; c2 <= m2)

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
|]

-- https://github.com/Kakadu/LogicT-demos/blob/master/TicTacToe.hs
programTicTacToe :: Prog Var Var
programTicTacToe = [logic|
elem x (x:_)
elem x (_:xs) :- elem x xs

boardSize 3
marksForWin 3

#data Mark = X | O
#data Location = Loc Int Int
#data Entry = Entry Location Mark
#data Direction = N | NE | E | SE | S | SW | W | NW

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
|]

prime25 :: [Integer]
prime25 =
  [ 2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41
  , 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97 ]

compileTest :: String -> Prog Var Var -> IO ()
compileTest name program = do
  let code = compile (T.pack name) program
      file = "test/" ++ name ++ ".hs"
  code `shouldSatisfy` (not . T.null)
  updateCode <- isJust <$> lookupEnv "UPDATE_CODE"
  when updateCode $ do
    expect <- TIO.readFile file `catch` \(_ :: IOException) -> return ""
    when (code /= expect) $
      TIO.writeFile file code
  expect <- TIO.readFile file
  code `shouldBe` expect

main :: IO ()
main = do
  putStrLn . unlines $ show <$>
    [ programAppend
    , programHigherOrder
    , programPrimes
    , programSort
    , programQueens
    , programCrypt
    , programKiselyov
    , programDCG
    , programEuler
    , programCannibals
    , programTicTacToe
    ]
  hspec $ do
    describe "Parse" $ do
      it "apply" $ do
        let Right r0 = parse rule "" "result n :- apply sum (observeAll p) n"
            [r1] = combineDefs [r0]
            r2 = superhomogeneous [("sum",2), ("observeAll",2), ("p",1)] r1
            r3 = simp r2
        show r0 `shouldBe` "result n :- (apply sum (observeAll p) n)."
        show r1 `shouldBe` "result n :- (((apply sum (observeAll p) n)))."
        show r2 `shouldBe` "result n :- ((((apply pred0 pred2 n, (pred0 curry1 curry2 :- sum curry1 curry2), (pred2 curry1 :- (observeAll pred1 curry1, (pred1 curry1 :- p curry1)))))))."
        show r3 `shouldBe` "result n :- ((apply pred0 pred2 n, (pred0 curry1 curry2 :- sum curry1 curry2), (pred2 curry1 :- (observeAll pred1 curry1, (pred1 curry1 :- p curry1)))))."
    describe "Append" $ do
      it "compile" $ compileTest "Append" programAppend
      it "append" $ do
        observeAll (call @'[In, In, Out] Append.append [1 .. 3] [4 .. 6]) `shouldBe` [[1 .. 6]]
        observeAll (call @'[In, In, In] Append.append [1 .. 3] [4 .. 6] [1 .. 6]) `shouldBe` guard True
        observeAll (call @'[In, In, In] Append.append [1 .. 3] [4 .. 6] [0 .. 6]) `shouldBe` guard False
        observeAll (call @'[Out, Out, In] Append.append [1 .. 6]) `shouldBe`
          [splitAt i [1 .. 6] | i <- [0 .. 6]]
        observeAll (call @'[In, Out, In] Append.append [1 .. 3] [1 .. 6]) `shouldBe` [[4 .. 6]]
        observeAll (call @'[Out, In, In] Append.append [4 .. 6] [1 .. 6]) `shouldBe` [[1 .. 3]]
      it "append3" $ do
        observeAll (call @'[In, In, In, Out] Append.append3 [1, 2] [3, 4] [5, 6]) `shouldBe` [[1 .. 6]]
        observeAll (call @'[In, In, In, In] Append.append3 [1, 2] [3, 4] [5, 6] [1 .. 6]) `shouldBe` guard True
        observeAll (call @'[In, In, In, In] Append.append3 [1, 2] [3, 4] [5, 6] [0 .. 6]) `shouldBe` guard False
        ((List.sort . observeAll $ call @'[Out, Out, Out, In] Append.append3 [1 .. 6]) `shouldBe`) .
          List.sort $ do
          i <- [0 .. 6]
          let (a, bc) = splitAt i [1 .. 6]
          j <- [0 .. length bc]
          let (b, c) = splitAt j bc
          pure (a, b, c)
      it "reverse" $ do
        observeAll (call @'[Out, In] Append.reverse [0 .. 9]) `shouldBe` [[9,8 .. 0]]
        observeAll (call @'[In, Out] Append.reverse [0 .. 9]) `shouldBe` [[9,8 .. 0]]
        observeAll (call @'[In, In] Append.reverse [0 .. 9] [9,8 .. 0]) `shouldBe` guard True
        observeAll (call @'[In, In] Append.reverse [0 .. 9] [9,8 .. 1]) `shouldBe` guard False
      it "palindrome" $ do
        observeAll (call @'[In] Append.palindrome [1, 2, 3, 2, 1]) `shouldBe` guard True
        observeAll (call @'[In] Append.palindrome [1, 2, 3, 4, 5]) `shouldBe` guard False
      it "duplicate" $ do
        observeAll (call @'[Out, In] Append.duplicate [0, 1, 0, 1]) `shouldBe` [[0, 1]]
        observeAll (call @'[Out, In] Append.duplicate [0, 1, 2, 3]) `shouldBe` empty
      it "classify" $ do
        observeAll (call @'[In, Out] Append.classify [1, 2, 3, 2, 1]) `shouldBe` [Just []]
        observeAll (call @'[In, Out] Append.classify [1, 2, 1, 2]) `shouldBe` [Just [1, 2]]
        observeAll (call @'[In, Out] Append.classify [1, 2, 3]) `shouldBe` [Nothing]
      it "perm" $ do
        List.sort (observeAll (call @'[In, Out] Append.perm [1 .. 5])) `shouldBe`
          List.sort (List.permutations [1 .. 5])
        List.sort (observeAll (call @'[Out, In] Append.perm [1 .. 5])) `shouldBe`
          List.sort (List.permutations [1 .. 5])
        observeAll (call @'[In, In] Append.perm [1, 5, 3, 2, 4] [4, 2, 5, 1, 3]) `shouldBe` guard True
        observeAll (call @'[In, In] Append.perm [1, 5, 3, 2, 4] [4, 2, 5, 5, 3]) `shouldBe` guard False
      it "id" $ do
        observeAll (call @[In, Out] Append.id 7) `shouldBe` [7]
        observeAll (call @[In, In] Append.id 7 7) `shouldBe` guard True
        observeAll (call @[In, In] Append.id 7 8) `shouldBe` guard False
    describe "HigherOrder" $ do
      it "compile" $ compileTest "HigherOrder" programHigherOrder
      it "map" $ do
        observeAll (call @'[PredMode '[In, Out], In, Out] HigherOrder.map MPrelude.succ [0 .. 9]) `shouldBe` [[1 .. 10]]
        observeAll (call @'[PredMode '[Out, In], Out, In] HigherOrder.map MPrelude.succ [1 .. 10]) `shouldBe` [[0 .. 9]]
        observeAll (call @'[In, Out] HigherOrder.succs [0 .. 9]) `shouldBe` [[1 .. 10]]
        observeAll (call @'[Out, In] HigherOrder.succs [1 .. 10]) `shouldBe` [[0 .. 9]]
      it "filter" $ do
        observeAll (call @'[In, Out] HigherOrder.evens [1..9]) `shouldBe` [[2,4,6,8]]
      it "foldl" $ do
        observeAll (call @'[In, In, Out] HigherOrder.sum [1..9] 0) `shouldBe` [sum [1..9]]
        observeAll (call @'[In, Out, In] HigherOrder.sum [1..9] 999) `shouldBe` [999 - sum [1..9]]
        observeAll (call @'[Out, In, Out] HigherOrder.split [1..9]) `shouldBe` [splitAt i [1..9] | i <- [0..9]]
        observeMany 10 (call @'[Out, Out, In] HigherOrder.splitr [1..9]) `shouldBe`
          [let (a, b) = splitAt i [1..9] in (reverse a, b) | i <- [0..9]]
      it "closure" $ do
        observeAll (call @'[In, Out] HigherOrder.smaller 1) `shouldBe` [2]
        observeAll (call @'[In, Out] HigherOrder.smallerTransitive 1) `shouldBe` [2, 3]
        observeAll (call @'[In, In] HigherOrder.smallerTransitive 1 3) `shouldBe` guard True
      it "compose" $ do
        observeAll (call @'[In, Out] HigherOrder.composeTest 7) `shouldBe` [2 * (1 + 7)]
        observeAll (call @'[Out, In] HigherOrder.composeTest (2 * (1 + 7))) `shouldBe` [7]
      it "inline" $ do
        observeAll (call @'[Out] HigherOrder.inlineTest) `shouldBe` [7]
    describe "Primes" $ do
      it "compile" $ compileTest "Primes" programPrimes
      it "primes" $ do
        observeAll (call @'[In, Out] Primes.primes 100) `shouldBe` [prime25]
        observeAll (call @'[In, In] Primes.primes 100 prime25) `shouldBe` guard True
        observeAll (call @'[In, In] Primes.primes 100 [2 .. 99]) `shouldBe` guard False
    describe "Sort" $ do
      it "compile" $ compileTest "Sort" programSort
      it "sort" $ do
        let xs = [27,74,17,33,94,18,46,83,65,2,32,53,28,85,99,47,28,82,6,11,55,29,39,81,
                  90,37,10,0,66,51,7,21,85,27,31,63,75,4,95,99,11,28,61,74,18,92,40,53,59,8]
        observeAll (call @'[In, Out] Sort.sort xs) `shouldBe` [List.sort xs]
        observeAll (call @'[In, In] Sort.sort xs (List.sort xs)) `shouldBe` guard True
        observeAll (call @'[In, In] Sort.sort xs xs) `shouldBe` guard False
    describe "Queens" $ do
      it "compile" $ compileTest "Queens" programQueens
      it "queens1" $ do
        observeAll (call @'[In, Out] Queens.queens1 [1 .. 4]) `shouldBe` [[2, 4, 1, 3], [3, 1, 4, 2]]
      it "queens2" $ do
        observeAll (call @'[In, Out] Queens.queens2 [1 .. 4]) `shouldBe` [[2, 4, 1, 3], [3, 1, 4, 2]]
      forM_ [1 .. 6] $ \n ->
        it ("n=" ++ show n) $
        observeAll (call @'[In, Out] Queens.queens1 [1 .. n]) `shouldBe`
        observeAll (call @'[In, Out] Queens.queens2 [1 .. n])
    describe "Kiselyov" $ do
      it "compile" $ compileTest "Kiselyov" programKiselyov
      it "elem" $ do
        observeAll (call @'[In, In] Kiselyov.elem 2 [1,2,3]) `shouldBe` guard True
      it "pythag" $ do
        Stream.observeMany 7 (call @'[Out, Out, Out] Kiselyov.pythag) `shouldBe`
          [(3,4,5),(6,8,10),(5,12,13),(9,12,15),(8,15,17),(12,16,20),(7,24,25)]
      it "ptriang" $ do
        observeAll (call @'[Out] Kiselyov.ptriang) `shouldBe`
          [3,6,8,10,11,13,15,16,18,20,21,23,26,27,28]
      it "stepN" $ do
        observeAll (call @'[In, Out] Kiselyov.stepN 99) `shouldBe` [0..99]
      it "oddsTest" $ do
        Stream.observe (call @'[Out] Kiselyov.oddsTest) `shouldBe` 10
      it "oddsPlusTest" $ do
        Stream.observe (call @'[Out] Kiselyov.oddsPlusTest) `shouldBe` 2
      it "oddsPrime" $ do
        let expect = [3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
        observeMany 10 (call @'[Out] Kiselyov.oddsPrime) `shouldBe` expect
        observeManyT 10 (call @'[Out] Kiselyov.oddsPrimeIO) `shouldReturn` expect
      it "bogosort" $ do
        observeAll (call @'[In, Out] Kiselyov.bogosort [5,0,3,4,0,1]) `shouldBe`
          replicate 2 [0,0,1,3,4,5]
        observeAll (call @'[In, In] Kiselyov.bogosort [5,0,3,4,0,1] [0,0,1,3,4,5]) `shouldBe`
          guard True
        List.sort (observeAll (call @'[Out, In] Kiselyov.bogosort [1 .. 5])) `shouldBe`
          List.sort (List.permutations [1 .. 5])
        observeAll (call @'[Out, In] Kiselyov.bogosort [1,0]) `shouldBe` empty
      it "tcomp" $ do
        observeAll (call @'[Out] Kiselyov.tcomp_ex1) `shouldBe` [Just 1]
      it "findI" $ do
        observeAll (call @'[In, Out] Kiselyov.prefix "hello") `shouldBe` List.inits "hello"
        observeAll (call @'[In, Out] Kiselyov.suffix "hello") `shouldBe` List.tails "hello"
        let sentence = "Store it in the neighboring harbor"
        observeAll (call @'[In, In, Out] Kiselyov.findI "or" sentence) `shouldBe`
          List.findIndices ("or" `List.isPrefixOf`) (List.tails sentence)
        let sentence1 = liftIO (putStrLn "sentence1") >> return sentence
            sentence2 = liftIO (putStrLn "sentence2") >> return "Sort of"
            twosen = liftIO . print =<< call @'[In, In, Out] Kiselyov.findI "or" =<< sentence1 <|> sentence2
        observeAllT twosen `shouldReturn` replicate 4 ()
    describe "DCG" $ do
      it "compile" $ compileTest "DCG" programDCG
      it "sentence" $ do
        let dets = ["a", "the"]
            nouns = ["bat", "cat"]
            sent = "the bat eats a cat"
            tree = DCG.S (DCG.NP "the" "bat") (DCG.VP "eats" (DCG.NP "a" "cat"))
        List.sort (snd <$> observeAll (call @'[Out, In, Out] DCG.sentence [])) `shouldBe`
          [unwords [d, n, "eats", d', n'] | d <- dets, n <- nouns, d' <- dets, n' <- nouns]
        observeAll (call @'[Out, In, In] DCG.sentence [] sent) `shouldBe` [tree]
        observeAll (call @'[In, In, Out] DCG.sentence tree []) `shouldBe` [sent]
    describe "Euler" $ do
      it "compile" $ compileTest "Euler" programEuler
      it "1" $ do
        observeAll (call @'[Out] Euler.euler1') `shouldBe` [233168]
      it "2" $ do
        [observeAll (call @'[In, Out] Euler.fib i) | i <- [0 .. 12 :: Integer]] `shouldBe`
          map pure [0,1,1,2,3,5,8,13,21,34,55,89,144]
        observeAll (call @'[In, Out] Euler.fib (100 :: Integer)) `shouldBe` [354224848179261915075]
        observeAll (call @'[Out] Euler.euler2) `shouldBe` [1089154]
      it "3" $ do
        observeMany 25 (call @'[Out] Euler.prime) `shouldBe` prime25
        observeMany 25 (call @'[Out] Euler.primeSlow) `shouldBe` prime25
        observeAll (call @'[In, Out] Euler.euler3 600851475143) `shouldBe` [6857]
      it "4" $ do
        observeAll (call @'[In, Out] Euler.reverse "hello") `shouldBe` ["olleh"]
        -- observeAll (call @'[Out, In] Euler.reverse "hello") `shouldBe` ["olleh"]
        observeAll (call @'[Out] Euler.euler4') `shouldBe` [9009]
      it "5" $ do
        observe (call @'[Out] Euler.euler5) `shouldBe` 60
    describe "Cannibals" $ do
      it "compile" $ compileTest "Cannibals" programCannibals
      it "solve" $ do
        let s = Cannibals.State 3 3 1 0 0 0
            start = Cannibals.Search s [s] []
            actions (Cannibals.Search _ _ a) = a
            expect =
              [[F 1 1,B 1 0,F 0 2,B 0 1,F 2 0,B 1 1,F 2 0,B 0 1,F 0 2,B 0 1,F 0 2]
              ,[F 0 2,B 0 1,F 0 2,B 0 1,F 2 0,B 1 1,F 2 0,B 0 1,F 0 2,B 0 1,F 0 2]
              ,[F 1 1,B 1 0,F 0 2,B 0 1,F 2 0,B 1 1,F 2 0,B 0 1,F 0 2,B 1 0,F 1 1]
              ,[F 0 2,B 0 1,F 0 2,B 0 1,F 2 0,B 1 1,F 2 0,B 0 1,F 0 2,B 1 0,F 1 1]]
        observeAllT (actions <$> call @'[In, Out] Cannibals.solve start) `shouldReturn` expect
    describe "TicTacToe" $ do
      it "compile" $ compileTest "TicTacToe" programTicTacToe
