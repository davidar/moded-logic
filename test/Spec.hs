{-# LANGUAGE QuasiQuotes, OverloadedStrings, TypeApplications, DataKinds #-}
{-# OPTIONS_GHC -Wno-type-defaults -Wno-unticked-promoted-constructors #-}

import qualified Append
import qualified Euler
import qualified HigherOrder
import qualified Kiselyov
import qualified Primes
import qualified Queens
import qualified Sort

import Control.Applicative (Alternative(..))
import Control.Monad (forM_, guard, when)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Logic (observe, observeMany, observeManyT, observeAll, observeAllT)
import qualified Control.Monad.Logic.Fair as FairLogic
import Control.Monad.Logic.Moded.AST (Prog, Var, Mode(..))
import Control.Monad.Logic.Moded.Codegen (compile)
import Control.Monad.Logic.Moded.Parse (logic)
import qualified Control.Monad.Logic.Moded.Prelude as MPrelude
import Control.Monad.Logic.Moded.Procedure (call)
import qualified Data.List as List
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Test.Hspec (describe, hspec, it)
import Test.Hspec.Expectations.Pretty (shouldBe, shouldReturn, shouldSatisfy)

updateCode :: Bool
updateCode = False

programAppend :: Prog Var Var
programAppend =
  [logic|
  append [] b b.
  append (h:t) b (h:tb) :- append t b tb.

  append3 a b c abc :-
    append a b ab, append ab c abc.

  reverse [] [].
  reverse (h:t) l :- reverse t r, append r [h] l.

  palindrome a :- reverse a a.
  duplicate a b :- append a a b.
  classify xs r :- if palindrome xs then r = Just []
              else if duplicate h xs then r = Just h
              else r = Nothing.

  delete h (h:t) t.
  delete x (h:t) (h:r) :- delete x t r.
  perm [] [].
  perm xs (h:t) :- delete h xs ys, perm ys t.
  |]

programHigherOrder :: Prog Var Var
programHigherOrder =
  [logic|
  even n :- mod n 2 0.

  map p [] [].
  map p (x:xs) (y:ys) :- p x y, map p xs ys.

  succs xs ys :- map (\x y :- succ x y) xs ys.

  filter p [] [].
  filter p (h:t) ts :-
    if p h
    then filter p t t', ts = (h:t')
    else filter p t ts.

  evens xs ys :- filter (\x :- even x) xs ys.

  foldl p [] a a.
  foldl p (h:t) a a'' :- p h a a', foldl p t a' a''.

  sum xs z r :- foldl (\x a a' :- plus x a a') xs z r.
  split xs z r :- foldl (\x a a' :- a = (x:a')) xs z r.
  splitr xs z r :- foldl (\x a a' :- a' = (x:a)) xs z r.
  |]

programPrimes :: Prog Var Var
programPrimes =
  [logic|
  integers low high result :-
    if low <= high
    then succ low m, integers m high rest, result = (low:rest)
    else result = [].

  remove _ [] [].
  remove p (j:js) result :-
    mod j p m,
    remove p js njs,
    if m = 0 then result = njs else result = (j:njs).

  sift [] [].
  sift (p:js) (p:ps) :- remove p js new, sift new ps.

  primes limit ps :- integers 2 limit js, sift js ps.
  |]

programSort :: Prog Var Var
programSort =
  [logic|
  partition [] _ [] [].
  partition (h:t) p lo hi :-
    if h <= p
    then partition t p lo1 hi, lo = (h:lo1)
    else partition t p lo hi1, hi = (h:hi1).

  qsort [] r r.
  qsort (x:xs) r r0 :-
    partition xs x ys zs,
    qsort zs r1 r0,
    qsort ys r (x:r1).

  sort list sorted :- qsort list sorted [].
  |]

programQueens :: Prog Var Var
programQueens =
  [logic|
  qdelete h (h:t) t.
  qdelete x (h:t) (h:r) :- qdelete x t r.
  qperm [] [].
  qperm xs (h:t) :- qdelete h xs ys, qperm ys t.

  nodiag _ _ [].
  nodiag b d (h:t) :-
    plus hmb b h,
    plus bmh h b,
    succ d d1,
    if d = hmb then empty
    else if d = bmh then empty
    else nodiag b d1 t.

  safe [].
  safe (h:t) :- nodiag h 1 t, safe t.

  queens1 dat out :- qperm dat out, safe out.

  cqueens [] _ [].
  cqueens xs history (q:m) :-
    xs = (_:_),
    qdelete q xs r,
    nodiag q 1 history,
    cqueens r (q:history) m.

  queens2 dat out :- cqueens dat [] out.
  |]

programCrypt :: Prog Var Var
programCrypt =
  [logic|
  sumDigits [] [] carry cs :-
    if carry = 0 then cs = [] else cs = [carry].
  sumDigits [] (b:bs) carry (c:cs) :-
    if carry = 0 then c = b, cs = bs else
    plus b carry x,
    divMod x 10 carry' c,
    sumDigits [] bs carry' cs.
  sumDigits (a:as) [] carry (c:cs) :-
    if carry = 0 then c = a, cs = as else
    plus a carry x,
    divMod x 10 carry' c,
    sumDigits [] as carry' cs.
  sumDigits (a:as) (b:bs) carry (c:cs) :-
    sum [a, b, carry] x,
    divMod x 10 carry' c,
    sumDigits as bs carry' cs.

  mulDigits (a:as) d carry (b:bs) :-
    times a d ad,
    plus ad carry x,
    divMod x 10 carry' b,
    mulDigits as d carry' bs.
  mulDigits [] _ carry [c,c'] :-
    divMod carry 10 c' c.

  zeros [].
  zeros (z:zs) :- z = 0, zeros zs.

  oddDigit 1.
  oddDigit 3.
  oddDigit 5.
  oddDigit 7.
  oddDigit 9.

  evenDigit 0.
  evenDigit 2.
  evenDigit 4.
  evenDigit 6.
  evenDigit 8.

  crypt [a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p] :-
    oddDigit a, evenDigit b, evenDigit c,
    evenDigit d, d > 0, evenDigit e,
    mulDigits [c,b,a] e 0 (i:h:g:f:x),
    evenDigit f, f > 0, oddDigit g, evenDigit h, evenDigit i,
    zeros x,
    mulDigits [c,b,a] d 0 (l:k:j:y),
    evenDigit j, j > 0, oddDigit k, evenDigit l,
    zeros y,
    sumDigits [i,h,g,f] [0,l,k,j] 0 (p:o:n:m:z),
    oddDigit m, oddDigit n, evenDigit o, evenDigit p,
    zeros z.
  |]

programKiselyov :: Prog Var Var
programKiselyov =
  [logic|
  nat 0.
  nat n' :- nat n, succ n n'.

  elem x (x:_).
  elem x (_:xs) :- elem x xs.

  insert e l (e:l).
  insert e (h:t) (h:t') :- insert e t t'.

  permute [] [].
  permute (h:t) r :- permute t t', insert h t' r.

  sorted [].
  sorted [_].
  sorted (a:b:r) :- a <= b, sorted (b:r).

  suffix l l.
  suffix (_:t) r :- suffix t r.

  prefix _ [].
  prefix (h:t) (h:t') :- prefix t t'.

  length [] 0.
  length (_:t) n' :- length t n, succ n n'.

  -- http://okmij.org/ftp/Computation/monads.html#fair-bt-stream
  pythag i j k :-
    nat i, i > 0, nat j, j > 0, nat k, k > 0, i < j,
    timesInt i i ii, timesInt j j jj, timesInt k k kk,
    plus ii jj kk.

  -- http://okmij.org/ftp/Haskell/set-monad.html
  triang n r :- succ n n', timesInt n n' nn', div nn' 2 r.

  #pragma nub ptriang.
  ptriang k :-
    elem k [1..30], elem i [1..k], elem j [1..i],
    triang i ti, triang j tj, triang k tk,
    plus ti tj tk.

  #pragma nub stepN.
  stepN 0 0.
  stepN n' r :- n' > 0, succ n n', stepN n i, succ i i', elem r [i,i'].

  -- http://okmij.org/ftp/papers/LogicT.pdf
  test 10.
  test 20.
  test 30.

  odds 1.
  odds n :- odds m, plus 2 m n.

  even n :- mod n 2 0.

  oddsTest x :- (odds x; test x), even x.

  oddsPlus n x :- odds a, plus a n x.

  oddsPlusTest x :- (n = 0; n = 1), oddsPlus n x, even x.

  oddsPrime n :-
    odds n, n > 1, succ n' n,
    if elem d [1..n'], d > 1, mod n d 0 then empty else.

  nontrivialDivisor n d :- succ n' n, elem d [2..n'], mod n d 0.

  oddsPrimeIO n :-
    odds n, n > 1,
    if nontrivialDivisor n d, print d then empty else.

  bogosort l p :- permute l p, sorted p.

  -- http://okmij.org/ftp/continuations/generators.html#logicT
  tcomp_ex1 r :-
    if (i = 2; i = 1; i = 3), (j = 0; j = 1), i = j
    then r = Just i else r = Nothing.

  findI pat str i :-
    suffix str t, prefix t pat,
    length t m, length str n, plus i m n.
  |]

programEuler :: Prog Var Var
programEuler =
  [logic|
  #pragma type nat Integer.
  nat 0.
  nat n' :- nat n, succ n n'.

  oddNat 1.
  oddNat n' :- oddNat n, plus n 2 n'.

  even x :- mod x 2 0.

  elem x (x:_).
  elem x (_:xs) :- elem x xs.

  span p [] [] [].
  span p (x:xs) ys zs :-
    if p x
    then span p xs yt zs, ys = (x:yt)
    else ys = [], zs = (x:xs).

  reverseDL [] xs xs.
  reverseDL (h:t) rest r :- reverseDL t (h:rest) r.
  reverse s r :- reverseDL s [] r.

  all p [].
  all p (h:t) :- if p h then all p t else empty.

  multiple x y :- mod x y 0.

  #pragma nub euler1.
  euler1 x :- elem x [0..999], multiple x y, (y = 3; y = 5).

  euler1' s :- observeAll (\x :- euler1 x) r, sum r s.

  #pragma memo fib.
  fib 0 0.
  fib 1 1.
  fib k fk :- k > 1, succ i j, succ j k, fib i fi, fib j fj, plus fi fj fk.

  fib' f :- nat i, fib i f.

  euler2 s :-
    observeAll (\x :- fib' x, even x) fs,
    span (\x :- x < 1000000) fs xs _, sum xs s.

  nontrivialDivisor n d :- succ n' n, elem d [2..n'], mod n d 0.

  primeSlow n :- nat n, n > 1, if nontrivialDivisor n _ then empty else.

  factor (p:ps) n f :-
    if timesInt p p pp, pp > n then f = n
    else if divMod n p d 0 then (f = p; factor (p:ps) d f)
    else factor ps n f.

  #pragma memo prime.
  prime 2.
  prime p :-
    oddNat p, p > 2,
    observeAll (\x :- prime x) primes,
    if factor primes p d, p /= d then empty else.

  primeFactor n d :-
    observeAll (\x :- prime x) primes, factor primes n d.

  euler3 n r :- observeAll (\d :- primeFactor n d) fs, maximum fs r.

  euler4 n :-
    elem x [10..99], elem y [10..99], timesInt x y n,
    show n s, reverse s s.

  euler4' n :- observeAll (\x :- euler4 x) s, maximum s n.

  euler5 n :- nat n, n > 0, all (\x :- multiple n x) [1..5].
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
  when updateCode $
    TIO.writeFile file code
  expect <- TIO.readFile file
  code `shouldBe` expect

main :: IO ()
main = do
  putStrLn . unlines $
    map show [programAppend, programHigherOrder, programPrimes, programSort, programQueens, programCrypt, programKiselyov, programEuler]
  hspec $ do
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
      it "pythag" $ do
        FairLogic.observeMany 7 (call @'[Out, Out, Out] Kiselyov.pythag) `shouldBe`
          [(3,4,5),(6,8,10),(5,12,13),(9,12,15),(8,15,17),(12,16,20),(7,24,25)]
      it "ptriang" $ do
        observeAll (call @'[Out] Kiselyov.ptriang) `shouldBe`
          [3,6,8,10,11,13,15,16,18,20,21,23,26,27,28]
      it "stepN" $ do
        observeAll (call @'[In, Out] Kiselyov.stepN 99) `shouldBe` [0..99]
      it "oddsTest" $ do
        FairLogic.observe (call @'[Out] Kiselyov.oddsTest) `shouldBe` 10
      it "oddsPlusTest" $ do
        FairLogic.observe (call @'[Out] Kiselyov.oddsPlusTest) `shouldBe` 2
      it "oddsPrime" $ do
        let expect = [3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
        observeMany 10 (call @'[Out] Kiselyov.oddsPrime) `shouldBe` expect
        observeManyT 10 (call @'[Out] Kiselyov.oddsPrimeIO) `shouldReturn` expect
      it "bogosort" $ do
        observeAll (call @'[In, Out] Kiselyov.bogosort [5,0,3,4,0,1]) `shouldBe`
          replicate 2 [0,0,1,3,4,5]
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
