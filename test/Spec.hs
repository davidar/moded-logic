{-# LANGUAGE QuasiQuotes, OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-type-defaults #-}

import Control.Monad.Logic.Moded.Prelude
import Append
import Euler
import HigherOrder
import Kiselyov
import Primes
import Queens
import Sort

import Control.Applicative ((<|>))
import Control.Monad (forM_, when)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Logic (observeMany, observeManyT, observeAll, observeAllT)
import qualified Control.Monad.Logic.Fair as FairLogic
import Control.Monad.Logic.Moded.AST (Prog, Var)
import Control.Monad.Logic.Moded.Codegen (compile)
import Control.Monad.Logic.Moded.Parse (logic)
import qualified Data.List as List
import qualified Data.Text.IO as TIO
import Test.Hspec (describe, hspec, it)
import Test.Hspec.Expectations.Pretty (shouldBe, shouldReturn)

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

  succs xs ys :- (p x y :- succ x y), map p xs ys.

  filter p [] [].
  filter p (h:t) ts :-
    if p h
    then filter p t t', ts = (h:t')
    else filter p t ts.

  evens xs ys :- (p x :- even x), filter p xs ys.

  foldl p [] a a.
  foldl p (h:t) a a'' :- p h a a', foldl p t a' a''.

  sum xs z r :- (p x a a' :- plus x a a'), foldl p xs z r.
  split xs z r :- (p x a a' :- a = (x:a')), foldl p xs z r.
  splitr xs z r :- (p x a a' :- a' = (x:a)), foldl p xs z r.
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
  triang n r :- succ n n', times n n' nn', div nn' 2 r.

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

  even x :- mod x 2 0.

  elem x (x:_).
  elem x (_:xs) :- elem x xs.

  span p [] [] [].
  span p (x:xs) ys zs :-
    if p x
    then span p xs yt zs, ys = (x:yt)
    else ys = [], zs = (x:xs).

  multiple x y :- mod x y 0.

  #pragma nub euler1.
  euler1 x :- elem x [0..999], multiple x y, (y = 3; y = 5).

  euler1' s :- (p x :- euler1 x), observeAll p r, sum r s.

  #pragma memo fib.
  fib 0 0.
  fib 1 1.
  fib k fk :- k > 1, succ i j, succ j k, fib i fi, fib j fj, plus fi fj fk.

  fib' f :- nat i, fib i f.

  euler2 s :-
    (p x :- fib' x, even x), observeAll p fs,
    (q x :- x < 1000000), span q fs xs _, sum xs s.

  nontrivialDivisor n d :- succ n' n, elem d [2..n'], mod n d 0.

  prime n :- nat n, n > 1, if nontrivialDivisor n _ then empty else.

  euler3 r :-
    (p x :- nontrivialDivisor 42 x, prime x),
    observeAll p fs, maximum fs r.
  |]

prime25 :: [Integer]
prime25 =
  [ 2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41
  , 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97 ]

main :: IO ()
main = do
  putStrLn . unlines $
    map show [programAppend, programHigherOrder, programPrimes, programSort, programQueens, programCrypt, programKiselyov, programEuler]
  hspec $ do
    describe "Append" $ do
      it "compile" $ do
        let code = compile "Append" programAppend
        when updateCode $ TIO.writeFile "test/Append.hs" code
        expect <- TIO.readFile "test/Append.hs"
        code `shouldBe` expect
      it "append" $ do
        observeAll (append_iio [1 .. 3] [4 .. 6]) `shouldBe` [[1 .. 6]]
        observeAll (append_iii [1 .. 3] [4 .. 6] [1 .. 6]) `shouldBe` [()]
        observeAll (append_iii [1 .. 3] [4 .. 6] [0 .. 6]) `shouldBe` []
        observeAll (append_ooi [1 .. 6]) `shouldBe`
          [splitAt i [1 .. 6] | i <- [0 .. 6]]
        observeAll (append_ioi [1 .. 3] [1 .. 6]) `shouldBe` [[4 .. 6]]
        observeAll (append_oii [4 .. 6] [1 .. 6]) `shouldBe` [[1 .. 3]]
      it "append3" $ do
        observeAll (append3_iiio [1, 2] [3, 4] [5, 6]) `shouldBe` [[1 .. 6]]
        observeAll (append3_iiii [1, 2] [3, 4] [5, 6] [1 .. 6]) `shouldBe` [()]
        observeAll (append3_iiii [1, 2] [3, 4] [5, 6] [0 .. 6]) `shouldBe` []
        ((List.sort . observeAll $ append3_oooi [1 .. 6]) `shouldBe`) .
          List.sort $ do
          i <- [0 .. 6]
          let (a, bc) = splitAt i [1 .. 6]
          j <- [0 .. length bc]
          let (b, c) = splitAt j bc
          pure (a, b, c)
      it "reverse" $ do
        observeAll (reverse_oi [0 .. 9]) `shouldBe` [[9,8 .. 0]]
        observeAll (reverse_io [0 .. 9]) `shouldBe` [[9,8 .. 0]]
        observeAll (reverse_ii [0 .. 9] [9,8 .. 0]) `shouldBe` [()]
        observeAll (reverse_ii [0 .. 9] [9,8 .. 1]) `shouldBe` []
      it "palindrome" $ do
        observeAll (palindrome_i [1, 2, 3, 2, 1]) `shouldBe` [()]
        observeAll (palindrome_i [1, 2, 3, 4, 5]) `shouldBe` []
      it "duplicate" $ do
        observeAll (duplicate_oi [0, 1, 0, 1]) `shouldBe` [[0, 1]]
        observeAll (duplicate_oi [0, 1, 2, 3]) `shouldBe` []
      it "classify" $ do
        observeAll (classify_io [1, 2, 3, 2, 1]) `shouldBe` [Just []]
        observeAll (classify_io [1, 2, 1, 2]) `shouldBe` [Just [1, 2]]
        observeAll (classify_io [1, 2, 3]) `shouldBe` [Nothing]
      it "perm" $ do
        List.sort (observeAll (perm_io [1 .. 5])) `shouldBe`
          List.sort (List.permutations [1 .. 5])
        List.sort (observeAll (perm_oi [1 .. 5])) `shouldBe`
          List.sort (List.permutations [1 .. 5])
        observeAll (perm_ii [1, 5, 3, 2, 4] [4, 2, 5, 1, 3]) `shouldBe` [()]
        observeAll (perm_ii [1, 5, 3, 2, 4] [4, 2, 5, 5, 3]) `shouldBe` []
    describe "HigherOrder" $ do
      it "compile" $ do
        let code = compile "HigherOrder" programHigherOrder
        when updateCode $ TIO.writeFile "test/HigherOrder.hs" code
        expect <- TIO.readFile "test/HigherOrder.hs"
        code `shouldBe` expect
      it "map" $ do
        observeAll (map_p2ioio succ_io [0 .. 9]) `shouldBe` [[1 .. 10]]
        observeAll (map_p2oioi succ_oi [1 .. 10]) `shouldBe` [[0 .. 9]]
        observeAll (succs_io [0 .. 9]) `shouldBe` [[1 .. 10]]
        observeAll (succs_oi [1 .. 10]) `shouldBe` [[0 .. 9]]
      it "filter" $ do
        observeAll (evens_io [1..9]) `shouldBe` [[2,4,6,8]]
      it "foldl" $ do
        observeAll (sum_iio [1..9] 0) `shouldBe` [sum [1..9]]
        observeAll (sum_ioi [1..9] 999) `shouldBe` [999 - sum [1..9]]
        observeAll (split_oio [1..9]) `shouldBe` [splitAt i [1..9] | i <- [0..9]]
        observeMany 10 (splitr_ooi [1..9]) `shouldBe`
          [let (a, b) = splitAt i [1..9] in (reverse a, b) | i <- [0..9]]
    describe "Primes" $ do
      it "compile" $ do
        let code = compile "Primes" programPrimes
        when updateCode $ TIO.writeFile "test/Primes.hs" code
        expect <- TIO.readFile "test/Primes.hs"
        code `shouldBe` expect
      it "primes" $ do
        observeAll (primes_io 100) `shouldBe` [prime25]
        observeAll (primes_ii 100 prime25) `shouldBe` [()]
        observeAll (primes_ii 100 [2 .. 99]) `shouldBe` []
    describe "Sort" $ do
      it "compile" $ do
        let code = compile "Sort" programSort
        when updateCode $ TIO.writeFile "test/Sort.hs" code
        expect <- TIO.readFile "test/Sort.hs"
        code `shouldBe` expect
      it "sort" $ do
        let xs = [27,74,17,33,94,18,46,83,65,2,32,53,28,85,99,47,28,82,6,11,55,29,39,81,
                  90,37,10,0,66,51,7,21,85,27,31,63,75,4,95,99,11,28,61,74,18,92,40,53,59,8]
        observeAll (sort_io xs) `shouldBe` [List.sort xs]
        observeAll (sort_ii xs (List.sort xs)) `shouldBe` [()]
        observeAll (sort_ii xs xs) `shouldBe` []
    describe "Queens" $ do
      it "compile" $ do
        let code = compile "Queens" programQueens
        when updateCode $ TIO.writeFile "test/Queens.hs" code
        expect <- TIO.readFile "test/Queens.hs"
        code `shouldBe` expect
      it "queens1" $ do
        observeAll (queens1_io [1 .. 4]) `shouldBe` [[2, 4, 1, 3], [3, 1, 4, 2]]
      it "queens2" $ do
        observeAll (queens2_io [1 .. 4]) `shouldBe` [[2, 4, 1, 3], [3, 1, 4, 2]]
      forM_ [1 .. 6] $ \n ->
        it ("n=" ++ show n) $
        observeAll (queens1_io [1 .. n]) `shouldBe`
        observeAll (queens2_io [1 .. n])
    describe "Kiselyov" $ do
      it "compile" $ do
        let code = compile "Kiselyov" programKiselyov
        when updateCode $ TIO.writeFile "test/Kiselyov.hs" code
        expect <- TIO.readFile "test/Kiselyov.hs"
        code `shouldBe` expect
      it "pythag" $ do
        take 7 (FairLogic.observeAll pythag_ooo) `shouldBe`
          [(3,4,5),(6,8,10),(5,12,13),(9,12,15),(8,15,17),(12,16,20),(7,24,25)]
      it "ptriang" $ do
        observeAll ptriang_o `shouldBe`
          [3,6,8,10,11,13,15,16,18,20,21,23,26,27,28]
      it "stepN" $ do
        observeAll (stepN_io 99) `shouldBe` [0..99]
      it "oddsTest" $ do
        head (FairLogic.observeAll oddsTest_o) `shouldBe` 10
      it "oddsPlusTest" $ do
        head (FairLogic.observeAll oddsPlusTest_o) `shouldBe` 2
      it "oddsPrime" $ do
        let expect = [3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
        observeMany 10 oddsPrime_o `shouldBe` expect
        observeManyT 10 oddsPrimeIO_o `shouldReturn` expect
      it "bogosort" $ do
        observeAll (bogosort_io [5,0,3,4,0,1]) `shouldBe`
          replicate 2 [0,0,1,3,4,5]
        List.sort (observeAll (bogosort_oi [1 .. 5])) `shouldBe`
          List.sort (List.permutations [1 .. 5])
        observeAll (bogosort_oi [1,0]) `shouldBe` []
      it "tcomp" $ do
        observeAll tcomp_ex1_o `shouldBe` [Just 1]
      it "findI" $ do
        observeAll (prefix_io "hello") `shouldBe` List.inits "hello"
        observeAll (suffix_io "hello") `shouldBe` List.tails "hello"
        let sentence = "Store it in the neighboring harbor"
        observeAll (findI_iio "or" sentence) `shouldBe`
          List.findIndices ("or" `List.isPrefixOf`) (List.tails sentence)
        let sentence1 = liftIO (putStrLn "sentence1") >> return sentence
            sentence2 = liftIO (putStrLn "sentence2") >> return "Sort of"
            twosen = liftIO . print =<< findI_iio "or" =<< sentence1 <|> sentence2
        observeAllT twosen `shouldReturn` replicate 4 ()
    describe "Euler" $ do
      it "compile" $ do
        let code = compile "Euler" programEuler
        when updateCode $ TIO.writeFile "test/Euler.hs" code
        expect <- TIO.readFile "test/Euler.hs"
        code `shouldBe` expect
      it "1" $ do
        observeAll euler1'_o `shouldBe` [233168]
      it "2" $ do
        [observeAll (fib_io i) | i <- [0 .. 12 :: Integer]] `shouldBe`
          map pure [0,1,1,2,3,5,8,13,21,34,55,89,144]
        observeAll (fib_io (100 :: Integer)) `shouldBe` [354224848179261915075]
        observeAll euler2_o `shouldBe` [1089154]
      it "3" $ do
        observeMany 25 prime_o `shouldBe` prime25
        observeAll euler3_o `shouldBe` [7]
