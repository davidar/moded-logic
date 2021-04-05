{-# LANGUAGE QuasiQuotes #-}

import Append
import Primes
import Sort
import Queens

import Control.Monad.Logic (observeAll)
import Control.Monad.Logic.Moded.AST (Prog, Var)
import Control.Monad.Logic.Moded.Codegen (compile)
import Control.Monad.Logic.Moded.Parse (logic)
import qualified Data.List as List
import qualified Data.Set as Set
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Test.Hspec (describe, hspec, it)
import Test.Hspec.Expectations.Pretty (shouldBe)

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

programQueens =
  [logic|
  delete h (h:t) t.
  delete x (h:t) (h:r) :- delete x t r.

  nodiag _ _ [].
  nodiag b d (h:t) :-
    plus hmb b h,
    plus bmh h b,
    succ d d1,
    if d = hmb then empty
    else if d = bmh then empty
    else nodiag b d1 t.

  cqueens [] _ [].
  cqueens xs history (q:m) :-
    xs = (_:_),
    delete q xs r,
    nodiag q 1 history,
    cqueens r (q:history) m.

  queens dat out :- cqueens dat [] out.
  |]

main :: IO ()
main = do
  putStrLn . unlines $ show <$> concat [programAppend, programPrimes, programSort, programQueens]
  hspec $ do
    describe "Append" $ do
      it "compile" $ do
        let code = T.pack "module Append where\n" <> compile programAppend
        --TIO.writeFile "test/Append.hs" code
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
        List.sort (observeAll (perm_io [1 .. 5])) `shouldBe` List.sort (List.permutations [1 .. 5])
        List.sort (observeAll (perm_oi [1 .. 5])) `shouldBe` List.sort (List.permutations [1 .. 5])
        observeAll (perm_ii [1, 5, 3, 2, 4] [4, 2, 5, 1, 3]) `shouldBe` [()]
        observeAll (perm_ii [1, 5, 3, 2, 4] [4, 2, 5, 5, 3]) `shouldBe` []
    describe "Primes" $ do
      it "compile" $ do
        let code = T.pack "module Primes where\n" <> compile programPrimes
        --TIO.writeFile "test/Primes.hs" code
        expect <- TIO.readFile "test/Primes.hs"
        code `shouldBe` expect
      it "primes" $ do
        let p100 = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41,
                    43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97]
        observeAll (primes_io 100) `shouldBe` [p100]
        observeAll (primes_ii 100 p100) `shouldBe` [()]
        observeAll (primes_ii 100 [2 .. 99]) `shouldBe` []
    describe "Sort" $ do
      it "compile" $ do
        let code = T.pack "module Sort where\n" <> compile programSort
        --TIO.writeFile "test/Sort.hs" code
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
        let code = T.pack "module Queens where\n" <> compile programQueens
        --TIO.writeFile "test/Queens.hs" code
        expect <- TIO.readFile "test/Queens.hs"
        code `shouldBe` expect
        print $ observeAll (queens_io [1 .. 5])
