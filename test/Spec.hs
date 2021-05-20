{-# LANGUAGE QuasiQuotes, OverloadedStrings, TypeApplications, DataKinds, ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-type-defaults -Wno-unticked-promoted-constructors #-}

import qualified Append
import qualified Cannibals
import Cannibals (Action(..))
import qualified Crypt
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
import qualified Control.Monad.Logic as Logic
import Control.Monad.Logic.Moded.Mode (Mode(..))
import Control.Monad.Logic.Moded.Optimise (simp)
import Control.Monad.Logic.Moded.Procedure (call)
import Control.Monad.State (evalStateT)
import qualified Control.Monad.Stream as Stream
import Control.Monad.Stream (observe, observeMany, observeManyT, observeAll, observeAllT)
import qualified Data.List as List
import Data.Maybe (isJust)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Language.Horn.Codegen (compile)
import Language.Horn.Parse (parseProg, rule)
import qualified Language.Horn.Prelude as HornPrelude
import Language.Horn.Preprocess (combineDefs, superhomogeneous)
import System.Environment (lookupEnv)
import Test.Hspec (describe, hspec, it)
import Test.Hspec.Expectations.Pretty (shouldBe, shouldReturn, shouldSatisfy)
import Text.Megaparsec (errorBundlePretty, parse)

prime25 :: [Integer]
prime25 =
  [ 2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41
  , 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97 ]

compileTest :: String -> IO ()
compileTest name = do
  src <- TIO.readFile $ "examples/" ++ name ++ ".hn"
  let program = either (error . errorBundlePretty) id $ parseProg "" src
  print program
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
  hspec $ do
    describe "Parse" $ do
      it "apply" $ do
        let Right r0 = parse (evalStateT rule 0) "" "result n :- apply sum (observeAll p) n"
            [r1] = combineDefs [r0]
            r2 = superhomogeneous [("sum",2), ("observeAll",2), ("p",1)] r1
            r3 = simp r2
        show r0 `shouldBe` "result n :- (apply sum (observeAll p) n)."
        show r1 `shouldBe` "result n :- (((apply sum (observeAll p) n)))."
        show r2 `shouldBe` "result n :- ((((apply pred0 pred2 n, (pred0 curry1 curry2 :- sum curry1 curry2), (pred2 curry1 :- (observeAll pred1 curry1, (pred1 curry1 :- p curry1)))))))."
        show r3 `shouldBe` "result n :- ((apply pred0 pred2 n, (pred0 curry1 curry2 :- sum curry1 curry2), (pred2 curry1 :- (observeAll pred1 curry1, (pred1 curry1 :- p curry1)))))."
    describe "Append" $ do
      it "compile" $ compileTest "Append"
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
      it "last" $ do
        observeAll (call @'[In, Out] Append.last [1 .. 5]) `shouldBe` [5]
        observeAll (call @'[In, Out] Append.last []) `shouldBe` (empty :: [()])
      it "id" $ do
        observeAll (call @[In, Out] Append.id 7) `shouldBe` [7]
        observeAll (call @[In, In] Append.id 7 7) `shouldBe` guard True
        observeAll (call @[In, In] Append.id 7 8) `shouldBe` guard False
    describe "HigherOrder" $ do
      it "compile" $ compileTest "HigherOrder"
      it "map" $ do
        observeAll (call @'[PredMode '[In, Out], In, Out] HigherOrder.map HornPrelude.succ [0 .. 9]) `shouldBe` [[1 .. 10]]
        observeAll (call @'[PredMode '[Out, In], Out, In] HigherOrder.map HornPrelude.succ [1 .. 10]) `shouldBe` [[0 .. 9]]
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
      it "compile" $ compileTest "Primes"
      it "primes" $ do
        observeAll (call @'[In, Out] Primes.primes 100) `shouldBe` [prime25]
        observeAll (call @'[In, In] Primes.primes 100 prime25) `shouldBe` guard True
        observeAll (call @'[In, In] Primes.primes 100 [2 .. 99]) `shouldBe` guard False
    describe "Sort" $ do
      it "compile" $ compileTest "Sort"
      it "sort" $ do
        let xs = [27,74,17,33,94,18,46,83,65,2,32,53,28,85,99,47,28,82,6,11,55,29,39,81,
                  90,37,10,0,66,51,7,21,85,27,31,63,75,4,95,99,11,28,61,74,18,92,40,53,59,8]
        observeAll (call @'[In, Out] Sort.sort xs) `shouldBe` [List.sort xs]
        observeAll (call @'[In, In] Sort.sort xs (List.sort xs)) `shouldBe` guard True
        observeAll (call @'[In, In] Sort.sort xs xs) `shouldBe` guard False
    describe "Queens" $ do
      it "compile" $ compileTest "Queens"
      it "queens1" $ do
        observeAll (call @'[In, Out] Queens.queens1 [1 .. 4]) `shouldBe` [[2, 4, 1, 3], [3, 1, 4, 2]]
      it "queens2" $ do
        List.sort (observeAll (call @'[In, Out] Queens.queens2 [1 .. 4])) `shouldBe` [[2, 4, 1, 3], [3, 1, 4, 2]]
      forM_ [1 .. 6] $ \n ->
        it ("n=" ++ show n) $
        List.sort (observeAll (call @'[In, Out] Queens.queens1 [1 .. n])) `shouldBe`
        List.sort (observeAll (call @'[In, Out] Queens.queens2 [1 .. n]))
    describe "Crypt" $ do
      it "compile" $ compileTest "Crypt"
      it "crypt" $ do
        observeAll (call @'[Out] Crypt.crypt) `shouldBe` pure
          [   3,4,8 --    OEE
          ,     2,8 --   * EE
                    --   ----
          , 2,7,8,4 --   EOEE
          , 6,9,6   -- + EOE
                    --   ----
          , 9,7,4,4 --   OOEE
          ]
        348 * 28 `shouldBe` 2784 + 6960
        2784 + 6960 `shouldBe` 9744
    describe "Kiselyov" $ do
      it "compile" $ compileTest "Kiselyov"
      it "elem" $ do
        observeAll (call @'[In, In] Kiselyov.elem 2 [1,2,3]) `shouldBe` guard True
      it "pythag" $ do
        Stream.observeMany 7 (call @'[Out, Out, Out] Kiselyov.pythag) `shouldBe`
          [(3,4,5),(6,8,10),(5,12,13),(9,12,15),(8,15,17),(12,16,20),(7,24,25)]
      it "ptriang" $ do
        observeAll (call @'[Out] Kiselyov.ptriang) `shouldBe`
          [3,6,8,10,11,13,15,16,18,20,21,23,26,27,28]
      it "stepN" $ do
        Logic.observeAll (call @'[In, Out] Kiselyov.stepN 99) `shouldBe` [0..99]
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
      it "compile" $ compileTest "DCG"
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
      it "compile" $ compileTest "Euler"
      it "1" $ do
        observeAll (call @'[Out] Euler.euler1') `shouldBe` [233168]
      it "2" $ do
        [Logic.observeAll (call @'[In, Out] Euler.fib i) | i <- [0 .. 12 :: Integer]] `shouldBe`
          map pure [0,1,1,2,3,5,8,13,21,34,55,89,144]
        Logic.observeAll (call @'[In, Out] Euler.fib (100 :: Integer)) `shouldBe` [354224848179261915075]
        Logic.observeAll (call @'[Out] Euler.euler2) `shouldBe` [1089154]
      it "3" $ do
        Logic.observeMany 25 (call @'[Out] Euler.prime) `shouldBe` prime25
        Logic.observeMany 25 (call @'[Out] Euler.primeSlow) `shouldBe` prime25
        Logic.observeAll (call @'[In, Out] Euler.euler3 600851475143) `shouldBe` [6857]
      it "4" $ do
        observeAll (call @'[In, Out] Euler.reverse "hello") `shouldBe` ["olleh"]
        -- observeAll (call @'[Out, In] Euler.reverse "hello") `shouldBe` ["olleh"]
        observeAll (call @'[Out] Euler.euler4') `shouldBe` [9009]
      it "5" $ do
        observe (call @'[Out] Euler.euler5) `shouldBe` 60
    describe "Cannibals" $ do
      it "compile" $ compileTest "Cannibals"
      it "solve" $ do
        let s = Cannibals.State 3 3 1 0 0 0
            start = Cannibals.Search s [s] []
            actions (Cannibals.Search _ _ a) = a
            expect =
              [[F 0 2,B 0 1,F 0 2,B 0 1,F 2 0,B 1 1,F 2 0,B 0 1,F 0 2,B 0 1,F 0 2]
              ,[F 0 2,B 0 1,F 0 2,B 0 1,F 2 0,B 1 1,F 2 0,B 0 1,F 0 2,B 1 0,F 1 1]
              ,[F 1 1,B 1 0,F 0 2,B 0 1,F 2 0,B 1 1,F 2 0,B 0 1,F 0 2,B 0 1,F 0 2]
              ,[F 1 1,B 1 0,F 0 2,B 0 1,F 2 0,B 1 1,F 2 0,B 0 1,F 0 2,B 1 0,F 1 1]]
        (List.sort <$> observeAllT (actions <$> call @'[In, Out] Cannibals.solve start)) `shouldReturn` expect
    describe "TicTacToe" $ do
      it "compile" $ compileTest "TicTacToe"
