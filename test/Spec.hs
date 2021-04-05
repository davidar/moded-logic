import Append
import Primes

import Control.Monad.Logic (observeAll)
import Control.Monad.Logic.Moded.Codegen (compile)
import Control.Monad.Logic.Moded.Parse (parseProg)
import qualified Data.List as List
import qualified Data.Set as Set
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import System.IO
import Test.Hspec (describe, hspec, it)
import Test.Hspec.Expectations.Pretty (shouldBe)

main :: IO ()
main = do
  lp <- readFile "test/Append.lp"
  let program = parseProg "test/Append.lp" lp
  lp' <- readFile "test/Primes.lp"
  let program' = parseProg "test/Primes.lp" lp'
  --putStrLn . unlines $ show <$> program
  hspec $ do
    describe "Append" $ do
      it "compile" $ do
        let code = T.pack "module Append where\n" <> compile program
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
    describe "Primes" $ do
      it "compile" $ do
        let code = T.pack "module Primes where\n" <> compile program'
        --TIO.writeFile "test/Primes.hs" code
        expect <- TIO.readFile "test/Primes.hs"
        code `shouldBe` expect
      it "primes" $ do
        let p100 = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97]
        observeAll (primes_io 100) `shouldBe` [p100]
        observeAll (primes_ii 100 p100) `shouldBe` [()]
        observeAll (primes_ii 100 [2 .. 99]) `shouldBe` []
