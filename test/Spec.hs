{-#LANGUAGE QuasiQuotes #-}
import Control.Monad
import Control.Monad.Logic
import Control.Monad.Logic.Moded
import Data.Either
import qualified Data.List as List
import Data.Monoid
import qualified Data.Set as Set
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Test.Hspec (hspec, describe, it)
import Test.Hspec.Expectations.Pretty
import NeatInterpolation
import Append
import Control.Monad.Logic.Parse
import Text.Megaparsec
import System.IO

main :: IO ()
main = do
    lp <- readFile "test/Append.lp"
    let program = parseProg "test/Append.lp" lp
    --putStrLn . unlines $ show <$> program
    hspec $ do
      describe "append" $ do
        it "compile" $ do
            let code = T.pack "module Append where\n" <> compile program
            --TIO.writeFile "test/Append.hs" code
            expect <- TIO.readFile "test/Append.hs"
            code `shouldBe` expect
        it "iio" $ do
            observeAll (append_iio [1..3] [4..6]) `shouldBe` [[1..6]]
        it "ooi" $ do
            observeAll (append_ooi [1..6]) `shouldBe` [splitAt i [1..6] | i <- [0..6]]
        it "iiio" $ do
            observeAll (append_iiio [1,2] [3,4] [5,6]) `shouldBe` [[1..6]]
        it "iiii" $ do
            observeAll (append_iiii [1,2] [3,4] [5,6] [1..6]) `shouldBe` [()]
            observeAll (append_iiii [1,2] [3,4] [5,6] [0..6]) `shouldBe` []
        it "oooi" $ do
            ((List.sort . observeAll $ append_oooi [1..6]) `shouldBe`) . List.sort $ do
                i <- [0..6]
                let (a,bc) = splitAt i [1..6]
                j <- [0..length bc]
                let (b,c) = splitAt j bc
                pure (a,b,c)
        {-
        it "reverse" $ do
            observeAll (reverse_oi [0..9]) `shouldBe` [[9,8..0]]
            observeAll (reverse_io [0..9]) `shouldBe` [[9,8..0]]
            observeAll (reverse_ii [0..9] [9,8..0]) `shouldBe` [()]
            observeAll (reverse_ii [0..9] [9,8..1]) `shouldBe` []
        it "palindrome" $ do
            observeAll (palindrome_i [1,2,3,2,1]) `shouldBe` [()]
            observeAll (palindrome_i [1,2,3,4,5]) `shouldBe` []
        it "duplicate" $ do
            observeAll (duplicate_oi [0,1,0,1]) `shouldBe` [[0,1]]
            observeAll (duplicate_oi [0,1,2,3]) `shouldBe` []
        -}
