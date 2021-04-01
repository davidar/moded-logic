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
    lp <- readFile "test/append.lp"
    let program = map superhomogeneous . either (error . errorBundlePretty) id $ parse rules "test/append.lp" lp
    --putStrLn . unlines $ show <$> program
    hspec $ do
      describe "append" $ do
        it "constraints" $ do
            expect <- T.strip <$> TIO.readFile "test/append.constraints"
            (`shouldBe` expect) $
                T.unwords . map (T.pack . show) . Set.elems $ cComp [] [] (program !! 0)
        it "compile" $ do
            let code = T.strip $ T.pack "module Append where\n" <> compile program
            --TIO.putStrLn code
            expect <- T.strip <$> TIO.readFile "test/Append.hs"
            code `shouldBe` expect
        it "iio" $ do
            observeAll (append_iio [1..3] [4..6]) `shouldBe` [[1..6]]
        it "ooi" $ do
            observeAll (append_ooi [1..6]) `shouldBe` [splitAt i [1..6] | i <- [0..6]]
        it "iiio" $ do
            observeAll (append_iiio [1,2] [3,4] [5,6]) `shouldBe` [[1..6]]
        it "oooi" $ do
            ((List.sort . observeAll $ append_oooi [1..6]) `shouldBe`) . List.sort $ do
                i <- [0..6]
                let (a,bc) = splitAt i [1..6]
                j <- [0..length bc]
                let (b,c) = splitAt j bc
                pure (a,b,c)
        it "reverse" $ do
            observeAll (reverse_oi [0..9]) `shouldBe` [[9,8..0]]
            observeAll (reverse_io [0..9]) `shouldBe` [[9,8..0]]
            observeAll (reverse_ii [0..9] [9,8..0]) `shouldBe` [()]
            observeAll (reverse_ii [0..9] [9,8..1]) `shouldBe` []
