{-#LANGUAGE QuasiQuotes #-}
import Control.Monad
import Control.Monad.Logic
import Control.Monad.Logic.Moded
import qualified Data.List as List
import Data.Monoid
import qualified Picologic
import qualified Data.Set as Set
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Test.Hspec
import NeatInterpolation
import Append
import Control.Monad.Logic.Parse
import Text.Parsec

main :: IO ()
main = hspec $ do
    describe "append" $ do
        let Right appendRule = parse rule "<stdin>" "append(A,B,C) :- A = [], B = C; A = [AH | AT], C = [CH | CT], AH = CH, append(AT, B, CT)."
        it "cComp" $ do
            expect <- T.strip <$> TIO.readFile "test/append.constraints"
            (`shouldBe` expect) $
                T.unwords . map (T.pack . show) . Set.elems $ cComp [] appendRule
        it "cgRule" $ do
            expect <- T.strip <$> TIO.readFile "test/Append.hs"
            (`shouldBe` expect) . T.strip $
                T.pack "module Append where\n" <> compile [appendRule]
        it "iio" $ do
            observeAll (append_iio [1..3] [4..6]) `shouldBe` [[1..6]]
        it "ooi" $ do
            observeAll (append_ooi [1..6]) `shouldBe` [splitAt i [1..6] | i <- [0..6]]
