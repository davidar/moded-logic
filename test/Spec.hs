{-#LANGUAGE QuasiQuotes #-}
import Lib
import Control.Monad
import qualified Data.List as List
import qualified Picologic
import qualified Data.Set as Set
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Test.Hspec
import NeatInterpolation

appendRule = Rule "append" ["a", "b", "c"]
    [[ Func "[]" [] "a"
     , Unif "b" "c"
     ]
    ,[ Func ":" ["ah", "at"] "a"
     , Func ":" ["ch", "ct"] "c"
     , Unif "ah" "ch"
     , Pred "append" ["at", "b", "ct"]
     ]
    ]

main :: IO ()
main = hspec $ do
    describe "append" $ do
        it "cComp" $ do
            expect <- T.strip <$> TIO.readFile "test/append.constraints"
            (`shouldBe` expect) $
                T.unwords . map (T.pack . show) . Set.elems $ cComp [] appendRule
        it "cgRule" $ do
            expect <- T.strip <$> TIO.readFile "test/append.hs"
            solns <- solveConstraints appendRule
            (`shouldBe` expect) . T.strip . T.unlines $
                map (\soln -> cgRule $ mode soln appendRule) (Set.elems solns)
