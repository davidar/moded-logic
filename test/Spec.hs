import Lib
import Control.Monad
import qualified Data.List as List
import qualified Picologic
import qualified Data.Set as Set
import Test.Hspec

rule = Rule "append" ["A", "B", "C"]
    [[Func "[]" [] "A"
     , Unif "B" "C"]
    ,[ Func ":" ["AH", "AT"] "A"
     , Func ":" ["CH", "CT"] "C"
     , Unif "AH" "CH"
     , Pred "append" ["AT", "B", "CT"]
     ]
    ]

main :: IO ()
main = do
    Picologic.Solutions solns <- Picologic.solveProp . foldr1 Picologic.Conj . Set.elems $ cComp [] rule
    forM_ solns $ \soln -> do
        let s = Set.fromList soln
        print s
        print $ mode s rule
    hspec $ do
        describe "cComp" $ do
            it "append" $
                (List.intercalate " " . map show . Set.elems $ cComp [] rule) `shouldBe`
                "AH[1] AH[] AT[1] AT[] CH[1] CH[] CT[1] CT[] ~(AH[1,0] & AH[1,2]) ~(AH[1,2] & CH[1,2]) ~(AT[1,0] & AT[1,3]) ~(A[1,0] & AH[1,0]) ~(B[0,1] & C[0,1]) ~(CH[1,1] & CH[1,2]) ~(CT[1,1] & CT[1,3]) ~(C[1,1] & CH[1,1]) (AH[1,0] <-> AT[1,0]) (AH[1] <-> (AH[1,0] | AH[1,2])) (AT[1,3] <-> A[]) (AT[1] <-> (AT[1,0] | AT[1,3])) (A[0] <-> A[0,0]) (A[1] <-> A[1,0]) (A[] <-> A[0]) (A[] <-> A[1]) (B[0] <-> B[0,1]) (B[1,3] <-> B[]) (B[1] <-> B[1,3]) (B[] <-> B[0]) (B[] <-> B[1]) (CH[1,1] <-> CT[1,1]) (CH[1] <-> (CH[1,1] | CH[1,2])) (CT[1,3] <-> C[]) (CT[1] <-> (CT[1,1] | CT[1,3])) (C[0] <-> C[0,1]) (C[1] <-> C[1,1]) (C[] <-> C[0]) (C[] <-> C[1])"
