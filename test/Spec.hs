import Lib
import Control.Monad
import qualified Picologic
import qualified Data.Set as Set

rule = Rule "append" ["A", "B", "C"]
  [ [Func "[]" [] "A", Unif "B" "C"]
  , [ Func ":" ["AH", "AT"] "A"
    , Func ":" ["CH", "CT"] "C"
    , Unif "AH" "CH"
    , Pred "append" ["AT", "B", "CT"]
    ]
  ]

main :: IO ()
main = do
  let constraints = cComp [] rule
  print constraints
  Picologic.Solutions solns <- Picologic.solveProp . foldr1 Picologic.Conj $ Set.elems constraints
  forM_ solns $ \soln -> do
    let s = Set.fromList soln
    print s
    print $ mode s rule
