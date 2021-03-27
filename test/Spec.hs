import Lib
import Control.Monad
import qualified Picologic

rule = Rule "append" ["A", "B", "C"] $ Disj
  [ Conj [Func "[]" [] "A", Unif "B" "C"]
  , Conj
    [ Func "[|]" ["AH", "AT"] "A"
    , Func "[|]" ["CH", "CT"] "C"
    , Unif "AH" "CH"
    , Pred "append" ["AT", "B", "CT"]
    ]
  ]

main :: IO ()
main = do
  print rule
  print . variables $ body rule
  let p = constraints' rule
  print p
  Picologic.Solutions solns <- Picologic.solveProp p
  putStrLn . Picologic.ppSolutions $ Picologic.Solutions solns
  forM_ solns $ \soln -> do
    print $ mode soln rule
