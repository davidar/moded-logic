import Lib

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
  print $ constraints [] rule
