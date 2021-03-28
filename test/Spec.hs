{-#LANGUAGE QuasiQuotes #-}
import Lib
import Control.Monad
import qualified Data.List as List
import qualified Picologic
import qualified Data.Set as Set
import qualified Data.Text as T
import Test.Hspec
import NeatInterpolation

appendRule = Rule "append" ["a", "b", "c"]
    [[Func "[]" [] "a"
     , Unif "b" "c"]
    ,[ Func ":" ["ah", "at"] "a"
     , Func ":" ["ch", "ct"] "c"
     , Unif "ah" "ch"
     , Pred "append" ["at", "b", "ct"]
     ]
    ]

appendConstraints = "ah[1] ah[] at[1] at[] ch[1] ch[] ct[1] ct[] ~(a[1,0] & ah[1,0]) ~(ah[1,0] & ah[1,2]) ~(ah[1,2] & ch[1,2]) ~(at[1,0] & at[1,3]) ~(b[0,1] & c[0,1]) ~(c[1,1] & ch[1,1]) ~(ch[1,1] & ch[1,2]) ~(ct[1,1] & ct[1,3]) (a[0] <-> a[0,0]) (a[1] <-> a[1,0]) (a[] <-> a[0]) (a[] <-> a[1]) (ah[1,0] <-> at[1,0]) (ah[1] <-> (ah[1,0] | ah[1,2])) (at[1,3] <-> a[]) (at[1] <-> (at[1,0] | at[1,3])) (b[0] <-> b[0,1]) (b[1,3] <-> b[]) (b[1] <-> b[1,3]) (b[] <-> b[0]) (b[] <-> b[1]) (c[0] <-> c[0,1]) (c[1] <-> c[1,1]) (c[] <-> c[0]) (c[] <-> c[1]) (ch[1,1] <-> ct[1,1]) (ch[1] <-> (ch[1,1] | ch[1,2])) (ct[1,3] <-> c[]) (ct[1] <-> (ct[1,1] | ct[1,3]))"

appendCode = T.strip [text|
append_ooi c = (do
  b <- pure c
  a <- pure []
  pure (a,b)
 )
 <|> (do
  (ch:ct) <- pure c
  ah <- pure ch
  (at,b) <- append_ooi ct
  a <- pure (ah:at)
  pure (a,b)
 )

append_oii b c = (do
  guard $ b == c
  a <- pure []
  pure (a)
 )
 <|> (do
  (ch:ct) <- pure c
  ah <- pure ch
  (at) <- append_oii b ct
  a <- pure (ah:at)
  pure (a)
 )

append_ioi a c = (do
  b <- pure c
  guard $ a == []
  pure (b)
 )
 <|> (do
  (ch:ct) <- pure c
  (ah:at) <- pure a
  guard $ ah == ch
  (b) <- append_ioi at ct
  pure (b)
 )

append_iio a b = (do
  c <- pure b
  guard $ a == []
  pure (c)
 )
 <|> (do
  (ah:at) <- pure a
  ch <- pure ah
  (ct) <- append_iio at b
  c <- pure (ch:ct)
  pure (c)
 )

append_iii a b c = (do
  guard $ b == c
  guard $ a == []
  pure ()
 )
 <|> (do
  (ch:ct) <- pure c
  (ah:at) <- pure a
  guard $ ah == ch
  () <- append_iii at b ct
  pure ()
 )
 |]

main :: IO ()
main = hspec $ do
    describe "append" $ do
        it "cComp" . (`shouldBe` appendConstraints) $
            List.intercalate " " . map show . Set.elems $ cComp [] appendRule
        it "cgRule" $ do
            solns <- solveConstraints appendRule
            (`shouldBe` appendCode) . T.strip . T.unlines $
                map (\soln -> cgRule $ mode soln appendRule) (Set.elems solns)
