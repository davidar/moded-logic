module Append where
import Control.Applicative
import Control.Monad.Logic

append_ooi a3 = (do
  a1 <- pure []
  xs <- pure a3
  a2 <- pure xs
  pure (a1,a2)
 ) <|> (do
  (ch:ct) <- pure a3
  ah <- pure ch
  (at,b) <- append_ooi ct
  a1 <- pure (ah:at)
  a2 <- pure b
  pure (a1,a2)
 )
append_oii a2 a3 = (do
  a1 <- pure []
  xs <- pure a2
  guard $ a3 == xs
  pure (a1)
 ) <|> (do
  b <- pure a2
  (ch:ct) <- pure a3
  ah <- pure ch
  (at) <- append_oii b ct
  a1 <- pure (ah:at)
  pure (a1)
 )
append_ioi a1 a3 = (do
  guard $ a1 == []
  xs <- pure a3
  a2 <- pure xs
  pure (a2)
 ) <|> (do
  (ah:at) <- pure a1
  (ch:ct) <- pure a3
  guard $ ah == ch
  (b) <- append_ioi at ct
  a2 <- pure b
  pure (a2)
 )
append_iio a1 a2 = (do
  guard $ a1 == []
  xs <- pure a2
  a3 <- pure xs
  pure (a3)
 ) <|> (do
  (ah:at) <- pure a1
  b <- pure a2
  ch <- pure ah
  (ct) <- append_iio at b
  a3 <- pure (ch:ct)
  pure (a3)
 )
append_iii a1 a2 a3 = (do
  guard $ a1 == []
  xs <- pure a2
  guard $ a3 == xs
  pure ()
 ) <|> (do
  (ah:at) <- pure a1
  b <- pure a2
  (ch:ct) <- pure a3
  guard $ ah == ch
  () <- append_iii at b ct
  pure ()
 )
append_oooi abc = (do
  (ab,c) <- append_ooi abc
  (a,b) <- append_ooi ab
  pure (a,b,c)
 )
append_ooii c abc = (do
  (ab) <- append_oii c abc
  (a,b) <- append_ooi ab
  pure (a,b)
 )
append_oioi b abc = (do
  (ab,c) <- append_ooi abc
  (a) <- append_oii b ab
  pure (a,c)
 )
append_oiii b c abc = (do
  (ab) <- append_oii c abc
  (a) <- append_oii b ab
  pure (a)
 )
append_iiio a b c = (do
  (ab) <- append_iio a b
  (abc) <- append_iio ab c
  pure (abc)
 )
append_iioi a b abc = (do
  (ab) <- append_iio a b
  (c) <- append_ioi ab abc
  pure (c)
 )
append_iiii a b c abc = (do
  (ab) <- append_iio a b
  () <- append_iii ab c abc
  pure ()
 )
append_iooi a abc = (do
  (ab,c) <- append_ooi abc
  (b) <- append_ioi a ab
  pure (b,c)
 )
append_ioii a c abc = (do
  (ab) <- append_oii c abc
  (b) <- append_ioi a ab
  pure (b)
 )
reverse_oi a2 = (do
  a1 <- pure []
  guard $ a2 == []
  pure (a1)
 ) <|> (do
  l <- pure a2
  (r,x1) <- append_ooi l
  (h:x0) <- pure x1
  guard $ x0 == []
  (t) <- reverse_oi r
  a1 <- pure (h:t)
  pure (a1)
 )
reverse_io a1 = (do
  guard $ a1 == []
  a2 <- pure []
  pure (a2)
 ) <|> (do
  x0 <- pure []
  (h:t) <- pure a1
  x1 <- pure (h:x0)
  (r) <- reverse_io t
  (l) <- append_iio r x1
  a2 <- pure l
  pure (a2)
 )
reverse_ii a1 a2 = (do
  guard $ a1 == []
  guard $ a2 == []
  pure ()
 ) <|> (do
  x0 <- pure []
  (h:t) <- pure a1
  x1 <- pure (h:x0)
  l <- pure a2
  (r) <- append_oii x1 l
  () <- reverse_ii t r
  pure ()
 )
