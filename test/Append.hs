module Append where
import Control.Applicative
import Control.Monad.Logic

append_ooi c = (do
  a <- pure []
  b <- pure c
  pure (a,b)
 ) <|> (do
  (ch:ct) <- pure c
  ah <- pure ch
  (at,b) <- append_ooi ct
  a <- pure (ah:at)
  pure (a,b)
 )
append_oii b c = (do
  a <- pure []
  guard $ b == c
  pure (a)
 ) <|> (do
  (ch:ct) <- pure c
  ah <- pure ch
  (at) <- append_oii b ct
  a <- pure (ah:at)
  pure (a)
 )
append_ioi a c = (do
  guard $ a == []
  b <- pure c
  pure (b)
 ) <|> (do
  (ah:at) <- pure a
  (ch:ct) <- pure c
  guard $ ah == ch
  (b) <- append_ioi at ct
  pure (b)
 )
append_iio a b = (do
  guard $ a == []
  c <- pure b
  pure (c)
 ) <|> (do
  (ah:at) <- pure a
  ch <- pure ah
  (ct) <- append_iio at b
  c <- pure (ch:ct)
  pure (c)
 )
append_iii a b c = (do
  guard $ a == []
  guard $ b == c
  pure ()
 ) <|> (do
  (ah:at) <- pure a
  (ch:ct) <- pure c
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
reverse_oi l = (do
  a <- pure []
  guard $ l == []
  pure (a)
 ) <|> (do
  (r,x1) <- append_ooi l
  (h:x0) <- pure x1
  guard $ x0 == []
  (t) <- reverse_oi r
  a <- pure (h:t)
  pure (a)
 )
reverse_io a = (do
  guard $ a == []
  l <- pure []
  pure (l)
 ) <|> (do
  x0 <- pure []
  (h:t) <- pure a
  x1 <- pure (h:x0)
  (r) <- reverse_io t
  (l) <- append_iio r x1
  pure (l)
 )
reverse_ii a l = (do
  guard $ a == []
  guard $ l == []
  pure ()
 ) <|> (do
  x0 <- pure []
  (h:t) <- pure a
  x1 <- pure (h:x0)
  (r) <- append_oii x1 l
  () <- reverse_ii t r
  pure ()
 )
