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
