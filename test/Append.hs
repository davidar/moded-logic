module Append where
import Control.Applicative
import Control.Monad.Logic

{- append/3
append arg1 arg2 arg3 :- ((arg1 = [], arg2 = x, arg3 = x, ()); (arg1 = ah : t, arg2 = b, arg3 = ch : tb, (ah = ch, append t b tb))).
constraints:
ah[1]
ah[]
b[1]
b[]
ch[1]
ch[]
t[1]
t[]
tb[1]
tb[]
x[0]
x[]
~(ah[1,0] & ah[1,3])
~(ah[1,3,0] & ch[1,3,0])
~(arg1[1,0] & ah[1,0])
~(arg2[0,1] & x[0,1])
~(arg2[1,1] & b[1,1])
~(arg3[0,2] & x[0,2])
~(arg3[1,2] & ch[1,2])
~(b[1,1] & b[1,3])
~(ch[1,2] & ch[1,3])
~(t[1,0] & t[1,3])
~(tb[1,2] & tb[1,3])
~(x[0,1] & x[0,2])
(ah[1,0] <-> t[1,0])
(ah[1,3] <-> ah[1,3,0])
(ah[1] <-> (ah[1,0] | ah[1,3]))
(arg1[0] <-> arg1[0,0])
(arg1[1] <-> arg1[1,0])
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg2[0] <-> arg2[0,1])
(arg2[1] <-> arg2[1,1])
(arg2[] <-> arg2[0])
(arg2[] <-> arg2[1])
(arg3[0] <-> arg3[0,2])
(arg3[1] <-> arg3[1,2])
(arg3[] <-> arg3[0])
(arg3[] <-> arg3[1])
(b[1,3,1] <-> arg2[])
(b[1,3] <-> b[1,3,1])
(b[1] <-> (b[1,1] | b[1,3]))
(ch[1,2] <-> tb[1,2])
(ch[1,3] <-> ch[1,3,0])
(ch[1] <-> (ch[1,2] | ch[1,3]))
(t[1,3,1] <-> arg1[])
(t[1,3] <-> t[1,3,1])
(t[1] <-> (t[1,0] | t[1,3]))
(tb[1,3,1] <-> arg3[])
(tb[1,3] <-> tb[1,3,1])
(tb[1] <-> (tb[1,2] | tb[1,3]))
(x[0] <-> (x[0,1] | x[0,2]))
-}
append_iii arg1 arg2 arg3 = do
  () <- (do
    guard $ arg1 == []
    x <- pure arg2
    guard $ arg3 == x
    () <- (do
      
      pure ()
     )
    pure ()
   ) <|> (do
    (ah:t) <- pure arg1
    b <- pure arg2
    (ch:tb) <- pure arg3
    () <- (do
      guard $ ah == ch
      () <- append_iii t b tb
      pure ()
     )
    pure ()
   )
  pure ()
--append_iii arg1 arg2 arg3 = do
--  () <- (do
--    guard $ arg1 == []
--    x <- pure arg3
--    guard $ arg2 == x
--    () <- (do
--      
--      pure ()
--     )
--    pure ()
--   ) <|> (do
--    (ah:t) <- pure arg1
--    b <- pure arg2
--    (ch:tb) <- pure arg3
--    () <- (do
--      guard $ ah == ch
--      () <- append_iii t b tb
--      pure ()
--     )
--    pure ()
--   )
--  pure ()

append_iio arg1 arg2 = do
  (arg3) <- (do
    guard $ arg1 == []
    x <- pure arg2
    arg3 <- pure x
    () <- (do
      
      pure ()
     )
    pure (arg3)
   ) <|> (do
    (ah:t) <- pure arg1
    b <- pure arg2
    (ch,tb) <- (do
      ch <- pure ah
      (tb) <- append_iio t b
      pure (ch,tb)
     )
    arg3 <- pure (ch:tb)
    pure (arg3)
   )
  pure (arg3)
append_ioi arg1 arg3 = do
  (arg2) <- (do
    guard $ arg1 == []
    x <- pure arg3
    arg2 <- pure x
    () <- (do
      
      pure ()
     )
    pure (arg2)
   ) <|> (do
    (ah:t) <- pure arg1
    (ch:tb) <- pure arg3
    (b) <- (do
      guard $ ah == ch
      (b) <- append_ioi t tb
      pure (b)
     )
    arg2 <- pure b
    pure (arg2)
   )
  pure (arg2)
append_oii arg2 arg3 = do
  (arg1) <- (do
    arg1 <- pure []
    x <- pure arg2
    guard $ arg3 == x
    () <- (do
      
      pure ()
     )
    pure (arg1)
   ) <|> (do
    b <- pure arg2
    (ch:tb) <- pure arg3
    (ah,t) <- (do
      ah <- pure ch
      (t) <- append_oii b tb
      pure (ah,t)
     )
    arg1 <- pure (ah:t)
    pure (arg1)
   )
  pure (arg1)
--append_oii arg2 arg3 = do
--  (arg1) <- (do
--    arg1 <- pure []
--    x <- pure arg3
--    guard $ arg2 == x
--    () <- (do
--      
--      pure ()
--     )
--    pure (arg1)
--   ) <|> (do
--    b <- pure arg2
--    (ch:tb) <- pure arg3
--    (ah,t) <- (do
--      ah <- pure ch
--      (t) <- append_oii b tb
--      pure (ah,t)
--     )
--    arg1 <- pure (ah:t)
--    pure (arg1)
--   )
--  pure (arg1)

append_ooi arg3 = do
  (arg1,arg2) <- (do
    arg1 <- pure []
    x <- pure arg3
    arg2 <- pure x
    () <- (do
      
      pure ()
     )
    pure (arg1,arg2)
   ) <|> (do
    (ch:tb) <- pure arg3
    (ah,b,t) <- (do
      ah <- pure ch
      (t,b) <- append_ooi tb
      pure (ah,b,t)
     )
    arg1 <- pure (ah:t)
    arg2 <- pure b
    pure (arg1,arg2)
   )
  pure (arg1,arg2)