module Queens where
import Control.Applicative
import Control.Monad.Logic
import Control.Monad.Logic.Moded.Prelude

{- delete/3
delete arg1 arg2 arg3 :- ((arg1 = h, (arg2 = h0 : t1, h0 = h, t1 = t), arg3 = t, ()); (arg1 = x, (arg2 = h2 : t3, h2 = h, t3 = t), (arg3 = h4 : r, h4 = h), ((delete x t r)))).
constraints:
~(arg1[0,0] & h[0,0])
~(arg1[1,0] & x[1,0])
~(arg2[0,1,0] & h0[0,1,0])
~(arg2[1,1,0] & h2[1,1,0])
~(arg3[0,2] & t[0,2])
~(arg3[1,2,0] & h4[1,2,0])
~(h0[0,1,0] & h0[0,1,1])
~(h0[0,1,1] & h[0,1,1])
~(h2[1,1,0] & h2[1,1,1])
~(h2[1,1,1] & h[1,1,1])
~(h4[1,2,0] & h4[1,2,1])
~(h4[1,2,1] & h[1,2,1])
~(h[0,0] & h[0,1])
~(h[1,1] & h[1,2])
~(r[1,2] & r[1,3])
~(t1[0,1,0] & t1[0,1,2])
~(t1[0,1,2] & t[0,1,2])
~(t3[1,1,0] & t3[1,1,2])
~(t3[1,1,2] & t[1,1,2])
~(t[0,1] & t[0,2])
~(t[1,1] & t[1,3])
~(x[1,0] & x[1,3])
(h0[0,1,0] | h0[0,1,1])
(h2[1,1,0] | h2[1,1,1])
(h4[1,2,0] | h4[1,2,1])
(h[0,0] | h[0,1])
(h[1,1] | h[1,2])
(r[1,2] | r[1,3])
(t1[0,1,0] | t1[0,1,2])
(t3[1,1,0] | t3[1,1,2])
(t[0,1] | t[0,2])
(t[1,1] | t[1,3])
(x[1,0] | x[1,3])
(arg1[0] <-> arg1[0,0])
(arg1[1] <-> arg1[1,0])
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg2[0,1] <-> arg2[0,1,0])
(arg2[0] <-> arg2[0,1])
(arg2[1,1] <-> arg2[1,1,0])
(arg2[1] <-> arg2[1,1])
(arg2[] <-> arg2[0])
(arg2[] <-> arg2[1])
(arg3[0] <-> arg3[0,2])
(arg3[1,2] <-> arg3[1,2,0])
(arg3[1] <-> arg3[1,2])
(arg3[] <-> arg3[0])
(arg3[] <-> arg3[1])
(h0[0,1,0] <-> t1[0,1,0])
(h2[1,1,0] <-> t3[1,1,0])
(h4[1,2,0] <-> r[1,2,0])
(h[0,1] <-> h[0,1,1])
(h[1,1] <-> h[1,1,1])
(h[1,2] <-> h[1,2,1])
(r[1,2] <-> r[1,2,0])
(r[1,3,0,0] <-> arg3[])
(r[1,3,0] <-> r[1,3,0,0])
(r[1,3] <-> r[1,3,0])
(t[0,1] <-> t[0,1,2])
(t[1,1] <-> t[1,1,2])
(t[1,3,0,0] <-> arg2[])
(t[1,3,0] <-> t[1,3,0,0])
(t[1,3] <-> t[1,3,0])
(x[1,3,0,0] <-> arg1[])
(x[1,3,0] <-> x[1,3,0,0])
(x[1,3] <-> x[1,3,0])
1
-}
delete_iii arg1 arg2 arg3 = do
  -- solution: h0[0,1,0] h2[1,1,0] h4[1,2,0] h[0,0] h[1,1,1] h[1,1] r[1,2,0] r[1,2] t1[0,1,0] t3[1,1,0] t[0,1,2] t[0,1] t[1,1,2] t[1,1] x[1,0] ~arg1[0,0] ~arg1[0] ~arg1[1,0] ~arg1[1] ~arg1[] ~arg2[0,1,0] ~arg2[0,1] ~arg2[0] ~arg2[1,1,0] ~arg2[1,1] ~arg2[1] ~arg2[] ~arg3[0,2] ~arg3[0] ~arg3[1,2,0] ~arg3[1,2] ~arg3[1] ~arg3[] ~h0[0,1,1] ~h2[1,1,1] ~h4[1,2,1] ~h[0,1,1] ~h[0,1] ~h[1,2,1] ~h[1,2] ~r[1,3,0,0] ~r[1,3,0] ~r[1,3] ~t1[0,1,2] ~t3[1,1,2] ~t[0,2] ~t[1,3,0,0] ~t[1,3,0] ~t[1,3] ~x[1,3,0,0] ~x[1,3,0] ~x[1,3]
  () <- (do
    h <- pure arg1
    (t) <- (do
      (h0:t1) <- pure arg2
      guard $ h0 == h
      t <- pure t1
      pure (t)
     )
    guard $ arg3 == t
    () <- (do
      
      pure ()
     )
    pure ()
   ) <|> (do
    x <- pure arg1
    (h,t) <- (do
      (h2:t3) <- pure arg2
      h <- pure h2
      t <- pure t3
      pure (h,t)
     )
    (r) <- (do
      (h4:r) <- pure arg3
      guard $ h4 == h
      pure (r)
     )
    () <- (do
      () <- (do
        () <- delete_iii x t r
        pure ()
       )
      pure ()
     )
    pure ()
   )
  pure ()

--delete_iii arg1 arg2 arg3 = do
--  -- solution: h0[0,1,0] h2[1,1,0] h4[1,2,0] h[0,0] h[1,1,1] h[1,1] r[1,2,0] r[1,2] t1[0,1,0] t3[1,1,0] t[0,2] t[1,1,2] t[1,1] x[1,0] ~arg1[0,0] ~arg1[0] ~arg1[1,0] ~arg1[1] ~arg1[] ~arg2[0,1,0] ~arg2[0,1] ~arg2[0] ~arg2[1,1,0] ~arg2[1,1] ~arg2[1] ~arg2[] ~arg3[0,2] ~arg3[0] ~arg3[1,2,0] ~arg3[1,2] ~arg3[1] ~arg3[] ~h0[0,1,1] ~h2[1,1,1] ~h4[1,2,1] ~h[0,1,1] ~h[0,1] ~h[1,2,1] ~h[1,2] ~r[1,3,0,0] ~r[1,3,0] ~r[1,3] ~t1[0,1,2] ~t3[1,1,2] ~t[0,1,2] ~t[0,1] ~t[1,3,0,0] ~t[1,3,0] ~t[1,3] ~x[1,3,0,0] ~x[1,3,0] ~x[1,3]
--  () <- (do
--    h <- pure arg1
--    t <- pure arg3
--    () <- (do
--      (h0:t1) <- pure arg2
--      guard $ h0 == h
--      guard $ t1 == t
--      pure ()
--     )
--    () <- (do
--      
--      pure ()
--     )
--    pure ()
--   ) <|> (do
--    x <- pure arg1
--    (h,t) <- (do
--      (h2:t3) <- pure arg2
--      h <- pure h2
--      t <- pure t3
--      pure (h,t)
--     )
--    (r) <- (do
--      (h4:r) <- pure arg3
--      guard $ h4 == h
--      pure (r)
--     )
--    () <- (do
--      () <- (do
--        () <- delete_iii x t r
--        pure ()
--       )
--      pure ()
--     )
--    pure ()
--   )
--  pure ()

--delete_iii arg1 arg2 arg3 = do
--  -- solution: h0[0,1,0] h2[1,1,0] h4[1,2,0] h[0,0] h[1,2,1] h[1,2] r[1,2,0] r[1,2] t1[0,1,0] t3[1,1,0] t[0,1,2] t[0,1] t[1,1,2] t[1,1] x[1,0] ~arg1[0,0] ~arg1[0] ~arg1[1,0] ~arg1[1] ~arg1[] ~arg2[0,1,0] ~arg2[0,1] ~arg2[0] ~arg2[1,1,0] ~arg2[1,1] ~arg2[1] ~arg2[] ~arg3[0,2] ~arg3[0] ~arg3[1,2,0] ~arg3[1,2] ~arg3[1] ~arg3[] ~h0[0,1,1] ~h2[1,1,1] ~h4[1,2,1] ~h[0,1,1] ~h[0,1] ~h[1,1,1] ~h[1,1] ~r[1,3,0,0] ~r[1,3,0] ~r[1,3] ~t1[0,1,2] ~t3[1,1,2] ~t[0,2] ~t[1,3,0,0] ~t[1,3,0] ~t[1,3] ~x[1,3,0,0] ~x[1,3,0] ~x[1,3]
--  () <- (do
--    h <- pure arg1
--    (t) <- (do
--      (h0:t1) <- pure arg2
--      guard $ h0 == h
--      t <- pure t1
--      pure (t)
--     )
--    guard $ arg3 == t
--    () <- (do
--      
--      pure ()
--     )
--    pure ()
--   ) <|> (do
--    x <- pure arg1
--    (h,r) <- (do
--      (h4:r) <- pure arg3
--      h <- pure h4
--      pure (h,r)
--     )
--    (t) <- (do
--      (h2:t3) <- pure arg2
--      guard $ h2 == h
--      t <- pure t3
--      pure (t)
--     )
--    () <- (do
--      () <- (do
--        () <- delete_iii x t r
--        pure ()
--       )
--      pure ()
--     )
--    pure ()
--   )
--  pure ()

--delete_iii arg1 arg2 arg3 = do
--  -- solution: h0[0,1,0] h2[1,1,0] h4[1,2,0] h[0,0] h[1,2,1] h[1,2] r[1,2,0] r[1,2] t1[0,1,0] t3[1,1,0] t[0,2] t[1,1,2] t[1,1] x[1,0] ~arg1[0,0] ~arg1[0] ~arg1[1,0] ~arg1[1] ~arg1[] ~arg2[0,1,0] ~arg2[0,1] ~arg2[0] ~arg2[1,1,0] ~arg2[1,1] ~arg2[1] ~arg2[] ~arg3[0,2] ~arg3[0] ~arg3[1,2,0] ~arg3[1,2] ~arg3[1] ~arg3[] ~h0[0,1,1] ~h2[1,1,1] ~h4[1,2,1] ~h[0,1,1] ~h[0,1] ~h[1,1,1] ~h[1,1] ~r[1,3,0,0] ~r[1,3,0] ~r[1,3] ~t1[0,1,2] ~t3[1,1,2] ~t[0,1,2] ~t[0,1] ~t[1,3,0,0] ~t[1,3,0] ~t[1,3] ~x[1,3,0,0] ~x[1,3,0] ~x[1,3]
--  () <- (do
--    h <- pure arg1
--    t <- pure arg3
--    () <- (do
--      (h0:t1) <- pure arg2
--      guard $ h0 == h
--      guard $ t1 == t
--      pure ()
--     )
--    () <- (do
--      
--      pure ()
--     )
--    pure ()
--   ) <|> (do
--    x <- pure arg1
--    (h,r) <- (do
--      (h4:r) <- pure arg3
--      h <- pure h4
--      pure (h,r)
--     )
--    (t) <- (do
--      (h2:t3) <- pure arg2
--      guard $ h2 == h
--      t <- pure t3
--      pure (t)
--     )
--    () <- (do
--      () <- (do
--        () <- delete_iii x t r
--        pure ()
--       )
--      pure ()
--     )
--    pure ()
--   )
--  pure ()

--delete_iii arg1 arg2 arg3 = do
--  -- solution: h0[0,1,0] h2[1,1,0] h4[1,2,0] h[0,1,1] h[0,1] h[1,1,1] h[1,1] r[1,2,0] r[1,2] t1[0,1,0] t3[1,1,0] t[0,1,2] t[0,1] t[1,1,2] t[1,1] x[1,0] ~arg1[0,0] ~arg1[0] ~arg1[1,0] ~arg1[1] ~arg1[] ~arg2[0,1,0] ~arg2[0,1] ~arg2[0] ~arg2[1,1,0] ~arg2[1,1] ~arg2[1] ~arg2[] ~arg3[0,2] ~arg3[0] ~arg3[1,2,0] ~arg3[1,2] ~arg3[1] ~arg3[] ~h0[0,1,1] ~h2[1,1,1] ~h4[1,2,1] ~h[0,0] ~h[1,2,1] ~h[1,2] ~r[1,3,0,0] ~r[1,3,0] ~r[1,3] ~t1[0,1,2] ~t3[1,1,2] ~t[0,2] ~t[1,3,0,0] ~t[1,3,0] ~t[1,3] ~x[1,3,0,0] ~x[1,3,0] ~x[1,3]
--  () <- (do
--    (h,t) <- (do
--      (h0:t1) <- pure arg2
--      h <- pure h0
--      t <- pure t1
--      pure (h,t)
--     )
--    guard $ arg1 == h
--    guard $ arg3 == t
--    () <- (do
--      
--      pure ()
--     )
--    pure ()
--   ) <|> (do
--    x <- pure arg1
--    (h,t) <- (do
--      (h2:t3) <- pure arg2
--      h <- pure h2
--      t <- pure t3
--      pure (h,t)
--     )
--    (r) <- (do
--      (h4:r) <- pure arg3
--      guard $ h4 == h
--      pure (r)
--     )
--    () <- (do
--      () <- (do
--        () <- delete_iii x t r
--        pure ()
--       )
--      pure ()
--     )
--    pure ()
--   )
--  pure ()

--delete_iii arg1 arg2 arg3 = do
--  -- solution: h0[0,1,0] h2[1,1,0] h4[1,2,0] h[0,1,1] h[0,1] h[1,1,1] h[1,1] r[1,2,0] r[1,2] t1[0,1,0] t3[1,1,0] t[0,2] t[1,1,2] t[1,1] x[1,0] ~arg1[0,0] ~arg1[0] ~arg1[1,0] ~arg1[1] ~arg1[] ~arg2[0,1,0] ~arg2[0,1] ~arg2[0] ~arg2[1,1,0] ~arg2[1,1] ~arg2[1] ~arg2[] ~arg3[0,2] ~arg3[0] ~arg3[1,2,0] ~arg3[1,2] ~arg3[1] ~arg3[] ~h0[0,1,1] ~h2[1,1,1] ~h4[1,2,1] ~h[0,0] ~h[1,2,1] ~h[1,2] ~r[1,3,0,0] ~r[1,3,0] ~r[1,3] ~t1[0,1,2] ~t3[1,1,2] ~t[0,1,2] ~t[0,1] ~t[1,3,0,0] ~t[1,3,0] ~t[1,3] ~x[1,3,0,0] ~x[1,3,0] ~x[1,3]
--  () <- (do
--    t <- pure arg3
--    (h) <- (do
--      (h0:t1) <- pure arg2
--      h <- pure h0
--      guard $ t1 == t
--      pure (h)
--     )
--    guard $ arg1 == h
--    () <- (do
--      
--      pure ()
--     )
--    pure ()
--   ) <|> (do
--    x <- pure arg1
--    (h,t) <- (do
--      (h2:t3) <- pure arg2
--      h <- pure h2
--      t <- pure t3
--      pure (h,t)
--     )
--    (r) <- (do
--      (h4:r) <- pure arg3
--      guard $ h4 == h
--      pure (r)
--     )
--    () <- (do
--      () <- (do
--        () <- delete_iii x t r
--        pure ()
--       )
--      pure ()
--     )
--    pure ()
--   )
--  pure ()

--delete_iii arg1 arg2 arg3 = do
--  -- solution: h0[0,1,0] h2[1,1,0] h4[1,2,0] h[0,1,1] h[0,1] h[1,2,1] h[1,2] r[1,2,0] r[1,2] t1[0,1,0] t3[1,1,0] t[0,1,2] t[0,1] t[1,1,2] t[1,1] x[1,0] ~arg1[0,0] ~arg1[0] ~arg1[1,0] ~arg1[1] ~arg1[] ~arg2[0,1,0] ~arg2[0,1] ~arg2[0] ~arg2[1,1,0] ~arg2[1,1] ~arg2[1] ~arg2[] ~arg3[0,2] ~arg3[0] ~arg3[1,2,0] ~arg3[1,2] ~arg3[1] ~arg3[] ~h0[0,1,1] ~h2[1,1,1] ~h4[1,2,1] ~h[0,0] ~h[1,1,1] ~h[1,1] ~r[1,3,0,0] ~r[1,3,0] ~r[1,3] ~t1[0,1,2] ~t3[1,1,2] ~t[0,2] ~t[1,3,0,0] ~t[1,3,0] ~t[1,3] ~x[1,3,0,0] ~x[1,3,0] ~x[1,3]
--  () <- (do
--    (h,t) <- (do
--      (h0:t1) <- pure arg2
--      h <- pure h0
--      t <- pure t1
--      pure (h,t)
--     )
--    guard $ arg1 == h
--    guard $ arg3 == t
--    () <- (do
--      
--      pure ()
--     )
--    pure ()
--   ) <|> (do
--    x <- pure arg1
--    (h,r) <- (do
--      (h4:r) <- pure arg3
--      h <- pure h4
--      pure (h,r)
--     )
--    (t) <- (do
--      (h2:t3) <- pure arg2
--      guard $ h2 == h
--      t <- pure t3
--      pure (t)
--     )
--    () <- (do
--      () <- (do
--        () <- delete_iii x t r
--        pure ()
--       )
--      pure ()
--     )
--    pure ()
--   )
--  pure ()

--delete_iii arg1 arg2 arg3 = do
--  -- solution: h0[0,1,0] h2[1,1,0] h4[1,2,0] h[0,1,1] h[0,1] h[1,2,1] h[1,2] r[1,2,0] r[1,2] t1[0,1,0] t3[1,1,0] t[0,2] t[1,1,2] t[1,1] x[1,0] ~arg1[0,0] ~arg1[0] ~arg1[1,0] ~arg1[1] ~arg1[] ~arg2[0,1,0] ~arg2[0,1] ~arg2[0] ~arg2[1,1,0] ~arg2[1,1] ~arg2[1] ~arg2[] ~arg3[0,2] ~arg3[0] ~arg3[1,2,0] ~arg3[1,2] ~arg3[1] ~arg3[] ~h0[0,1,1] ~h2[1,1,1] ~h4[1,2,1] ~h[0,0] ~h[1,1,1] ~h[1,1] ~r[1,3,0,0] ~r[1,3,0] ~r[1,3] ~t1[0,1,2] ~t3[1,1,2] ~t[0,1,2] ~t[0,1] ~t[1,3,0,0] ~t[1,3,0] ~t[1,3] ~x[1,3,0,0] ~x[1,3,0] ~x[1,3]
--  () <- (do
--    t <- pure arg3
--    (h) <- (do
--      (h0:t1) <- pure arg2
--      h <- pure h0
--      guard $ t1 == t
--      pure (h)
--     )
--    guard $ arg1 == h
--    () <- (do
--      
--      pure ()
--     )
--    pure ()
--   ) <|> (do
--    x <- pure arg1
--    (h,r) <- (do
--      (h4:r) <- pure arg3
--      h <- pure h4
--      pure (h,r)
--     )
--    (t) <- (do
--      (h2:t3) <- pure arg2
--      guard $ h2 == h
--      t <- pure t3
--      pure (t)
--     )
--    () <- (do
--      () <- (do
--        () <- delete_iii x t r
--        pure ()
--       )
--      pure ()
--     )
--    pure ()
--   )
--  pure ()

--delete_iii arg1 arg2 arg3 = do
--  -- solution: h0[0,1,1] h2[1,1,0] h4[1,2,0] h[0,0] h[1,1,1] h[1,1] r[1,2,0] r[1,2] t1[0,1,2] t3[1,1,0] t[0,2] t[1,1,2] t[1,1] x[1,0] ~arg1[0,0] ~arg1[0] ~arg1[1,0] ~arg1[1] ~arg1[] ~arg2[0,1,0] ~arg2[0,1] ~arg2[0] ~arg2[1,1,0] ~arg2[1,1] ~arg2[1] ~arg2[] ~arg3[0,2] ~arg3[0] ~arg3[1,2,0] ~arg3[1,2] ~arg3[1] ~arg3[] ~h0[0,1,0] ~h2[1,1,1] ~h4[1,2,1] ~h[0,1,1] ~h[0,1] ~h[1,2,1] ~h[1,2] ~r[1,3,0,0] ~r[1,3,0] ~r[1,3] ~t1[0,1,0] ~t3[1,1,2] ~t[0,1,2] ~t[0,1] ~t[1,3,0,0] ~t[1,3,0] ~t[1,3] ~x[1,3,0,0] ~x[1,3,0] ~x[1,3]
--  () <- (do
--    h <- pure arg1
--    t <- pure arg3
--    () <- (do
--      h0 <- pure h
--      t1 <- pure t
--      guard $ arg2 == (h0:t1)
--      pure ()
--     )
--    () <- (do
--      
--      pure ()
--     )
--    pure ()
--   ) <|> (do
--    x <- pure arg1
--    (h,t) <- (do
--      (h2:t3) <- pure arg2
--      h <- pure h2
--      t <- pure t3
--      pure (h,t)
--     )
--    (r) <- (do
--      (h4:r) <- pure arg3
--      guard $ h4 == h
--      pure (r)
--     )
--    () <- (do
--      () <- (do
--        () <- delete_iii x t r
--        pure ()
--       )
--      pure ()
--     )
--    pure ()
--   )
--  pure ()

--delete_iii arg1 arg2 arg3 = do
--  -- solution: h0[0,1,1] h2[1,1,0] h4[1,2,0] h[0,0] h[1,2,1] h[1,2] r[1,2,0] r[1,2] t1[0,1,2] t3[1,1,0] t[0,2] t[1,1,2] t[1,1] x[1,0] ~arg1[0,0] ~arg1[0] ~arg1[1,0] ~arg1[1] ~arg1[] ~arg2[0,1,0] ~arg2[0,1] ~arg2[0] ~arg2[1,1,0] ~arg2[1,1] ~arg2[1] ~arg2[] ~arg3[0,2] ~arg3[0] ~arg3[1,2,0] ~arg3[1,2] ~arg3[1] ~arg3[] ~h0[0,1,0] ~h2[1,1,1] ~h4[1,2,1] ~h[0,1,1] ~h[0,1] ~h[1,1,1] ~h[1,1] ~r[1,3,0,0] ~r[1,3,0] ~r[1,3] ~t1[0,1,0] ~t3[1,1,2] ~t[0,1,2] ~t[0,1] ~t[1,3,0,0] ~t[1,3,0] ~t[1,3] ~x[1,3,0,0] ~x[1,3,0] ~x[1,3]
--  () <- (do
--    h <- pure arg1
--    t <- pure arg3
--    () <- (do
--      h0 <- pure h
--      t1 <- pure t
--      guard $ arg2 == (h0:t1)
--      pure ()
--     )
--    () <- (do
--      
--      pure ()
--     )
--    pure ()
--   ) <|> (do
--    x <- pure arg1
--    (h,r) <- (do
--      (h4:r) <- pure arg3
--      h <- pure h4
--      pure (h,r)
--     )
--    (t) <- (do
--      (h2:t3) <- pure arg2
--      guard $ h2 == h
--      t <- pure t3
--      pure (t)
--     )
--    () <- (do
--      () <- (do
--        () <- delete_iii x t r
--        pure ()
--       )
--      pure ()
--     )
--    pure ()
--   )
--  pure ()

delete_iio arg1 arg2 = do
  -- solution: arg3[0,2] arg3[0] arg3[1,2,0] arg3[1,2] arg3[1] arg3[] h0[0,1,0] h2[1,1,0] h4[1,2,1] h[0,0] h[1,1,1] h[1,1] r[1,3,0,0] r[1,3,0] r[1,3] t1[0,1,0] t3[1,1,0] t[0,1,2] t[0,1] t[1,1,2] t[1,1] x[1,0] ~arg1[0,0] ~arg1[0] ~arg1[1,0] ~arg1[1] ~arg1[] ~arg2[0,1,0] ~arg2[0,1] ~arg2[0] ~arg2[1,1,0] ~arg2[1,1] ~arg2[1] ~arg2[] ~h0[0,1,1] ~h2[1,1,1] ~h4[1,2,0] ~h[0,1,1] ~h[0,1] ~h[1,2,1] ~h[1,2] ~r[1,2,0] ~r[1,2] ~t1[0,1,2] ~t3[1,1,2] ~t[0,2] ~t[1,3,0,0] ~t[1,3,0] ~t[1,3] ~x[1,3,0,0] ~x[1,3,0] ~x[1,3]
  (arg3) <- (do
    h <- pure arg1
    (t) <- (do
      (h0:t1) <- pure arg2
      guard $ h0 == h
      t <- pure t1
      pure (t)
     )
    arg3 <- pure t
    () <- (do
      
      pure ()
     )
    pure (arg3)
   ) <|> (do
    x <- pure arg1
    (h,t) <- (do
      (h2:t3) <- pure arg2
      h <- pure h2
      t <- pure t3
      pure (h,t)
     )
    (r) <- (do
      (r) <- (do
        (r) <- delete_iio x t
        pure (r)
       )
      pure (r)
     )
    (arg3) <- (do
      h4 <- pure h
      arg3 <- pure (h4:r)
      pure (arg3)
     )
    pure (arg3)
   )
  pure (arg3)

--delete_iio arg1 arg2 = do
--  -- solution: arg3[0,2] arg3[0] arg3[1,2,0] arg3[1,2] arg3[1] arg3[] h0[0,1,0] h2[1,1,0] h4[1,2,1] h[0,1,1] h[0,1] h[1,1,1] h[1,1] r[1,3,0,0] r[1,3,0] r[1,3] t1[0,1,0] t3[1,1,0] t[0,1,2] t[0,1] t[1,1,2] t[1,1] x[1,0] ~arg1[0,0] ~arg1[0] ~arg1[1,0] ~arg1[1] ~arg1[] ~arg2[0,1,0] ~arg2[0,1] ~arg2[0] ~arg2[1,1,0] ~arg2[1,1] ~arg2[1] ~arg2[] ~h0[0,1,1] ~h2[1,1,1] ~h4[1,2,0] ~h[0,0] ~h[1,2,1] ~h[1,2] ~r[1,2,0] ~r[1,2] ~t1[0,1,2] ~t3[1,1,2] ~t[0,2] ~t[1,3,0,0] ~t[1,3,0] ~t[1,3] ~x[1,3,0,0] ~x[1,3,0] ~x[1,3]
--  (arg3) <- (do
--    (h,t) <- (do
--      (h0:t1) <- pure arg2
--      h <- pure h0
--      t <- pure t1
--      pure (h,t)
--     )
--    guard $ arg1 == h
--    arg3 <- pure t
--    () <- (do
--      
--      pure ()
--     )
--    pure (arg3)
--   ) <|> (do
--    x <- pure arg1
--    (h,t) <- (do
--      (h2:t3) <- pure arg2
--      h <- pure h2
--      t <- pure t3
--      pure (h,t)
--     )
--    (r) <- (do
--      (r) <- (do
--        (r) <- delete_iio x t
--        pure (r)
--       )
--      pure (r)
--     )
--    (arg3) <- (do
--      h4 <- pure h
--      arg3 <- pure (h4:r)
--      pure (arg3)
--     )
--    pure (arg3)
--   )
--  pure (arg3)

delete_ioi arg1 arg3 = do
  -- solution: arg2[0,1,0] arg2[0,1] arg2[0] arg2[1,1,0] arg2[1,1] arg2[1] arg2[] h0[0,1,1] h2[1,1,1] h4[1,2,0] h[0,0] h[1,2,1] h[1,2] r[1,2,0] r[1,2] t1[0,1,2] t3[1,1,2] t[0,2] t[1,3,0,0] t[1,3,0] t[1,3] x[1,0] ~arg1[0,0] ~arg1[0] ~arg1[1,0] ~arg1[1] ~arg1[] ~arg3[0,2] ~arg3[0] ~arg3[1,2,0] ~arg3[1,2] ~arg3[1] ~arg3[] ~h0[0,1,0] ~h2[1,1,0] ~h4[1,2,1] ~h[0,1,1] ~h[0,1] ~h[1,1,1] ~h[1,1] ~r[1,3,0,0] ~r[1,3,0] ~r[1,3] ~t1[0,1,0] ~t3[1,1,0] ~t[0,1,2] ~t[0,1] ~t[1,1,2] ~t[1,1] ~x[1,3,0,0] ~x[1,3,0] ~x[1,3]
  (arg2) <- (do
    h <- pure arg1
    t <- pure arg3
    (arg2) <- (do
      h0 <- pure h
      t1 <- pure t
      arg2 <- pure (h0:t1)
      pure (arg2)
     )
    () <- (do
      
      pure ()
     )
    pure (arg2)
   ) <|> (do
    x <- pure arg1
    (h,r) <- (do
      (h4:r) <- pure arg3
      h <- pure h4
      pure (h,r)
     )
    (t) <- (do
      (t) <- (do
        (t) <- delete_ioi x r
        pure (t)
       )
      pure (t)
     )
    (arg2) <- (do
      h2 <- pure h
      t3 <- pure t
      arg2 <- pure (h2:t3)
      pure (arg2)
     )
    pure (arg2)
   )
  pure (arg2)

delete_oii arg2 arg3 = do
  -- solution: arg1[0,0] arg1[0] arg1[1,0] arg1[1] arg1[] h0[0,1,0] h2[1,1,0] h4[1,2,0] h[0,1,1] h[0,1] h[1,1,1] h[1,1] r[1,2,0] r[1,2] t1[0,1,0] t3[1,1,0] t[0,1,2] t[0,1] t[1,1,2] t[1,1] x[1,3,0,0] x[1,3,0] x[1,3] ~arg2[0,1,0] ~arg2[0,1] ~arg2[0] ~arg2[1,1,0] ~arg2[1,1] ~arg2[1] ~arg2[] ~arg3[0,2] ~arg3[0] ~arg3[1,2,0] ~arg3[1,2] ~arg3[1] ~arg3[] ~h0[0,1,1] ~h2[1,1,1] ~h4[1,2,1] ~h[0,0] ~h[1,2,1] ~h[1,2] ~r[1,3,0,0] ~r[1,3,0] ~r[1,3] ~t1[0,1,2] ~t3[1,1,2] ~t[0,2] ~t[1,3,0,0] ~t[1,3,0] ~t[1,3] ~x[1,0]
  (arg1) <- (do
    (h,t) <- (do
      (h0:t1) <- pure arg2
      h <- pure h0
      t <- pure t1
      pure (h,t)
     )
    arg1 <- pure h
    guard $ arg3 == t
    () <- (do
      
      pure ()
     )
    pure (arg1)
   ) <|> (do
    (h,t) <- (do
      (h2:t3) <- pure arg2
      h <- pure h2
      t <- pure t3
      pure (h,t)
     )
    (r) <- (do
      (h4:r) <- pure arg3
      guard $ h4 == h
      pure (r)
     )
    (x) <- (do
      (x) <- (do
        (x) <- delete_oii t r
        pure (x)
       )
      pure (x)
     )
    arg1 <- pure x
    pure (arg1)
   )
  pure (arg1)

--delete_oii arg2 arg3 = do
--  -- solution: arg1[0,0] arg1[0] arg1[1,0] arg1[1] arg1[] h0[0,1,0] h2[1,1,0] h4[1,2,0] h[0,1,1] h[0,1] h[1,1,1] h[1,1] r[1,2,0] r[1,2] t1[0,1,0] t3[1,1,0] t[0,2] t[1,1,2] t[1,1] x[1,3,0,0] x[1,3,0] x[1,3] ~arg2[0,1,0] ~arg2[0,1] ~arg2[0] ~arg2[1,1,0] ~arg2[1,1] ~arg2[1] ~arg2[] ~arg3[0,2] ~arg3[0] ~arg3[1,2,0] ~arg3[1,2] ~arg3[1] ~arg3[] ~h0[0,1,1] ~h2[1,1,1] ~h4[1,2,1] ~h[0,0] ~h[1,2,1] ~h[1,2] ~r[1,3,0,0] ~r[1,3,0] ~r[1,3] ~t1[0,1,2] ~t3[1,1,2] ~t[0,1,2] ~t[0,1] ~t[1,3,0,0] ~t[1,3,0] ~t[1,3] ~x[1,0]
--  (arg1) <- (do
--    t <- pure arg3
--    (h) <- (do
--      (h0:t1) <- pure arg2
--      h <- pure h0
--      guard $ t1 == t
--      pure (h)
--     )
--    arg1 <- pure h
--    () <- (do
--      
--      pure ()
--     )
--    pure (arg1)
--   ) <|> (do
--    (h,t) <- (do
--      (h2:t3) <- pure arg2
--      h <- pure h2
--      t <- pure t3
--      pure (h,t)
--     )
--    (r) <- (do
--      (h4:r) <- pure arg3
--      guard $ h4 == h
--      pure (r)
--     )
--    (x) <- (do
--      (x) <- (do
--        (x) <- delete_oii t r
--        pure (x)
--       )
--      pure (x)
--     )
--    arg1 <- pure x
--    pure (arg1)
--   )
--  pure (arg1)

--delete_oii arg2 arg3 = do
--  -- solution: arg1[0,0] arg1[0] arg1[1,0] arg1[1] arg1[] h0[0,1,0] h2[1,1,0] h4[1,2,0] h[0,1,1] h[0,1] h[1,2,1] h[1,2] r[1,2,0] r[1,2] t1[0,1,0] t3[1,1,0] t[0,1,2] t[0,1] t[1,1,2] t[1,1] x[1,3,0,0] x[1,3,0] x[1,3] ~arg2[0,1,0] ~arg2[0,1] ~arg2[0] ~arg2[1,1,0] ~arg2[1,1] ~arg2[1] ~arg2[] ~arg3[0,2] ~arg3[0] ~arg3[1,2,0] ~arg3[1,2] ~arg3[1] ~arg3[] ~h0[0,1,1] ~h2[1,1,1] ~h4[1,2,1] ~h[0,0] ~h[1,1,1] ~h[1,1] ~r[1,3,0,0] ~r[1,3,0] ~r[1,3] ~t1[0,1,2] ~t3[1,1,2] ~t[0,2] ~t[1,3,0,0] ~t[1,3,0] ~t[1,3] ~x[1,0]
--  (arg1) <- (do
--    (h,t) <- (do
--      (h0:t1) <- pure arg2
--      h <- pure h0
--      t <- pure t1
--      pure (h,t)
--     )
--    arg1 <- pure h
--    guard $ arg3 == t
--    () <- (do
--      
--      pure ()
--     )
--    pure (arg1)
--   ) <|> (do
--    (h,r) <- (do
--      (h4:r) <- pure arg3
--      h <- pure h4
--      pure (h,r)
--     )
--    (t) <- (do
--      (h2:t3) <- pure arg2
--      guard $ h2 == h
--      t <- pure t3
--      pure (t)
--     )
--    (x) <- (do
--      (x) <- (do
--        (x) <- delete_oii t r
--        pure (x)
--       )
--      pure (x)
--     )
--    arg1 <- pure x
--    pure (arg1)
--   )
--  pure (arg1)

--delete_oii arg2 arg3 = do
--  -- solution: arg1[0,0] arg1[0] arg1[1,0] arg1[1] arg1[] h0[0,1,0] h2[1,1,0] h4[1,2,0] h[0,1,1] h[0,1] h[1,2,1] h[1,2] r[1,2,0] r[1,2] t1[0,1,0] t3[1,1,0] t[0,2] t[1,1,2] t[1,1] x[1,3,0,0] x[1,3,0] x[1,3] ~arg2[0,1,0] ~arg2[0,1] ~arg2[0] ~arg2[1,1,0] ~arg2[1,1] ~arg2[1] ~arg2[] ~arg3[0,2] ~arg3[0] ~arg3[1,2,0] ~arg3[1,2] ~arg3[1] ~arg3[] ~h0[0,1,1] ~h2[1,1,1] ~h4[1,2,1] ~h[0,0] ~h[1,1,1] ~h[1,1] ~r[1,3,0,0] ~r[1,3,0] ~r[1,3] ~t1[0,1,2] ~t3[1,1,2] ~t[0,1,2] ~t[0,1] ~t[1,3,0,0] ~t[1,3,0] ~t[1,3] ~x[1,0]
--  (arg1) <- (do
--    t <- pure arg3
--    (h) <- (do
--      (h0:t1) <- pure arg2
--      h <- pure h0
--      guard $ t1 == t
--      pure (h)
--     )
--    arg1 <- pure h
--    () <- (do
--      
--      pure ()
--     )
--    pure (arg1)
--   ) <|> (do
--    (h,r) <- (do
--      (h4:r) <- pure arg3
--      h <- pure h4
--      pure (h,r)
--     )
--    (t) <- (do
--      (h2:t3) <- pure arg2
--      guard $ h2 == h
--      t <- pure t3
--      pure (t)
--     )
--    (x) <- (do
--      (x) <- (do
--        (x) <- delete_oii t r
--        pure (x)
--       )
--      pure (x)
--     )
--    arg1 <- pure x
--    pure (arg1)
--   )
--  pure (arg1)

delete_oio arg2 = do
  -- solution: arg1[0,0] arg1[0] arg1[1,0] arg1[1] arg1[] arg3[0,2] arg3[0] arg3[1,2,0] arg3[1,2] arg3[1] arg3[] h0[0,1,0] h2[1,1,0] h4[1,2,1] h[0,1,1] h[0,1] h[1,1,1] h[1,1] r[1,3,0,0] r[1,3,0] r[1,3] t1[0,1,0] t3[1,1,0] t[0,1,2] t[0,1] t[1,1,2] t[1,1] x[1,3,0,0] x[1,3,0] x[1,3] ~arg2[0,1,0] ~arg2[0,1] ~arg2[0] ~arg2[1,1,0] ~arg2[1,1] ~arg2[1] ~arg2[] ~h0[0,1,1] ~h2[1,1,1] ~h4[1,2,0] ~h[0,0] ~h[1,2,1] ~h[1,2] ~r[1,2,0] ~r[1,2] ~t1[0,1,2] ~t3[1,1,2] ~t[0,2] ~t[1,3,0,0] ~t[1,3,0] ~t[1,3] ~x[1,0]
  (arg1,arg3) <- (do
    (h,t) <- (do
      (h0:t1) <- pure arg2
      h <- pure h0
      t <- pure t1
      pure (h,t)
     )
    arg1 <- pure h
    arg3 <- pure t
    () <- (do
      
      pure ()
     )
    pure (arg1,arg3)
   ) <|> (do
    (h,t) <- (do
      (h2:t3) <- pure arg2
      h <- pure h2
      t <- pure t3
      pure (h,t)
     )
    (r,x) <- (do
      (r,x) <- (do
        (x,r) <- delete_oio t
        pure (r,x)
       )
      pure (r,x)
     )
    arg1 <- pure x
    (arg3) <- (do
      h4 <- pure h
      arg3 <- pure (h4:r)
      pure (arg3)
     )
    pure (arg1,arg3)
   )
  pure (arg1,arg3)

{- nodiag/3
nodiag arg1 arg2 arg3 :- (((arg3 = []), ()); (arg1 = b, arg2 = d, (arg3 = h : t), ((plus hmb b h), (plus bmh h b), (succ d d1), if (d = hmb) then ((empty)) else (if (d = bmh) then ((empty)) else ((nodiag b d1 t)))))).
constraints:
~arg1[]
~arg2[]
~b[1,3,3,2,0,2]
~b[1,3,3,2]
~bmh[1,3,3,2,0,0,0]
~bmh[1,3,3,2,0]
~bmh[1,3,3,2]
~d1[1,3,3,2,0,2]
~d1[1,3,3,2]
~d[1,3,3,0,0]
~d[1,3,3,2,0,0,0]
~d[1,3,3,2,0]
~d[1,3,3,2]
~hmb[1,3,3,0,0]
~hmb[1,3,3]
~t[1,3,3,2,0,2]
~t[1,3,3,2]
~(arg1[1,0] & b[1,0])
~(arg2[1,1] & d[1,1])
~(arg3[1,2,0] & h[1,2,0])
~(b[1,0] & b[1,3])
~(b[1,3,0] & b[1,3,1])
~(b[1,3,0] & b[1,3,3])
~(b[1,3,1] & b[1,3,3])
~(bmh[1,3,1] & bmh[1,3,3])
~(d1[1,3,2] & d1[1,3,3])
~(d[1,1] & d[1,3])
~(d[1,3,2] & d[1,3,3])
~(d[1,3,3,0,0] & hmb[1,3,3,0,0])
~(d[1,3,3,2,0,0,0] & bmh[1,3,3,2,0,0,0])
~(h[1,2] & h[1,3])
~(h[1,3,0] & h[1,3,1])
~(hmb[1,3,0] & hmb[1,3,3])
~(t[1,2] & t[1,3])
(b[1,0] | b[1,3])
(bmh[1,3,1] | bmh[1,3,3])
(d1[1,3,2] | d1[1,3,3])
(d[1,1] | d[1,3])
(h[1,2] | h[1,3])
(hmb[1,3,0] | hmb[1,3,3])
(t[1,2] | t[1,3])
((bmh[1,3,1,0] & (~h[1,3,1,0] & ~b[1,3,1,0])) | ((~bmh[1,3,1,0] & (h[1,3,1,0] & ~b[1,3,1,0])) | (~bmh[1,3,1,0] & (~h[1,3,1,0] & b[1,3,1,0]))))
((d[1,3,2,0] & ~d1[1,3,2,0]) | ((~d[1,3,2,0] & d1[1,3,2,0]) | (~d[1,3,2,0] & ~d1[1,3,2,0])))
((hmb[1,3,0,0] & (~b[1,3,0,0] & ~h[1,3,0,0])) | ((~hmb[1,3,0,0] & (b[1,3,0,0] & ~h[1,3,0,0])) | (~hmb[1,3,0,0] & (~b[1,3,0,0] & h[1,3,0,0]))))
(arg1[1] <-> arg1[1,0])
(arg1[] <-> arg1[1])
(arg2[1] <-> arg2[1,1])
(arg2[] <-> arg2[1])
(arg3[0,0] <-> arg3[0,0,0])
(arg3[0] <-> arg3[0,0])
(arg3[1,2] <-> arg3[1,2,0])
(arg3[1] <-> arg3[1,2])
(arg3[] <-> arg3[0])
(arg3[] <-> arg3[1])
(b[1,3,0] <-> b[1,3,0,0])
(b[1,3,1] <-> b[1,3,1,0])
(b[1,3,3,2,0,2,0,0] <-> arg1[])
(b[1,3,3,2,0,2,0] <-> b[1,3,3,2,0,2,0,0])
(b[1,3,3,2,0,2] <-> b[1,3,3,2,0,2,0])
(b[1,3,3,2,0] <-> b[1,3,3,2,0,2])
(b[1,3,3,2] <-> b[1,3,3,2,0])
(b[1,3,3] <-> b[1,3,3,2])
(b[1,3] <-> (b[1,3,0] | (b[1,3,1] | b[1,3,3])))
(bmh[1,3,1] <-> bmh[1,3,1,0])
(bmh[1,3,3,2] <-> bmh[1,3,3,2,0])
(bmh[1,3,3] <-> bmh[1,3,3,2])
(d1[1,3,2] <-> d1[1,3,2,0])
(d1[1,3,3,2,0,2,0,0] <-> arg2[])
(d1[1,3,3,2,0,2,0] <-> d1[1,3,3,2,0,2,0,0])
(d1[1,3,3,2,0,2] <-> d1[1,3,3,2,0,2,0])
(d1[1,3,3,2,0] <-> d1[1,3,3,2,0,2])
(d1[1,3,3,2] <-> d1[1,3,3,2,0])
(d1[1,3,3] <-> d1[1,3,3,2])
(d[1,3,2] <-> d[1,3,2,0])
(d[1,3,3,2] <-> d[1,3,3,2,0])
(d[1,3,3] <-> d[1,3,3,2])
(d[1,3] <-> (d[1,3,2] | d[1,3,3]))
(h[1,2,0] <-> t[1,2,0])
(h[1,2] <-> h[1,2,0])
(h[1,3,0] <-> h[1,3,0,0])
(h[1,3,1] <-> h[1,3,1,0])
(h[1,3] <-> (h[1,3,0] | h[1,3,1]))
(hmb[1,3,0] <-> hmb[1,3,0,0])
(t[1,2] <-> t[1,2,0])
(t[1,3,3,2,0,2,0,0] <-> arg3[])
(t[1,3,3,2,0,2,0] <-> t[1,3,3,2,0,2,0,0])
(t[1,3,3,2,0,2] <-> t[1,3,3,2,0,2,0])
(t[1,3,3,2,0] <-> t[1,3,3,2,0,2])
(t[1,3,3,2] <-> t[1,3,3,2,0])
(t[1,3,3] <-> t[1,3,3,2])
(t[1,3] <-> t[1,3,3])
1
-}
nodiag_iii arg1 arg2 arg3 = do
  -- solution: b[1,0] bmh[1,3,1,0] bmh[1,3,1] d1[1,3,2,0] d1[1,3,2] d[1,1] h[1,2,0] h[1,2] hmb[1,3,0,0] hmb[1,3,0] t[1,2,0] t[1,2] ~arg1[1,0] ~arg1[1] ~arg1[] ~arg2[1,1] ~arg2[1] ~arg2[] ~arg3[0,0,0] ~arg3[0,0] ~arg3[0] ~arg3[1,2,0] ~arg3[1,2] ~arg3[1] ~arg3[] ~b[1,3,0,0] ~b[1,3,0] ~b[1,3,1,0] ~b[1,3,1] ~b[1,3,3,2,0,2,0,0] ~b[1,3,3,2,0,2,0] ~b[1,3,3,2,0,2] ~b[1,3,3,2,0] ~b[1,3,3,2] ~b[1,3,3] ~b[1,3] ~bmh[1,3,3,2,0,0,0] ~bmh[1,3,3,2,0] ~bmh[1,3,3,2] ~bmh[1,3,3] ~d1[1,3,3,2,0,2,0,0] ~d1[1,3,3,2,0,2,0] ~d1[1,3,3,2,0,2] ~d1[1,3,3,2,0] ~d1[1,3,3,2] ~d1[1,3,3] ~d[1,3,2,0] ~d[1,3,2] ~d[1,3,3,0,0] ~d[1,3,3,2,0,0,0] ~d[1,3,3,2,0] ~d[1,3,3,2] ~d[1,3,3] ~d[1,3] ~h[1,3,0,0] ~h[1,3,0] ~h[1,3,1,0] ~h[1,3,1] ~h[1,3] ~hmb[1,3,3,0,0] ~hmb[1,3,3] ~t[1,3,3,2,0,2,0,0] ~t[1,3,3,2,0,2,0] ~t[1,3,3,2,0,2] ~t[1,3,3,2,0] ~t[1,3,3,2] ~t[1,3,3] ~t[1,3]
  () <- (do
    () <- (do
      guard $ arg3 == []
      pure ()
     )
    () <- (do
      
      pure ()
     )
    pure ()
   ) <|> (do
    b <- pure arg1
    d <- pure arg2
    (h,t) <- (do
      (h:t) <- pure arg3
      pure (h,t)
     )
    () <- (do
      (hmb) <- (do
        (hmb) <- plus_oii b h
        pure (hmb)
       )
      (bmh) <- (do
        (bmh) <- plus_oii h b
        pure (bmh)
       )
      (d1) <- (do
        (d1) <- succ_io d
        pure (d1)
       )
      () <- ifte ((do
        guard $ d == hmb
        pure ()
       )) (\() -> (do
        () <- (do
          () <- empty 
          pure ()
         )
        pure ()
       )) ((do
        () <- ifte ((do
          guard $ d == bmh
          pure ()
         )) (\() -> (do
          () <- (do
            () <- empty 
            pure ()
           )
          pure ()
         )) ((do
          () <- (do
            () <- nodiag_iii b d1 t
            pure ()
           )
          pure ()
         ))
        pure ()
       ))
      pure ()
     )
    pure ()
   )
  pure ()

{- cqueens/3
cqueens arg1 arg2 arg3 :- (((arg1 = []), (arg3 = []), ()); (arg1 = xs, arg2 = history, (arg3 = q0 : m, q0 = q), ((xs = _ : _), (delete q xs r), ((nodiag q data0 history), (data0 = 1)), ((cqueens r data1 m), (data1 = q1 : history, q1 = q))))).
constraints:
~arg2[]
~xs[1,3,0,0]
~(arg1[1,0] & xs[1,0])
~(arg2[1,1] & history[1,1])
~(arg3[1,2,0] & q0[1,2,0])
~(data0[1,3,2,0] & data0[1,3,2,1])
~(data1[1,3,3,0] & data1[1,3,3,1])
~(data1[1,3,3,1,0] & q1[1,3,3,1,0])
~(history[1,1] & history[1,3])
~(history[1,3,2] & history[1,3,3])
~(m[1,2] & m[1,3])
~(q0[1,2,0] & q0[1,2,1])
~(q0[1,2,1] & q[1,2,1])
~(q1[1,3,3,1,0] & q1[1,3,3,1,1])
~(q1[1,3,3,1,1] & q[1,3,3,1,1])
~(q[1,2] & q[1,3])
~(q[1,3,1] & q[1,3,2])
~(q[1,3,1] & q[1,3,3])
~(q[1,3,2] & q[1,3,3])
~(r[1,3,1] & r[1,3,3])
~(xs[1,0] & xs[1,3])
~(xs[1,3,0] & xs[1,3,1])
(~q[1,3,2,0,0] & (~data0[1,3,2,0,0] & ~history[1,3,2,0,0]))
(data0[1,3,2,0] | data0[1,3,2,1])
(data1[1,3,3,0] | data1[1,3,3,1])
(history[1,1] | history[1,3])
(m[1,2] | m[1,3])
(q0[1,2,0] | q0[1,2,1])
(q1[1,3,3,1,0] | q1[1,3,3,1,1])
(q[1,2] | q[1,3])
(r[1,3,1] | r[1,3,3])
(xs[1,0] | xs[1,3])
((q[1,3,1,0] & (~xs[1,3,1,0] & r[1,3,1,0])) | ((q[1,3,1,0] & (~xs[1,3,1,0] & ~r[1,3,1,0])) | ((~q[1,3,1,0] & (xs[1,3,1,0] & ~r[1,3,1,0])) | ((~q[1,3,1,0] & (~xs[1,3,1,0] & r[1,3,1,0])) | (~q[1,3,1,0] & (~xs[1,3,1,0] & ~r[1,3,1,0]))))))
(arg1[0,0] <-> arg1[0,0,0])
(arg1[0] <-> arg1[0,0])
(arg1[1] <-> arg1[1,0])
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg2[1] <-> arg2[1,1])
(arg2[] <-> arg2[1])
(arg3[0,1] <-> arg3[0,1,0])
(arg3[0] <-> arg3[0,1])
(arg3[1,2] <-> arg3[1,2,0])
(arg3[1] <-> arg3[1,2])
(arg3[] <-> arg3[0])
(arg3[] <-> arg3[1])
(data0[1,3,2,0] <-> data0[1,3,2,0,0])
(data0[1,3,2,1] <-> data0[1,3,2,1,0])
(data1[1,3,3,0,0] <-> arg2[])
(data1[1,3,3,0] <-> data1[1,3,3,0,0])
(data1[1,3,3,1] <-> data1[1,3,3,1,0])
(history[1,3,2,0] <-> history[1,3,2,0,0])
(history[1,3,2] <-> history[1,3,2,0])
(history[1,3,3,1] <-> history[1,3,3,1,0])
(history[1,3,3] <-> history[1,3,3,1])
(history[1,3] <-> (history[1,3,2] | history[1,3,3]))
(m[1,2] <-> m[1,2,0])
(m[1,3,3,0,0] <-> arg3[])
(m[1,3,3,0] <-> m[1,3,3,0,0])
(m[1,3,3] <-> m[1,3,3,0])
(m[1,3] <-> m[1,3,3])
(q0[1,2,0] <-> m[1,2,0])
(q1[1,3,3,1,0] <-> history[1,3,3,1,0])
(q[1,2] <-> q[1,2,1])
(q[1,3,1] <-> q[1,3,1,0])
(q[1,3,2,0] <-> q[1,3,2,0,0])
(q[1,3,2] <-> q[1,3,2,0])
(q[1,3,3,1] <-> q[1,3,3,1,1])
(q[1,3,3] <-> q[1,3,3,1])
(q[1,3] <-> (q[1,3,1] | (q[1,3,2] | q[1,3,3])))
(r[1,3,1] <-> r[1,3,1,0])
(r[1,3,3,0,0] <-> arg1[])
(r[1,3,3,0] <-> r[1,3,3,0,0])
(r[1,3,3] <-> r[1,3,3,0])
(xs[1,3,0] <-> xs[1,3,0,0])
(xs[1,3,1] <-> xs[1,3,1,0])
(xs[1,3] <-> (xs[1,3,0] | xs[1,3,1]))
1
-}
-- mode ordering failure, cyclic dependency: [3] ((xs::in = _::out : _::out), (delete q::out xs::in r::out), ((data0::out = 1), (nodiag q::in data0::in history::in)), ((q1::out = q::in, data1::out = q1::in : history::in), (cqueens r::in data1::in m::in))) -> [2] (arg3::in = q0::out : m::out, q0::in = q::in)
cqueens_iii arg1 arg2 arg3 = do
  -- solution: data0[1,3,2,1,0] data0[1,3,2,1] data1[1,3,3,1,0] data1[1,3,3,1] history[1,1] m[1,2,0] m[1,2] q0[1,2,0] q1[1,3,3,1,1] q[1,2,1] q[1,2] r[1,3,1,0] r[1,3,1] xs[1,0] ~arg1[0,0,0] ~arg1[0,0] ~arg1[0] ~arg1[1,0] ~arg1[1] ~arg1[] ~arg2[1,1] ~arg2[1] ~arg2[] ~arg3[0,1,0] ~arg3[0,1] ~arg3[0] ~arg3[1,2,0] ~arg3[1,2] ~arg3[1] ~arg3[] ~data0[1,3,2,0,0] ~data0[1,3,2,0] ~data1[1,3,3,0,0] ~data1[1,3,3,0] ~history[1,3,2,0,0] ~history[1,3,2,0] ~history[1,3,2] ~history[1,3,3,1,0] ~history[1,3,3,1] ~history[1,3,3] ~history[1,3] ~m[1,3,3,0,0] ~m[1,3,3,0] ~m[1,3,3] ~m[1,3] ~q0[1,2,1] ~q1[1,3,3,1,0] ~q[1,3,1,0] ~q[1,3,1] ~q[1,3,2,0,0] ~q[1,3,2,0] ~q[1,3,2] ~q[1,3,3,1,1] ~q[1,3,3,1] ~q[1,3,3] ~q[1,3] ~r[1,3,3,0,0] ~r[1,3,3,0] ~r[1,3,3] ~xs[1,3,0,0] ~xs[1,3,0] ~xs[1,3,1,0] ~xs[1,3,1] ~xs[1,3]
  () <- (do
    () <- (do
      guard $ arg1 == []
      pure ()
     )
    () <- (do
      guard $ arg3 == []
      pure ()
     )
    () <- (do
      
      pure ()
     )
    pure ()
   ) <|> (do
    xs <- pure arg1
    history <- pure arg2
    (m,q) <- (do
      (q0:m) <- pure arg3
      q <- pure q0
      pure (m,q)
     )
    () <- (do
      () <- (do
        (_:_) <- pure xs
        pure ()
       )
      (r) <- (do
        (r) <- delete_iio q xs
        pure (r)
       )
      () <- (do
        (data0) <- (do
          data0 <- pure 1
          pure (data0)
         )
        () <- (do
          () <- nodiag_iii q data0 history
          pure ()
         )
        pure ()
       )
      () <- (do
        (data1) <- (do
          q1 <- pure q
          data1 <- pure (q1:history)
          pure (data1)
         )
        () <- (do
          () <- cqueens_iii r data1 m
          pure ()
         )
        pure ()
       )
      pure ()
     )
    pure ()
   )
  pure ()

cqueens_iio arg1 arg2 = do
  -- solution: arg3[0,1,0] arg3[0,1] arg3[0] arg3[1,2,0] arg3[1,2] arg3[1] arg3[] data0[1,3,2,1,0] data0[1,3,2,1] data1[1,3,3,1,0] data1[1,3,3,1] history[1,1] m[1,3,3,0,0] m[1,3,3,0] m[1,3,3] m[1,3] q0[1,2,1] q1[1,3,3,1,1] q[1,3,1,0] q[1,3,1] q[1,3] r[1,3,1,0] r[1,3,1] xs[1,0] ~arg1[0,0,0] ~arg1[0,0] ~arg1[0] ~arg1[1,0] ~arg1[1] ~arg1[] ~arg2[1,1] ~arg2[1] ~arg2[] ~data0[1,3,2,0,0] ~data0[1,3,2,0] ~data1[1,3,3,0,0] ~data1[1,3,3,0] ~history[1,3,2,0,0] ~history[1,3,2,0] ~history[1,3,2] ~history[1,3,3,1,0] ~history[1,3,3,1] ~history[1,3,3] ~history[1,3] ~m[1,2,0] ~m[1,2] ~q0[1,2,0] ~q1[1,3,3,1,0] ~q[1,2,1] ~q[1,2] ~q[1,3,2,0,0] ~q[1,3,2,0] ~q[1,3,2] ~q[1,3,3,1,1] ~q[1,3,3,1] ~q[1,3,3] ~r[1,3,3,0,0] ~r[1,3,3,0] ~r[1,3,3] ~xs[1,3,0,0] ~xs[1,3,0] ~xs[1,3,1,0] ~xs[1,3,1] ~xs[1,3]
  (arg3) <- (do
    () <- (do
      guard $ arg1 == []
      pure ()
     )
    (arg3) <- (do
      arg3 <- pure []
      pure (arg3)
     )
    () <- (do
      
      pure ()
     )
    pure (arg3)
   ) <|> (do
    xs <- pure arg1
    history <- pure arg2
    (m,q) <- (do
      () <- (do
        (_:_) <- pure xs
        pure ()
       )
      (q,r) <- (do
        (q,r) <- delete_oio xs
        pure (q,r)
       )
      () <- (do
        (data0) <- (do
          data0 <- pure 1
          pure (data0)
         )
        () <- (do
          () <- nodiag_iii q data0 history
          pure ()
         )
        pure ()
       )
      (m) <- (do
        (data1) <- (do
          q1 <- pure q
          data1 <- pure (q1:history)
          pure (data1)
         )
        (m) <- (do
          (m) <- cqueens_iio r data1
          pure (m)
         )
        pure (m)
       )
      pure (m,q)
     )
    (arg3) <- (do
      q0 <- pure q
      arg3 <- pure (q0:m)
      pure (arg3)
     )
    pure (arg3)
   )
  pure (arg3)

cqueens_oii arg2 arg3 = do
  -- solution: arg1[0,0,0] arg1[0,0] arg1[0] arg1[1,0] arg1[1] arg1[] data0[1,3,2,1,0] data0[1,3,2,1] data1[1,3,3,1,0] data1[1,3,3,1] history[1,1] m[1,2,0] m[1,2] q0[1,2,0] q1[1,3,3,1,1] q[1,2,1] q[1,2] r[1,3,3,0,0] r[1,3,3,0] r[1,3,3] xs[1,3,1,0] xs[1,3,1] xs[1,3] ~arg2[1,1] ~arg2[1] ~arg2[] ~arg3[0,1,0] ~arg3[0,1] ~arg3[0] ~arg3[1,2,0] ~arg3[1,2] ~arg3[1] ~arg3[] ~data0[1,3,2,0,0] ~data0[1,3,2,0] ~data1[1,3,3,0,0] ~data1[1,3,3,0] ~history[1,3,2,0,0] ~history[1,3,2,0] ~history[1,3,2] ~history[1,3,3,1,0] ~history[1,3,3,1] ~history[1,3,3] ~history[1,3] ~m[1,3,3,0,0] ~m[1,3,3,0] ~m[1,3,3] ~m[1,3] ~q0[1,2,1] ~q1[1,3,3,1,0] ~q[1,3,1,0] ~q[1,3,1] ~q[1,3,2,0,0] ~q[1,3,2,0] ~q[1,3,2] ~q[1,3,3,1,1] ~q[1,3,3,1] ~q[1,3,3] ~q[1,3] ~r[1,3,1,0] ~r[1,3,1] ~xs[1,0] ~xs[1,3,0,0] ~xs[1,3,0]
  (arg1) <- (do
    (arg1) <- (do
      arg1 <- pure []
      pure (arg1)
     )
    () <- (do
      guard $ arg3 == []
      pure ()
     )
    () <- (do
      
      pure ()
     )
    pure (arg1)
   ) <|> (do
    history <- pure arg2
    (m,q) <- (do
      (q0:m) <- pure arg3
      q <- pure q0
      pure (m,q)
     )
    (xs) <- (do
      () <- (do
        (data0) <- (do
          data0 <- pure 1
          pure (data0)
         )
        () <- (do
          () <- nodiag_iii q data0 history
          pure ()
         )
        pure ()
       )
      (r) <- (do
        (data1) <- (do
          q1 <- pure q
          data1 <- pure (q1:history)
          pure (data1)
         )
        (r) <- (do
          (r) <- cqueens_oii data1 m
          pure (r)
         )
        pure (r)
       )
      (xs) <- (do
        (xs) <- delete_ioi q r
        pure (xs)
       )
      () <- (do
        (_:_) <- pure xs
        pure ()
       )
      pure (xs)
     )
    arg1 <- pure xs
    pure (arg1)
   )
  pure (arg1)

{- queens/2
queens arg1 arg2 :- ((arg1 = dat, arg2 = out, (((cqueens dat data0 out), (data0 = []))))).
constraints:
~(arg1[0,0] & dat[0,0])
~(arg2[0,1] & out[0,1])
~(dat[0,0] & dat[0,2])
~(data0[0,2,0,0] & data0[0,2,0,1])
~(out[0,1] & out[0,2])
(dat[0,0] | dat[0,2])
(data0[0,2,0,0] | data0[0,2,0,1])
(out[0,1] | out[0,2])
((dat[0,2,0,0,0] & (~data0[0,2,0,0,0] & ~out[0,2,0,0,0])) | ((~dat[0,2,0,0,0] & (~data0[0,2,0,0,0] & out[0,2,0,0,0])) | (~dat[0,2,0,0,0] & (~data0[0,2,0,0,0] & ~out[0,2,0,0,0]))))
(arg1[0] <-> arg1[0,0])
(arg1[] <-> arg1[0])
(arg2[0] <-> arg2[0,1])
(arg2[] <-> arg2[0])
(dat[0,2,0,0] <-> dat[0,2,0,0,0])
(dat[0,2,0] <-> dat[0,2,0,0])
(dat[0,2] <-> dat[0,2,0])
(data0[0,2,0,0] <-> data0[0,2,0,0,0])
(data0[0,2,0,1] <-> data0[0,2,0,1,0])
(out[0,2,0,0] <-> out[0,2,0,0,0])
(out[0,2,0] <-> out[0,2,0,0])
(out[0,2] <-> out[0,2,0])
1
-}
queens_ii arg1 arg2 = do
  -- solution: dat[0,0] data0[0,2,0,1,0] data0[0,2,0,1] out[0,1] ~arg1[0,0] ~arg1[0] ~arg1[] ~arg2[0,1] ~arg2[0] ~arg2[] ~dat[0,2,0,0,0] ~dat[0,2,0,0] ~dat[0,2,0] ~dat[0,2] ~data0[0,2,0,0,0] ~data0[0,2,0,0] ~out[0,2,0,0,0] ~out[0,2,0,0] ~out[0,2,0] ~out[0,2]
  () <- (do
    dat <- pure arg1
    out <- pure arg2
    () <- (do
      () <- (do
        (data0) <- (do
          data0 <- pure []
          pure (data0)
         )
        () <- (do
          () <- cqueens_iii dat data0 out
          pure ()
         )
        pure ()
       )
      pure ()
     )
    pure ()
   )
  pure ()

--queens_ii arg1 arg2 = do
--  -- solution: dat[0,0] data0[0,2,0,1,0] data0[0,2,0,1] out[0,2,0,0,0] out[0,2,0,0] out[0,2,0] out[0,2] ~arg1[0,0] ~arg1[0] ~arg1[] ~arg2[0,1] ~arg2[0] ~arg2[] ~dat[0,2,0,0,0] ~dat[0,2,0,0] ~dat[0,2,0] ~dat[0,2] ~data0[0,2,0,0,0] ~data0[0,2,0,0] ~out[0,1]
--  () <- (do
--    dat <- pure arg1
--    (out) <- (do
--      (out) <- (do
--        (data0) <- (do
--          data0 <- pure []
--          pure (data0)
--         )
--        (out) <- (do
--          (out) <- cqueens_iio dat data0
--          pure (out)
--         )
--        pure (out)
--       )
--      pure (out)
--     )
--    guard $ arg2 == out
--    pure ()
--   )
--  pure ()

--queens_ii arg1 arg2 = do
--  -- solution: dat[0,2,0,0,0] dat[0,2,0,0] dat[0,2,0] dat[0,2] data0[0,2,0,1,0] data0[0,2,0,1] out[0,1] ~arg1[0,0] ~arg1[0] ~arg1[] ~arg2[0,1] ~arg2[0] ~arg2[] ~dat[0,0] ~data0[0,2,0,0,0] ~data0[0,2,0,0] ~out[0,2,0,0,0] ~out[0,2,0,0] ~out[0,2,0] ~out[0,2]
--  () <- (do
--    out <- pure arg2
--    (dat) <- (do
--      (dat) <- (do
--        (data0) <- (do
--          data0 <- pure []
--          pure (data0)
--         )
--        (dat) <- (do
--          (dat) <- cqueens_oii data0 out
--          pure (dat)
--         )
--        pure (dat)
--       )
--      pure (dat)
--     )
--    guard $ arg1 == dat
--    pure ()
--   )
--  pure ()

queens_io arg1 = do
  -- solution: arg2[0,1] arg2[0] arg2[] dat[0,0] data0[0,2,0,1,0] data0[0,2,0,1] out[0,2,0,0,0] out[0,2,0,0] out[0,2,0] out[0,2] ~arg1[0,0] ~arg1[0] ~arg1[] ~dat[0,2,0,0,0] ~dat[0,2,0,0] ~dat[0,2,0] ~dat[0,2] ~data0[0,2,0,0,0] ~data0[0,2,0,0] ~out[0,1]
  (arg2) <- (do
    dat <- pure arg1
    (out) <- (do
      (out) <- (do
        (data0) <- (do
          data0 <- pure []
          pure (data0)
         )
        (out) <- (do
          (out) <- cqueens_iio dat data0
          pure (out)
         )
        pure (out)
       )
      pure (out)
     )
    arg2 <- pure out
    pure (arg2)
   )
  pure (arg2)

queens_oi arg2 = do
  -- solution: arg1[0,0] arg1[0] arg1[] dat[0,2,0,0,0] dat[0,2,0,0] dat[0,2,0] dat[0,2] data0[0,2,0,1,0] data0[0,2,0,1] out[0,1] ~arg2[0,1] ~arg2[0] ~arg2[] ~dat[0,0] ~data0[0,2,0,0,0] ~data0[0,2,0,0] ~out[0,2,0,0,0] ~out[0,2,0,0] ~out[0,2,0] ~out[0,2]
  (arg1) <- (do
    out <- pure arg2
    (dat) <- (do
      (dat) <- (do
        (data0) <- (do
          data0 <- pure []
          pure (data0)
         )
        (dat) <- (do
          (dat) <- cqueens_oii data0 out
          pure (dat)
         )
        pure (dat)
       )
      pure (dat)
     )
    arg1 <- pure dat
    pure (arg1)
   )
  pure (arg1)
