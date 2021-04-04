module Append where
import Control.Applicative
import Control.Monad.Logic

{- append/3
append arg1 arg2 arg3 :- (((arg1 = []), arg2 = b, arg3 = b, ()); ((arg1 = h0 : t, h0 = h), arg2 = b, (arg3 = h1 : tb, h1 = h), ((append t b tb)))).
constraints:
b[0]
b[1]
b[]
h0[1,0]
h0[1]
h0[]
h1[1,2]
h1[1]
h1[]
h[1]
h[]
t[1]
t[]
tb[1]
tb[]
~arg1[0,1]
~arg1[0,2]
~arg1[0,3]
~arg1[1,0,1]
~arg1[1,1]
~arg1[1,2]
~arg1[1,3]
~arg2[0,0]
~arg2[0,2]
~arg2[0,3]
~arg2[1,0]
~arg2[1,2]
~arg2[1,3]
~arg3[0,0]
~arg3[0,1]
~arg3[0,3]
~arg3[1,0]
~arg3[1,1]
~arg3[1,2,1]
~arg3[1,3]
~b[0,0]
~b[0,3]
~b[1,0]
~b[1,2]
~h0[0]
~h0[1,1]
~h0[1,2]
~h0[1,3]
~h1[0]
~h1[1,0]
~h1[1,1]
~h1[1,3]
~h[0]
~h[1,0,0]
~h[1,1]
~h[1,2,0]
~h[1,3]
~t[0]
~t[1,0,1]
~t[1,1]
~t[1,2]
~tb[0]
~tb[1,0]
~tb[1,1]
~tb[1,2,1]
~(arg1[1,0,0] & h0[1,0,0])
~(arg2[0,1] & b[0,1])
~(arg2[1,1] & b[1,1])
~(arg3[0,2] & b[0,2])
~(arg3[1,2,0] & h1[1,2,0])
~(b[0,1] & b[0,2])
~(b[1,1] & b[1,3])
~(h0[1,0,0] & h0[1,0,1])
~(h0[1,0,1] & h[1,0,1])
~(h1[1,2,0] & h1[1,2,1])
~(h1[1,2,1] & h[1,2,1])
~(h[1,0] & h[1,2])
~(t[1,0] & t[1,3])
~(tb[1,2] & tb[1,3])
(arg1[0,0] <-> arg1[0,0,0])
(arg1[0] <-> arg1[0,0])
(arg1[1,0] <-> arg1[1,0,0])
(arg1[1] <-> arg1[1,0])
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg2[0] <-> arg2[0,1])
(arg2[1] <-> arg2[1,1])
(arg2[] <-> arg2[0])
(arg2[] <-> arg2[1])
(arg3[0] <-> arg3[0,2])
(arg3[1,2] <-> arg3[1,2,0])
(arg3[1] <-> arg3[1,2])
(arg3[] <-> arg3[0])
(arg3[] <-> arg3[1])
(b[0] <-> (b[0,1] | b[0,2]))
(b[1,3,0,0] <-> arg2[])
(b[1,3,0] <-> b[1,3,0,0])
(b[1,3] <-> b[1,3,0])
(b[1] <-> (b[1,1] | b[1,3]))
(h0[1,0,0] <-> t[1,0,0])
(h0[1,0] <-> (h0[1,0,0] | h0[1,0,1]))
(h0[1] <-> h0[1,0])
(h1[1,2,0] <-> tb[1,2,0])
(h1[1,2] <-> (h1[1,2,0] | h1[1,2,1]))
(h1[1] <-> h1[1,2])
(h[1,0] <-> h[1,0,1])
(h[1,2] <-> h[1,2,1])
(h[1] <-> (h[1,0] | h[1,2]))
(t[1,0] <-> t[1,0,0])
(t[1,3,0,0] <-> arg1[])
(t[1,3,0] <-> t[1,3,0,0])
(t[1,3] <-> t[1,3,0])
(t[1] <-> (t[1,0] | t[1,3]))
(tb[1,2] <-> tb[1,2,0])
(tb[1,3,0,0] <-> arg3[])
(tb[1,3,0] <-> tb[1,3,0,0])
(tb[1,3] <-> tb[1,3,0])
(tb[1] <-> (tb[1,2] | tb[1,3]))
-}
append_iii arg1 arg2 arg3 = do
  -- solution: b[0,1] b[0] b[1,1] b[1] b[] h0[1,0,0] h0[1,0] h0[1] h0[] h1[1,2,0] h1[1,2] h1[1] h1[] h[1,0,1] h[1,0] h[1] h[] t[1,0,0] t[1,0] t[1] t[] tb[1,2,0] tb[1,2] tb[1] tb[] ~arg1[0,0,0] ~arg1[0,0] ~arg1[0,1] ~arg1[0,2] ~arg1[0,3] ~arg1[0] ~arg1[1,0,0] ~arg1[1,0,1] ~arg1[1,0] ~arg1[1,1] ~arg1[1,2] ~arg1[1,3] ~arg1[1] ~arg1[] ~arg2[0,0] ~arg2[0,1] ~arg2[0,2] ~arg2[0,3] ~arg2[0] ~arg2[1,0] ~arg2[1,1] ~arg2[1,2] ~arg2[1,3] ~arg2[1] ~arg2[] ~arg3[0,0] ~arg3[0,1] ~arg3[0,2] ~arg3[0,3] ~arg3[0] ~arg3[1,0] ~arg3[1,1] ~arg3[1,2,0] ~arg3[1,2,1] ~arg3[1,2] ~arg3[1,3] ~arg3[1] ~arg3[] ~b[0,0] ~b[0,2] ~b[0,3] ~b[1,0] ~b[1,2] ~b[1,3,0,0] ~b[1,3,0] ~b[1,3] ~h0[0] ~h0[1,0,1] ~h0[1,1] ~h0[1,2] ~h0[1,3] ~h1[0] ~h1[1,0] ~h1[1,1] ~h1[1,2,1] ~h1[1,3] ~h[0] ~h[1,0,0] ~h[1,1] ~h[1,2,0] ~h[1,2,1] ~h[1,2] ~h[1,3] ~t[0] ~t[1,0,1] ~t[1,1] ~t[1,2] ~t[1,3,0,0] ~t[1,3,0] ~t[1,3] ~tb[0] ~tb[1,0] ~tb[1,1] ~tb[1,2,1] ~tb[1,3,0,0] ~tb[1,3,0] ~tb[1,3]
  () <- (do
    () <- (do
      guard $ arg1 == []
      pure ()
     )
    b <- pure arg2
    guard $ arg3 == b
    () <- (do
      
      pure ()
     )
    pure ()
   ) <|> (do
    (h,t) <- (do
      (h0:t) <- pure arg1
      h <- pure h0
      pure (h,t)
     )
    b <- pure arg2
    (tb) <- (do
      (h1:tb) <- pure arg3
      guard $ h1 == h
      pure (tb)
     )
    () <- (do
      () <- (do
        () <- append_iii t b tb
        pure ()
       )
      pure ()
     )
    pure ()
   )
  pure ()

--append_iii arg1 arg2 arg3 = do
--  -- solution: b[0,1] b[0] b[1,1] b[1] b[] h0[1,0,0] h0[1,0] h0[1] h0[] h1[1,2,0] h1[1,2] h1[1] h1[] h[1,2,1] h[1,2] h[1] h[] t[1,0,0] t[1,0] t[1] t[] tb[1,2,0] tb[1,2] tb[1] tb[] ~arg1[0,0,0] ~arg1[0,0] ~arg1[0,1] ~arg1[0,2] ~arg1[0,3] ~arg1[0] ~arg1[1,0,0] ~arg1[1,0,1] ~arg1[1,0] ~arg1[1,1] ~arg1[1,2] ~arg1[1,3] ~arg1[1] ~arg1[] ~arg2[0,0] ~arg2[0,1] ~arg2[0,2] ~arg2[0,3] ~arg2[0] ~arg2[1,0] ~arg2[1,1] ~arg2[1,2] ~arg2[1,3] ~arg2[1] ~arg2[] ~arg3[0,0] ~arg3[0,1] ~arg3[0,2] ~arg3[0,3] ~arg3[0] ~arg3[1,0] ~arg3[1,1] ~arg3[1,2,0] ~arg3[1,2,1] ~arg3[1,2] ~arg3[1,3] ~arg3[1] ~arg3[] ~b[0,0] ~b[0,2] ~b[0,3] ~b[1,0] ~b[1,2] ~b[1,3,0,0] ~b[1,3,0] ~b[1,3] ~h0[0] ~h0[1,0,1] ~h0[1,1] ~h0[1,2] ~h0[1,3] ~h1[0] ~h1[1,0] ~h1[1,1] ~h1[1,2,1] ~h1[1,3] ~h[0] ~h[1,0,0] ~h[1,0,1] ~h[1,0] ~h[1,1] ~h[1,2,0] ~h[1,3] ~t[0] ~t[1,0,1] ~t[1,1] ~t[1,2] ~t[1,3,0,0] ~t[1,3,0] ~t[1,3] ~tb[0] ~tb[1,0] ~tb[1,1] ~tb[1,2,1] ~tb[1,3,0,0] ~tb[1,3,0] ~tb[1,3]
--  () <- (do
--    () <- (do
--      guard $ arg1 == []
--      pure ()
--     )
--    b <- pure arg2
--    guard $ arg3 == b
--    () <- (do
--      
--      pure ()
--     )
--    pure ()
--   ) <|> (do
--    b <- pure arg2
--    (h,tb) <- (do
--      (h1:tb) <- pure arg3
--      h <- pure h1
--      pure (h,tb)
--     )
--    (t) <- (do
--      (h0:t) <- pure arg1
--      guard $ h0 == h
--      pure (t)
--     )
--    () <- (do
--      () <- (do
--        () <- append_iii t b tb
--        pure ()
--       )
--      pure ()
--     )
--    pure ()
--   )
--  pure ()

--append_iii arg1 arg2 arg3 = do
--  -- solution: b[0,2] b[0] b[1,1] b[1] b[] h0[1,0,0] h0[1,0] h0[1] h0[] h1[1,2,0] h1[1,2] h1[1] h1[] h[1,0,1] h[1,0] h[1] h[] t[1,0,0] t[1,0] t[1] t[] tb[1,2,0] tb[1,2] tb[1] tb[] ~arg1[0,0,0] ~arg1[0,0] ~arg1[0,1] ~arg1[0,2] ~arg1[0,3] ~arg1[0] ~arg1[1,0,0] ~arg1[1,0,1] ~arg1[1,0] ~arg1[1,1] ~arg1[1,2] ~arg1[1,3] ~arg1[1] ~arg1[] ~arg2[0,0] ~arg2[0,1] ~arg2[0,2] ~arg2[0,3] ~arg2[0] ~arg2[1,0] ~arg2[1,1] ~arg2[1,2] ~arg2[1,3] ~arg2[1] ~arg2[] ~arg3[0,0] ~arg3[0,1] ~arg3[0,2] ~arg3[0,3] ~arg3[0] ~arg3[1,0] ~arg3[1,1] ~arg3[1,2,0] ~arg3[1,2,1] ~arg3[1,2] ~arg3[1,3] ~arg3[1] ~arg3[] ~b[0,0] ~b[0,1] ~b[0,3] ~b[1,0] ~b[1,2] ~b[1,3,0,0] ~b[1,3,0] ~b[1,3] ~h0[0] ~h0[1,0,1] ~h0[1,1] ~h0[1,2] ~h0[1,3] ~h1[0] ~h1[1,0] ~h1[1,1] ~h1[1,2,1] ~h1[1,3] ~h[0] ~h[1,0,0] ~h[1,1] ~h[1,2,0] ~h[1,2,1] ~h[1,2] ~h[1,3] ~t[0] ~t[1,0,1] ~t[1,1] ~t[1,2] ~t[1,3,0,0] ~t[1,3,0] ~t[1,3] ~tb[0] ~tb[1,0] ~tb[1,1] ~tb[1,2,1] ~tb[1,3,0,0] ~tb[1,3,0] ~tb[1,3]
--  () <- (do
--    () <- (do
--      guard $ arg1 == []
--      pure ()
--     )
--    b <- pure arg3
--    guard $ arg2 == b
--    () <- (do
--      
--      pure ()
--     )
--    pure ()
--   ) <|> (do
--    (h,t) <- (do
--      (h0:t) <- pure arg1
--      h <- pure h0
--      pure (h,t)
--     )
--    b <- pure arg2
--    (tb) <- (do
--      (h1:tb) <- pure arg3
--      guard $ h1 == h
--      pure (tb)
--     )
--    () <- (do
--      () <- (do
--        () <- append_iii t b tb
--        pure ()
--       )
--      pure ()
--     )
--    pure ()
--   )
--  pure ()

--append_iii arg1 arg2 arg3 = do
--  -- solution: b[0,2] b[0] b[1,1] b[1] b[] h0[1,0,0] h0[1,0] h0[1] h0[] h1[1,2,0] h1[1,2] h1[1] h1[] h[1,2,1] h[1,2] h[1] h[] t[1,0,0] t[1,0] t[1] t[] tb[1,2,0] tb[1,2] tb[1] tb[] ~arg1[0,0,0] ~arg1[0,0] ~arg1[0,1] ~arg1[0,2] ~arg1[0,3] ~arg1[0] ~arg1[1,0,0] ~arg1[1,0,1] ~arg1[1,0] ~arg1[1,1] ~arg1[1,2] ~arg1[1,3] ~arg1[1] ~arg1[] ~arg2[0,0] ~arg2[0,1] ~arg2[0,2] ~arg2[0,3] ~arg2[0] ~arg2[1,0] ~arg2[1,1] ~arg2[1,2] ~arg2[1,3] ~arg2[1] ~arg2[] ~arg3[0,0] ~arg3[0,1] ~arg3[0,2] ~arg3[0,3] ~arg3[0] ~arg3[1,0] ~arg3[1,1] ~arg3[1,2,0] ~arg3[1,2,1] ~arg3[1,2] ~arg3[1,3] ~arg3[1] ~arg3[] ~b[0,0] ~b[0,1] ~b[0,3] ~b[1,0] ~b[1,2] ~b[1,3,0,0] ~b[1,3,0] ~b[1,3] ~h0[0] ~h0[1,0,1] ~h0[1,1] ~h0[1,2] ~h0[1,3] ~h1[0] ~h1[1,0] ~h1[1,1] ~h1[1,2,1] ~h1[1,3] ~h[0] ~h[1,0,0] ~h[1,0,1] ~h[1,0] ~h[1,1] ~h[1,2,0] ~h[1,3] ~t[0] ~t[1,0,1] ~t[1,1] ~t[1,2] ~t[1,3,0,0] ~t[1,3,0] ~t[1,3] ~tb[0] ~tb[1,0] ~tb[1,1] ~tb[1,2,1] ~tb[1,3,0,0] ~tb[1,3,0] ~tb[1,3]
--  () <- (do
--    () <- (do
--      guard $ arg1 == []
--      pure ()
--     )
--    b <- pure arg3
--    guard $ arg2 == b
--    () <- (do
--      
--      pure ()
--     )
--    pure ()
--   ) <|> (do
--    b <- pure arg2
--    (h,tb) <- (do
--      (h1:tb) <- pure arg3
--      h <- pure h1
--      pure (h,tb)
--     )
--    (t) <- (do
--      (h0:t) <- pure arg1
--      guard $ h0 == h
--      pure (t)
--     )
--    () <- (do
--      () <- (do
--        () <- append_iii t b tb
--        pure ()
--       )
--      pure ()
--     )
--    pure ()
--   )
--  pure ()

append_iio arg1 arg2 = do
  -- solution: arg3[0,2] arg3[0] arg3[1,2,0] arg3[1,2] arg3[1] arg3[] b[0,1] b[0] b[1,1] b[1] b[] h0[1,0,0] h0[1,0] h0[1] h0[] h1[1,2,1] h1[1,2] h1[1] h1[] h[1,0,1] h[1,0] h[1] h[] t[1,0,0] t[1,0] t[1] t[] tb[1,3,0,0] tb[1,3,0] tb[1,3] tb[1] tb[] ~arg1[0,0,0] ~arg1[0,0] ~arg1[0,1] ~arg1[0,2] ~arg1[0,3] ~arg1[0] ~arg1[1,0,0] ~arg1[1,0,1] ~arg1[1,0] ~arg1[1,1] ~arg1[1,2] ~arg1[1,3] ~arg1[1] ~arg1[] ~arg2[0,0] ~arg2[0,1] ~arg2[0,2] ~arg2[0,3] ~arg2[0] ~arg2[1,0] ~arg2[1,1] ~arg2[1,2] ~arg2[1,3] ~arg2[1] ~arg2[] ~arg3[0,0] ~arg3[0,1] ~arg3[0,3] ~arg3[1,0] ~arg3[1,1] ~arg3[1,2,1] ~arg3[1,3] ~b[0,0] ~b[0,2] ~b[0,3] ~b[1,0] ~b[1,2] ~b[1,3,0,0] ~b[1,3,0] ~b[1,3] ~h0[0] ~h0[1,0,1] ~h0[1,1] ~h0[1,2] ~h0[1,3] ~h1[0] ~h1[1,0] ~h1[1,1] ~h1[1,2,0] ~h1[1,3] ~h[0] ~h[1,0,0] ~h[1,1] ~h[1,2,0] ~h[1,2,1] ~h[1,2] ~h[1,3] ~t[0] ~t[1,0,1] ~t[1,1] ~t[1,2] ~t[1,3,0,0] ~t[1,3,0] ~t[1,3] ~tb[0] ~tb[1,0] ~tb[1,1] ~tb[1,2,0] ~tb[1,2,1] ~tb[1,2]
  (arg3) <- (do
    () <- (do
      guard $ arg1 == []
      pure ()
     )
    b <- pure arg2
    arg3 <- pure b
    () <- (do
      
      pure ()
     )
    pure (arg3)
   ) <|> (do
    (h,t) <- (do
      (h0:t) <- pure arg1
      h <- pure h0
      pure (h,t)
     )
    b <- pure arg2
    (tb) <- (do
      (tb) <- (do
        (tb) <- append_iio t b
        pure (tb)
       )
      pure (tb)
     )
    (arg3) <- (do
      h1 <- pure h
      arg3 <- pure (h1:tb)
      pure (arg3)
     )
    pure (arg3)
   )
  pure (arg3)

append_ioi arg1 arg3 = do
  -- solution: arg2[0,1] arg2[0] arg2[1,1] arg2[1] arg2[] b[0,2] b[0] b[1,3,0,0] b[1,3,0] b[1,3] b[1] b[] h0[1,0,0] h0[1,0] h0[1] h0[] h1[1,2,0] h1[1,2] h1[1] h1[] h[1,0,1] h[1,0] h[1] h[] t[1,0,0] t[1,0] t[1] t[] tb[1,2,0] tb[1,2] tb[1] tb[] ~arg1[0,0,0] ~arg1[0,0] ~arg1[0,1] ~arg1[0,2] ~arg1[0,3] ~arg1[0] ~arg1[1,0,0] ~arg1[1,0,1] ~arg1[1,0] ~arg1[1,1] ~arg1[1,2] ~arg1[1,3] ~arg1[1] ~arg1[] ~arg2[0,0] ~arg2[0,2] ~arg2[0,3] ~arg2[1,0] ~arg2[1,2] ~arg2[1,3] ~arg3[0,0] ~arg3[0,1] ~arg3[0,2] ~arg3[0,3] ~arg3[0] ~arg3[1,0] ~arg3[1,1] ~arg3[1,2,0] ~arg3[1,2,1] ~arg3[1,2] ~arg3[1,3] ~arg3[1] ~arg3[] ~b[0,0] ~b[0,1] ~b[0,3] ~b[1,0] ~b[1,1] ~b[1,2] ~h0[0] ~h0[1,0,1] ~h0[1,1] ~h0[1,2] ~h0[1,3] ~h1[0] ~h1[1,0] ~h1[1,1] ~h1[1,2,1] ~h1[1,3] ~h[0] ~h[1,0,0] ~h[1,1] ~h[1,2,0] ~h[1,2,1] ~h[1,2] ~h[1,3] ~t[0] ~t[1,0,1] ~t[1,1] ~t[1,2] ~t[1,3,0,0] ~t[1,3,0] ~t[1,3] ~tb[0] ~tb[1,0] ~tb[1,1] ~tb[1,2,1] ~tb[1,3,0,0] ~tb[1,3,0] ~tb[1,3]
  (arg2) <- (do
    () <- (do
      guard $ arg1 == []
      pure ()
     )
    b <- pure arg3
    arg2 <- pure b
    () <- (do
      
      pure ()
     )
    pure (arg2)
   ) <|> (do
    (h,t) <- (do
      (h0:t) <- pure arg1
      h <- pure h0
      pure (h,t)
     )
    (tb) <- (do
      (h1:tb) <- pure arg3
      guard $ h1 == h
      pure (tb)
     )
    (b) <- (do
      (b) <- (do
        (b) <- append_ioi t tb
        pure (b)
       )
      pure (b)
     )
    arg2 <- pure b
    pure (arg2)
   )
  pure (arg2)

--append_ioi arg1 arg3 = do
--  -- solution: arg2[0,1] arg2[0] arg2[1,1] arg2[1] arg2[] b[0,2] b[0] b[1,3,0,0] b[1,3,0] b[1,3] b[1] b[] h0[1,0,0] h0[1,0] h0[1] h0[] h1[1,2,0] h1[1,2] h1[1] h1[] h[1,2,1] h[1,2] h[1] h[] t[1,0,0] t[1,0] t[1] t[] tb[1,2,0] tb[1,2] tb[1] tb[] ~arg1[0,0,0] ~arg1[0,0] ~arg1[0,1] ~arg1[0,2] ~arg1[0,3] ~arg1[0] ~arg1[1,0,0] ~arg1[1,0,1] ~arg1[1,0] ~arg1[1,1] ~arg1[1,2] ~arg1[1,3] ~arg1[1] ~arg1[] ~arg2[0,0] ~arg2[0,2] ~arg2[0,3] ~arg2[1,0] ~arg2[1,2] ~arg2[1,3] ~arg3[0,0] ~arg3[0,1] ~arg3[0,2] ~arg3[0,3] ~arg3[0] ~arg3[1,0] ~arg3[1,1] ~arg3[1,2,0] ~arg3[1,2,1] ~arg3[1,2] ~arg3[1,3] ~arg3[1] ~arg3[] ~b[0,0] ~b[0,1] ~b[0,3] ~b[1,0] ~b[1,1] ~b[1,2] ~h0[0] ~h0[1,0,1] ~h0[1,1] ~h0[1,2] ~h0[1,3] ~h1[0] ~h1[1,0] ~h1[1,1] ~h1[1,2,1] ~h1[1,3] ~h[0] ~h[1,0,0] ~h[1,0,1] ~h[1,0] ~h[1,1] ~h[1,2,0] ~h[1,3] ~t[0] ~t[1,0,1] ~t[1,1] ~t[1,2] ~t[1,3,0,0] ~t[1,3,0] ~t[1,3] ~tb[0] ~tb[1,0] ~tb[1,1] ~tb[1,2,1] ~tb[1,3,0,0] ~tb[1,3,0] ~tb[1,3]
--  (arg2) <- (do
--    () <- (do
--      guard $ arg1 == []
--      pure ()
--     )
--    b <- pure arg3
--    arg2 <- pure b
--    () <- (do
--      
--      pure ()
--     )
--    pure (arg2)
--   ) <|> (do
--    (h,tb) <- (do
--      (h1:tb) <- pure arg3
--      h <- pure h1
--      pure (h,tb)
--     )
--    (t) <- (do
--      (h0:t) <- pure arg1
--      guard $ h0 == h
--      pure (t)
--     )
--    (b) <- (do
--      (b) <- (do
--        (b) <- append_ioi t tb
--        pure (b)
--       )
--      pure (b)
--     )
--    arg2 <- pure b
--    pure (arg2)
--   )
--  pure (arg2)

append_oii arg2 arg3 = do
  -- solution: arg1[0,0,0] arg1[0,0] arg1[0] arg1[1,0,0] arg1[1,0] arg1[1] arg1[] b[0,1] b[0] b[1,1] b[1] b[] h0[1,0,1] h0[1,0] h0[1] h0[] h1[1,2,0] h1[1,2] h1[1] h1[] h[1,2,1] h[1,2] h[1] h[] t[1,3,0,0] t[1,3,0] t[1,3] t[1] t[] tb[1,2,0] tb[1,2] tb[1] tb[] ~arg1[0,1] ~arg1[0,2] ~arg1[0,3] ~arg1[1,0,1] ~arg1[1,1] ~arg1[1,2] ~arg1[1,3] ~arg2[0,0] ~arg2[0,1] ~arg2[0,2] ~arg2[0,3] ~arg2[0] ~arg2[1,0] ~arg2[1,1] ~arg2[1,2] ~arg2[1,3] ~arg2[1] ~arg2[] ~arg3[0,0] ~arg3[0,1] ~arg3[0,2] ~arg3[0,3] ~arg3[0] ~arg3[1,0] ~arg3[1,1] ~arg3[1,2,0] ~arg3[1,2,1] ~arg3[1,2] ~arg3[1,3] ~arg3[1] ~arg3[] ~b[0,0] ~b[0,2] ~b[0,3] ~b[1,0] ~b[1,2] ~b[1,3,0,0] ~b[1,3,0] ~b[1,3] ~h0[0] ~h0[1,0,0] ~h0[1,1] ~h0[1,2] ~h0[1,3] ~h1[0] ~h1[1,0] ~h1[1,1] ~h1[1,2,1] ~h1[1,3] ~h[0] ~h[1,0,0] ~h[1,0,1] ~h[1,0] ~h[1,1] ~h[1,2,0] ~h[1,3] ~t[0] ~t[1,0,0] ~t[1,0,1] ~t[1,0] ~t[1,1] ~t[1,2] ~tb[0] ~tb[1,0] ~tb[1,1] ~tb[1,2,1] ~tb[1,3,0,0] ~tb[1,3,0] ~tb[1,3]
  (arg1) <- (do
    (arg1) <- (do
      arg1 <- pure []
      pure (arg1)
     )
    b <- pure arg2
    guard $ arg3 == b
    () <- (do
      
      pure ()
     )
    pure (arg1)
   ) <|> (do
    b <- pure arg2
    (h,tb) <- (do
      (h1:tb) <- pure arg3
      h <- pure h1
      pure (h,tb)
     )
    (t) <- (do
      (t) <- (do
        (t) <- append_oii b tb
        pure (t)
       )
      pure (t)
     )
    (arg1) <- (do
      h0 <- pure h
      arg1 <- pure (h0:t)
      pure (arg1)
     )
    pure (arg1)
   )
  pure (arg1)

--append_oii arg2 arg3 = do
--  -- solution: arg1[0,0,0] arg1[0,0] arg1[0] arg1[1,0,0] arg1[1,0] arg1[1] arg1[] b[0,2] b[0] b[1,1] b[1] b[] h0[1,0,1] h0[1,0] h0[1] h0[] h1[1,2,0] h1[1,2] h1[1] h1[] h[1,2,1] h[1,2] h[1] h[] t[1,3,0,0] t[1,3,0] t[1,3] t[1] t[] tb[1,2,0] tb[1,2] tb[1] tb[] ~arg1[0,1] ~arg1[0,2] ~arg1[0,3] ~arg1[1,0,1] ~arg1[1,1] ~arg1[1,2] ~arg1[1,3] ~arg2[0,0] ~arg2[0,1] ~arg2[0,2] ~arg2[0,3] ~arg2[0] ~arg2[1,0] ~arg2[1,1] ~arg2[1,2] ~arg2[1,3] ~arg2[1] ~arg2[] ~arg3[0,0] ~arg3[0,1] ~arg3[0,2] ~arg3[0,3] ~arg3[0] ~arg3[1,0] ~arg3[1,1] ~arg3[1,2,0] ~arg3[1,2,1] ~arg3[1,2] ~arg3[1,3] ~arg3[1] ~arg3[] ~b[0,0] ~b[0,1] ~b[0,3] ~b[1,0] ~b[1,2] ~b[1,3,0,0] ~b[1,3,0] ~b[1,3] ~h0[0] ~h0[1,0,0] ~h0[1,1] ~h0[1,2] ~h0[1,3] ~h1[0] ~h1[1,0] ~h1[1,1] ~h1[1,2,1] ~h1[1,3] ~h[0] ~h[1,0,0] ~h[1,0,1] ~h[1,0] ~h[1,1] ~h[1,2,0] ~h[1,3] ~t[0] ~t[1,0,0] ~t[1,0,1] ~t[1,0] ~t[1,1] ~t[1,2] ~tb[0] ~tb[1,0] ~tb[1,1] ~tb[1,2,1] ~tb[1,3,0,0] ~tb[1,3,0] ~tb[1,3]
--  (arg1) <- (do
--    (arg1) <- (do
--      arg1 <- pure []
--      pure (arg1)
--     )
--    b <- pure arg3
--    guard $ arg2 == b
--    () <- (do
--      
--      pure ()
--     )
--    pure (arg1)
--   ) <|> (do
--    b <- pure arg2
--    (h,tb) <- (do
--      (h1:tb) <- pure arg3
--      h <- pure h1
--      pure (h,tb)
--     )
--    (t) <- (do
--      (t) <- (do
--        (t) <- append_oii b tb
--        pure (t)
--       )
--      pure (t)
--     )
--    (arg1) <- (do
--      h0 <- pure h
--      arg1 <- pure (h0:t)
--      pure (arg1)
--     )
--    pure (arg1)
--   )
--  pure (arg1)

append_ooi arg3 = do
  -- solution: arg1[0,0,0] arg1[0,0] arg1[0] arg1[1,0,0] arg1[1,0] arg1[1] arg1[] arg2[0,1] arg2[0] arg2[1,1] arg2[1] arg2[] b[0,2] b[0] b[1,3,0,0] b[1,3,0] b[1,3] b[1] b[] h0[1,0,1] h0[1,0] h0[1] h0[] h1[1,2,0] h1[1,2] h1[1] h1[] h[1,2,1] h[1,2] h[1] h[] t[1,3,0,0] t[1,3,0] t[1,3] t[1] t[] tb[1,2,0] tb[1,2] tb[1] tb[] ~arg1[0,1] ~arg1[0,2] ~arg1[0,3] ~arg1[1,0,1] ~arg1[1,1] ~arg1[1,2] ~arg1[1,3] ~arg2[0,0] ~arg2[0,2] ~arg2[0,3] ~arg2[1,0] ~arg2[1,2] ~arg2[1,3] ~arg3[0,0] ~arg3[0,1] ~arg3[0,2] ~arg3[0,3] ~arg3[0] ~arg3[1,0] ~arg3[1,1] ~arg3[1,2,0] ~arg3[1,2,1] ~arg3[1,2] ~arg3[1,3] ~arg3[1] ~arg3[] ~b[0,0] ~b[0,1] ~b[0,3] ~b[1,0] ~b[1,1] ~b[1,2] ~h0[0] ~h0[1,0,0] ~h0[1,1] ~h0[1,2] ~h0[1,3] ~h1[0] ~h1[1,0] ~h1[1,1] ~h1[1,2,1] ~h1[1,3] ~h[0] ~h[1,0,0] ~h[1,0,1] ~h[1,0] ~h[1,1] ~h[1,2,0] ~h[1,3] ~t[0] ~t[1,0,0] ~t[1,0,1] ~t[1,0] ~t[1,1] ~t[1,2] ~tb[0] ~tb[1,0] ~tb[1,1] ~tb[1,2,1] ~tb[1,3,0,0] ~tb[1,3,0] ~tb[1,3]
  (arg1,arg2) <- (do
    (arg1) <- (do
      arg1 <- pure []
      pure (arg1)
     )
    b <- pure arg3
    arg2 <- pure b
    () <- (do
      
      pure ()
     )
    pure (arg1,arg2)
   ) <|> (do
    (h,tb) <- (do
      (h1:tb) <- pure arg3
      h <- pure h1
      pure (h,tb)
     )
    (b,t) <- (do
      (b,t) <- (do
        (t,b) <- append_ooi tb
        pure (b,t)
       )
      pure (b,t)
     )
    (arg1) <- (do
      h0 <- pure h
      arg1 <- pure (h0:t)
      pure (arg1)
     )
    arg2 <- pure b
    pure (arg1,arg2)
   )
  pure (arg1,arg2)

{- append/4
append arg1 arg2 arg3 arg4 :- ((arg1 = a, arg2 = b, arg3 = c, arg4 = abc, ((append a b ab), (append ab c abc)))).
constraints:
a[0]
a[]
ab[0,4]
ab[0]
ab[]
abc[0]
abc[]
b[0]
b[]
c[0]
c[]
~a[0,1]
~a[0,2]
~a[0,3]
~a[0,4,1]
~ab[0,0]
~ab[0,1]
~ab[0,2]
~ab[0,3]
~abc[0,0]
~abc[0,1]
~abc[0,2]
~abc[0,4,0]
~arg1[0,1]
~arg1[0,2]
~arg1[0,3]
~arg1[0,4]
~arg2[0,0]
~arg2[0,2]
~arg2[0,3]
~arg2[0,4]
~arg3[0,0]
~arg3[0,1]
~arg3[0,3]
~arg3[0,4]
~arg4[0,0]
~arg4[0,1]
~arg4[0,2]
~arg4[0,4]
~b[0,0]
~b[0,2]
~b[0,3]
~b[0,4,1]
~c[0,0]
~c[0,1]
~c[0,3]
~c[0,4,0]
~(a[0,0] & a[0,4])
~(ab[0,4,0] & ab[0,4,1])
~(abc[0,3] & abc[0,4])
~(arg1[0,0] & a[0,0])
~(arg2[0,1] & b[0,1])
~(arg3[0,2] & c[0,2])
~(arg4[0,3] & abc[0,3])
~(b[0,1] & b[0,4])
~(c[0,2] & c[0,4])
((a[0,4,0,0] & (b[0,4,0,0] & ~ab[0,4,0,0])) | ((a[0,4,0,0] & (~b[0,4,0,0] & ~ab[0,4,0,0])) | ((~a[0,4,0,0] & (b[0,4,0,0] & ~ab[0,4,0,0])) | ((~a[0,4,0,0] & (~b[0,4,0,0] & ab[0,4,0,0])) | (~a[0,4,0,0] & (~b[0,4,0,0] & ~ab[0,4,0,0]))))))
((ab[0,4,1,0] & (c[0,4,1,0] & ~abc[0,4,1,0])) | ((ab[0,4,1,0] & (~c[0,4,1,0] & ~abc[0,4,1,0])) | ((~ab[0,4,1,0] & (c[0,4,1,0] & ~abc[0,4,1,0])) | ((~ab[0,4,1,0] & (~c[0,4,1,0] & abc[0,4,1,0])) | (~ab[0,4,1,0] & (~c[0,4,1,0] & ~abc[0,4,1,0]))))))
(a[0,4,0] <-> a[0,4,0,0])
(a[0,4] <-> a[0,4,0])
(a[0] <-> (a[0,0] | a[0,4]))
(ab[0,4,0] <-> ab[0,4,0,0])
(ab[0,4,1] <-> ab[0,4,1,0])
(ab[0,4] <-> (ab[0,4,0] | ab[0,4,1]))
(ab[0] <-> ab[0,4])
(abc[0,4,1] <-> abc[0,4,1,0])
(abc[0,4] <-> abc[0,4,1])
(abc[0] <-> (abc[0,3] | abc[0,4]))
(arg1[0] <-> arg1[0,0])
(arg1[] <-> arg1[0])
(arg2[0] <-> arg2[0,1])
(arg2[] <-> arg2[0])
(arg3[0] <-> arg3[0,2])
(arg3[] <-> arg3[0])
(arg4[0] <-> arg4[0,3])
(arg4[] <-> arg4[0])
(b[0,4,0] <-> b[0,4,0,0])
(b[0,4] <-> b[0,4,0])
(b[0] <-> (b[0,1] | b[0,4]))
(c[0,4,1] <-> c[0,4,1,0])
(c[0,4] <-> c[0,4,1])
(c[0] <-> (c[0,2] | c[0,4]))
-}
append_iiii arg1 arg2 arg3 arg4 = do
  -- solution: a[0,0] a[0] a[] ab[0,4,0,0] ab[0,4,0] ab[0,4] ab[0] ab[] abc[0,3] abc[0] abc[] b[0,1] b[0] b[] c[0,2] c[0] c[] ~a[0,1] ~a[0,2] ~a[0,3] ~a[0,4,0,0] ~a[0,4,0] ~a[0,4,1] ~a[0,4] ~ab[0,0] ~ab[0,1] ~ab[0,2] ~ab[0,3] ~ab[0,4,1,0] ~ab[0,4,1] ~abc[0,0] ~abc[0,1] ~abc[0,2] ~abc[0,4,0] ~abc[0,4,1,0] ~abc[0,4,1] ~abc[0,4] ~arg1[0,0] ~arg1[0,1] ~arg1[0,2] ~arg1[0,3] ~arg1[0,4] ~arg1[0] ~arg1[] ~arg2[0,0] ~arg2[0,1] ~arg2[0,2] ~arg2[0,3] ~arg2[0,4] ~arg2[0] ~arg2[] ~arg3[0,0] ~arg3[0,1] ~arg3[0,2] ~arg3[0,3] ~arg3[0,4] ~arg3[0] ~arg3[] ~arg4[0,0] ~arg4[0,1] ~arg4[0,2] ~arg4[0,3] ~arg4[0,4] ~arg4[0] ~arg4[] ~b[0,0] ~b[0,2] ~b[0,3] ~b[0,4,0,0] ~b[0,4,0] ~b[0,4,1] ~b[0,4] ~c[0,0] ~c[0,1] ~c[0,3] ~c[0,4,0] ~c[0,4,1,0] ~c[0,4,1] ~c[0,4]
  () <- (do
    a <- pure arg1
    b <- pure arg2
    c <- pure arg3
    abc <- pure arg4
    () <- (do
      (ab) <- (do
        (ab) <- append_iio a b
        pure (ab)
       )
      () <- (do
        () <- append_iii ab c abc
        pure ()
       )
      pure ()
     )
    pure ()
   )
  pure ()

--append_iiii arg1 arg2 arg3 arg4 = do
--  -- solution: a[0,0] a[0] a[] ab[0,4,0,0] ab[0,4,0] ab[0,4] ab[0] ab[] abc[0,3] abc[0] abc[] b[0,1] b[0] b[] c[0,4,1,0] c[0,4,1] c[0,4] c[0] c[] ~a[0,1] ~a[0,2] ~a[0,3] ~a[0,4,0,0] ~a[0,4,0] ~a[0,4,1] ~a[0,4] ~ab[0,0] ~ab[0,1] ~ab[0,2] ~ab[0,3] ~ab[0,4,1,0] ~ab[0,4,1] ~abc[0,0] ~abc[0,1] ~abc[0,2] ~abc[0,4,0] ~abc[0,4,1,0] ~abc[0,4,1] ~abc[0,4] ~arg1[0,0] ~arg1[0,1] ~arg1[0,2] ~arg1[0,3] ~arg1[0,4] ~arg1[0] ~arg1[] ~arg2[0,0] ~arg2[0,1] ~arg2[0,2] ~arg2[0,3] ~arg2[0,4] ~arg2[0] ~arg2[] ~arg3[0,0] ~arg3[0,1] ~arg3[0,2] ~arg3[0,3] ~arg3[0,4] ~arg3[0] ~arg3[] ~arg4[0,0] ~arg4[0,1] ~arg4[0,2] ~arg4[0,3] ~arg4[0,4] ~arg4[0] ~arg4[] ~b[0,0] ~b[0,2] ~b[0,3] ~b[0,4,0,0] ~b[0,4,0] ~b[0,4,1] ~b[0,4] ~c[0,0] ~c[0,1] ~c[0,2] ~c[0,3] ~c[0,4,0]
--  () <- (do
--    a <- pure arg1
--    b <- pure arg2
--    abc <- pure arg4
--    (c) <- (do
--      (ab) <- (do
--        (ab) <- append_iio a b
--        pure (ab)
--       )
--      (c) <- (do
--        (c) <- append_ioi ab abc
--        pure (c)
--       )
--      pure (c)
--     )
--    guard $ arg3 == c
--    pure ()
--   )
--  pure ()

--append_iiii arg1 arg2 arg3 arg4 = do
--  -- solution: a[0,0] a[0] a[] ab[0,4,0,0] ab[0,4,0] ab[0,4] ab[0] ab[] abc[0,4,1,0] abc[0,4,1] abc[0,4] abc[0] abc[] b[0,1] b[0] b[] c[0,2] c[0] c[] ~a[0,1] ~a[0,2] ~a[0,3] ~a[0,4,0,0] ~a[0,4,0] ~a[0,4,1] ~a[0,4] ~ab[0,0] ~ab[0,1] ~ab[0,2] ~ab[0,3] ~ab[0,4,1,0] ~ab[0,4,1] ~abc[0,0] ~abc[0,1] ~abc[0,2] ~abc[0,3] ~abc[0,4,0] ~arg1[0,0] ~arg1[0,1] ~arg1[0,2] ~arg1[0,3] ~arg1[0,4] ~arg1[0] ~arg1[] ~arg2[0,0] ~arg2[0,1] ~arg2[0,2] ~arg2[0,3] ~arg2[0,4] ~arg2[0] ~arg2[] ~arg3[0,0] ~arg3[0,1] ~arg3[0,2] ~arg3[0,3] ~arg3[0,4] ~arg3[0] ~arg3[] ~arg4[0,0] ~arg4[0,1] ~arg4[0,2] ~arg4[0,3] ~arg4[0,4] ~arg4[0] ~arg4[] ~b[0,0] ~b[0,2] ~b[0,3] ~b[0,4,0,0] ~b[0,4,0] ~b[0,4,1] ~b[0,4] ~c[0,0] ~c[0,1] ~c[0,3] ~c[0,4,0] ~c[0,4,1,0] ~c[0,4,1] ~c[0,4]
--  () <- (do
--    a <- pure arg1
--    b <- pure arg2
--    c <- pure arg3
--    (abc) <- (do
--      (ab) <- (do
--        (ab) <- append_iio a b
--        pure (ab)
--       )
--      (abc) <- (do
--        (abc) <- append_iio ab c
--        pure (abc)
--       )
--      pure (abc)
--     )
--    guard $ arg4 == abc
--    pure ()
--   )
--  pure ()

--append_iiii arg1 arg2 arg3 arg4 = do
--  -- solution: a[0,0] a[0] a[] ab[0,4,1,0] ab[0,4,1] ab[0,4] ab[0] ab[] abc[0,3] abc[0] abc[] b[0,1] b[0] b[] c[0,2] c[0] c[] ~a[0,1] ~a[0,2] ~a[0,3] ~a[0,4,0,0] ~a[0,4,0] ~a[0,4,1] ~a[0,4] ~ab[0,0] ~ab[0,1] ~ab[0,2] ~ab[0,3] ~ab[0,4,0,0] ~ab[0,4,0] ~abc[0,0] ~abc[0,1] ~abc[0,2] ~abc[0,4,0] ~abc[0,4,1,0] ~abc[0,4,1] ~abc[0,4] ~arg1[0,0] ~arg1[0,1] ~arg1[0,2] ~arg1[0,3] ~arg1[0,4] ~arg1[0] ~arg1[] ~arg2[0,0] ~arg2[0,1] ~arg2[0,2] ~arg2[0,3] ~arg2[0,4] ~arg2[0] ~arg2[] ~arg3[0,0] ~arg3[0,1] ~arg3[0,2] ~arg3[0,3] ~arg3[0,4] ~arg3[0] ~arg3[] ~arg4[0,0] ~arg4[0,1] ~arg4[0,2] ~arg4[0,3] ~arg4[0,4] ~arg4[0] ~arg4[] ~b[0,0] ~b[0,2] ~b[0,3] ~b[0,4,0,0] ~b[0,4,0] ~b[0,4,1] ~b[0,4] ~c[0,0] ~c[0,1] ~c[0,3] ~c[0,4,0] ~c[0,4,1,0] ~c[0,4,1] ~c[0,4]
--  () <- (do
--    a <- pure arg1
--    b <- pure arg2
--    c <- pure arg3
--    abc <- pure arg4
--    () <- (do
--      (ab) <- (do
--        (ab) <- append_oii c abc
--        pure (ab)
--       )
--      () <- (do
--        () <- append_iii a b ab
--        pure ()
--       )
--      pure ()
--     )
--    pure ()
--   )
--  pure ()

--append_iiii arg1 arg2 arg3 arg4 = do
--  -- solution: a[0,0] a[0] a[] ab[0,4,1,0] ab[0,4,1] ab[0,4] ab[0] ab[] abc[0,3] abc[0] abc[] b[0,1] b[0] b[] c[0,4,1,0] c[0,4,1] c[0,4] c[0] c[] ~a[0,1] ~a[0,2] ~a[0,3] ~a[0,4,0,0] ~a[0,4,0] ~a[0,4,1] ~a[0,4] ~ab[0,0] ~ab[0,1] ~ab[0,2] ~ab[0,3] ~ab[0,4,0,0] ~ab[0,4,0] ~abc[0,0] ~abc[0,1] ~abc[0,2] ~abc[0,4,0] ~abc[0,4,1,0] ~abc[0,4,1] ~abc[0,4] ~arg1[0,0] ~arg1[0,1] ~arg1[0,2] ~arg1[0,3] ~arg1[0,4] ~arg1[0] ~arg1[] ~arg2[0,0] ~arg2[0,1] ~arg2[0,2] ~arg2[0,3] ~arg2[0,4] ~arg2[0] ~arg2[] ~arg3[0,0] ~arg3[0,1] ~arg3[0,2] ~arg3[0,3] ~arg3[0,4] ~arg3[0] ~arg3[] ~arg4[0,0] ~arg4[0,1] ~arg4[0,2] ~arg4[0,3] ~arg4[0,4] ~arg4[0] ~arg4[] ~b[0,0] ~b[0,2] ~b[0,3] ~b[0,4,0,0] ~b[0,4,0] ~b[0,4,1] ~b[0,4] ~c[0,0] ~c[0,1] ~c[0,2] ~c[0,3] ~c[0,4,0]
--  () <- (do
--    a <- pure arg1
--    b <- pure arg2
--    abc <- pure arg4
--    (c) <- (do
--      (ab,c) <- (do
--        (ab,c) <- append_ooi abc
--        pure (ab,c)
--       )
--      () <- (do
--        () <- append_iii a b ab
--        pure ()
--       )
--      pure (c)
--     )
--    guard $ arg3 == c
--    pure ()
--   )
--  pure ()

--append_iiii arg1 arg2 arg3 arg4 = do
--  -- solution: a[0,0] a[0] a[] ab[0,4,1,0] ab[0,4,1] ab[0,4] ab[0] ab[] abc[0,3] abc[0] abc[] b[0,4,0,0] b[0,4,0] b[0,4] b[0] b[] c[0,2] c[0] c[] ~a[0,1] ~a[0,2] ~a[0,3] ~a[0,4,0,0] ~a[0,4,0] ~a[0,4,1] ~a[0,4] ~ab[0,0] ~ab[0,1] ~ab[0,2] ~ab[0,3] ~ab[0,4,0,0] ~ab[0,4,0] ~abc[0,0] ~abc[0,1] ~abc[0,2] ~abc[0,4,0] ~abc[0,4,1,0] ~abc[0,4,1] ~abc[0,4] ~arg1[0,0] ~arg1[0,1] ~arg1[0,2] ~arg1[0,3] ~arg1[0,4] ~arg1[0] ~arg1[] ~arg2[0,0] ~arg2[0,1] ~arg2[0,2] ~arg2[0,3] ~arg2[0,4] ~arg2[0] ~arg2[] ~arg3[0,0] ~arg3[0,1] ~arg3[0,2] ~arg3[0,3] ~arg3[0,4] ~arg3[0] ~arg3[] ~arg4[0,0] ~arg4[0,1] ~arg4[0,2] ~arg4[0,3] ~arg4[0,4] ~arg4[0] ~arg4[] ~b[0,0] ~b[0,1] ~b[0,2] ~b[0,3] ~b[0,4,1] ~c[0,0] ~c[0,1] ~c[0,3] ~c[0,4,0] ~c[0,4,1,0] ~c[0,4,1] ~c[0,4]
--  () <- (do
--    a <- pure arg1
--    c <- pure arg3
--    abc <- pure arg4
--    (b) <- (do
--      (ab) <- (do
--        (ab) <- append_oii c abc
--        pure (ab)
--       )
--      (b) <- (do
--        (b) <- append_ioi a ab
--        pure (b)
--       )
--      pure (b)
--     )
--    guard $ arg2 == b
--    pure ()
--   )
--  pure ()

--append_iiii arg1 arg2 arg3 arg4 = do
--  -- solution: a[0,0] a[0] a[] ab[0,4,1,0] ab[0,4,1] ab[0,4] ab[0] ab[] abc[0,3] abc[0] abc[] b[0,4,0,0] b[0,4,0] b[0,4] b[0] b[] c[0,4,1,0] c[0,4,1] c[0,4] c[0] c[] ~a[0,1] ~a[0,2] ~a[0,3] ~a[0,4,0,0] ~a[0,4,0] ~a[0,4,1] ~a[0,4] ~ab[0,0] ~ab[0,1] ~ab[0,2] ~ab[0,3] ~ab[0,4,0,0] ~ab[0,4,0] ~abc[0,0] ~abc[0,1] ~abc[0,2] ~abc[0,4,0] ~abc[0,4,1,0] ~abc[0,4,1] ~abc[0,4] ~arg1[0,0] ~arg1[0,1] ~arg1[0,2] ~arg1[0,3] ~arg1[0,4] ~arg1[0] ~arg1[] ~arg2[0,0] ~arg2[0,1] ~arg2[0,2] ~arg2[0,3] ~arg2[0,4] ~arg2[0] ~arg2[] ~arg3[0,0] ~arg3[0,1] ~arg3[0,2] ~arg3[0,3] ~arg3[0,4] ~arg3[0] ~arg3[] ~arg4[0,0] ~arg4[0,1] ~arg4[0,2] ~arg4[0,3] ~arg4[0,4] ~arg4[0] ~arg4[] ~b[0,0] ~b[0,1] ~b[0,2] ~b[0,3] ~b[0,4,1] ~c[0,0] ~c[0,1] ~c[0,2] ~c[0,3] ~c[0,4,0]
--  () <- (do
--    a <- pure arg1
--    abc <- pure arg4
--    (b,c) <- (do
--      (ab,c) <- (do
--        (ab,c) <- append_ooi abc
--        pure (ab,c)
--       )
--      (b) <- (do
--        (b) <- append_ioi a ab
--        pure (b)
--       )
--      pure (b,c)
--     )
--    guard $ arg2 == b
--    guard $ arg3 == c
--    pure ()
--   )
--  pure ()

--append_iiii arg1 arg2 arg3 arg4 = do
--  -- solution: a[0,4,0,0] a[0,4,0] a[0,4] a[0] a[] ab[0,4,1,0] ab[0,4,1] ab[0,4] ab[0] ab[] abc[0,3] abc[0] abc[] b[0,1] b[0] b[] c[0,2] c[0] c[] ~a[0,0] ~a[0,1] ~a[0,2] ~a[0,3] ~a[0,4,1] ~ab[0,0] ~ab[0,1] ~ab[0,2] ~ab[0,3] ~ab[0,4,0,0] ~ab[0,4,0] ~abc[0,0] ~abc[0,1] ~abc[0,2] ~abc[0,4,0] ~abc[0,4,1,0] ~abc[0,4,1] ~abc[0,4] ~arg1[0,0] ~arg1[0,1] ~arg1[0,2] ~arg1[0,3] ~arg1[0,4] ~arg1[0] ~arg1[] ~arg2[0,0] ~arg2[0,1] ~arg2[0,2] ~arg2[0,3] ~arg2[0,4] ~arg2[0] ~arg2[] ~arg3[0,0] ~arg3[0,1] ~arg3[0,2] ~arg3[0,3] ~arg3[0,4] ~arg3[0] ~arg3[] ~arg4[0,0] ~arg4[0,1] ~arg4[0,2] ~arg4[0,3] ~arg4[0,4] ~arg4[0] ~arg4[] ~b[0,0] ~b[0,2] ~b[0,3] ~b[0,4,0,0] ~b[0,4,0] ~b[0,4,1] ~b[0,4] ~c[0,0] ~c[0,1] ~c[0,3] ~c[0,4,0] ~c[0,4,1,0] ~c[0,4,1] ~c[0,4]
--  () <- (do
--    b <- pure arg2
--    c <- pure arg3
--    abc <- pure arg4
--    (a) <- (do
--      (ab) <- (do
--        (ab) <- append_oii c abc
--        pure (ab)
--       )
--      (a) <- (do
--        (a) <- append_oii b ab
--        pure (a)
--       )
--      pure (a)
--     )
--    guard $ arg1 == a
--    pure ()
--   )
--  pure ()

--append_iiii arg1 arg2 arg3 arg4 = do
--  -- solution: a[0,4,0,0] a[0,4,0] a[0,4] a[0] a[] ab[0,4,1,0] ab[0,4,1] ab[0,4] ab[0] ab[] abc[0,3] abc[0] abc[] b[0,1] b[0] b[] c[0,4,1,0] c[0,4,1] c[0,4] c[0] c[] ~a[0,0] ~a[0,1] ~a[0,2] ~a[0,3] ~a[0,4,1] ~ab[0,0] ~ab[0,1] ~ab[0,2] ~ab[0,3] ~ab[0,4,0,0] ~ab[0,4,0] ~abc[0,0] ~abc[0,1] ~abc[0,2] ~abc[0,4,0] ~abc[0,4,1,0] ~abc[0,4,1] ~abc[0,4] ~arg1[0,0] ~arg1[0,1] ~arg1[0,2] ~arg1[0,3] ~arg1[0,4] ~arg1[0] ~arg1[] ~arg2[0,0] ~arg2[0,1] ~arg2[0,2] ~arg2[0,3] ~arg2[0,4] ~arg2[0] ~arg2[] ~arg3[0,0] ~arg3[0,1] ~arg3[0,2] ~arg3[0,3] ~arg3[0,4] ~arg3[0] ~arg3[] ~arg4[0,0] ~arg4[0,1] ~arg4[0,2] ~arg4[0,3] ~arg4[0,4] ~arg4[0] ~arg4[] ~b[0,0] ~b[0,2] ~b[0,3] ~b[0,4,0,0] ~b[0,4,0] ~b[0,4,1] ~b[0,4] ~c[0,0] ~c[0,1] ~c[0,2] ~c[0,3] ~c[0,4,0]
--  () <- (do
--    b <- pure arg2
--    abc <- pure arg4
--    (a,c) <- (do
--      (ab,c) <- (do
--        (ab,c) <- append_ooi abc
--        pure (ab,c)
--       )
--      (a) <- (do
--        (a) <- append_oii b ab
--        pure (a)
--       )
--      pure (a,c)
--     )
--    guard $ arg1 == a
--    guard $ arg3 == c
--    pure ()
--   )
--  pure ()

--append_iiii arg1 arg2 arg3 arg4 = do
--  -- solution: a[0,4,0,0] a[0,4,0] a[0,4] a[0] a[] ab[0,4,1,0] ab[0,4,1] ab[0,4] ab[0] ab[] abc[0,3] abc[0] abc[] b[0,4,0,0] b[0,4,0] b[0,4] b[0] b[] c[0,2] c[0] c[] ~a[0,0] ~a[0,1] ~a[0,2] ~a[0,3] ~a[0,4,1] ~ab[0,0] ~ab[0,1] ~ab[0,2] ~ab[0,3] ~ab[0,4,0,0] ~ab[0,4,0] ~abc[0,0] ~abc[0,1] ~abc[0,2] ~abc[0,4,0] ~abc[0,4,1,0] ~abc[0,4,1] ~abc[0,4] ~arg1[0,0] ~arg1[0,1] ~arg1[0,2] ~arg1[0,3] ~arg1[0,4] ~arg1[0] ~arg1[] ~arg2[0,0] ~arg2[0,1] ~arg2[0,2] ~arg2[0,3] ~arg2[0,4] ~arg2[0] ~arg2[] ~arg3[0,0] ~arg3[0,1] ~arg3[0,2] ~arg3[0,3] ~arg3[0,4] ~arg3[0] ~arg3[] ~arg4[0,0] ~arg4[0,1] ~arg4[0,2] ~arg4[0,3] ~arg4[0,4] ~arg4[0] ~arg4[] ~b[0,0] ~b[0,1] ~b[0,2] ~b[0,3] ~b[0,4,1] ~c[0,0] ~c[0,1] ~c[0,3] ~c[0,4,0] ~c[0,4,1,0] ~c[0,4,1] ~c[0,4]
--  () <- (do
--    c <- pure arg3
--    abc <- pure arg4
--    (a,b) <- (do
--      (ab) <- (do
--        (ab) <- append_oii c abc
--        pure (ab)
--       )
--      (a,b) <- (do
--        (a,b) <- append_ooi ab
--        pure (a,b)
--       )
--      pure (a,b)
--     )
--    guard $ arg1 == a
--    guard $ arg2 == b
--    pure ()
--   )
--  pure ()

--append_iiii arg1 arg2 arg3 arg4 = do
--  -- solution: a[0,4,0,0] a[0,4,0] a[0,4] a[0] a[] ab[0,4,1,0] ab[0,4,1] ab[0,4] ab[0] ab[] abc[0,3] abc[0] abc[] b[0,4,0,0] b[0,4,0] b[0,4] b[0] b[] c[0,4,1,0] c[0,4,1] c[0,4] c[0] c[] ~a[0,0] ~a[0,1] ~a[0,2] ~a[0,3] ~a[0,4,1] ~ab[0,0] ~ab[0,1] ~ab[0,2] ~ab[0,3] ~ab[0,4,0,0] ~ab[0,4,0] ~abc[0,0] ~abc[0,1] ~abc[0,2] ~abc[0,4,0] ~abc[0,4,1,0] ~abc[0,4,1] ~abc[0,4] ~arg1[0,0] ~arg1[0,1] ~arg1[0,2] ~arg1[0,3] ~arg1[0,4] ~arg1[0] ~arg1[] ~arg2[0,0] ~arg2[0,1] ~arg2[0,2] ~arg2[0,3] ~arg2[0,4] ~arg2[0] ~arg2[] ~arg3[0,0] ~arg3[0,1] ~arg3[0,2] ~arg3[0,3] ~arg3[0,4] ~arg3[0] ~arg3[] ~arg4[0,0] ~arg4[0,1] ~arg4[0,2] ~arg4[0,3] ~arg4[0,4] ~arg4[0] ~arg4[] ~b[0,0] ~b[0,1] ~b[0,2] ~b[0,3] ~b[0,4,1] ~c[0,0] ~c[0,1] ~c[0,2] ~c[0,3] ~c[0,4,0]
--  () <- (do
--    abc <- pure arg4
--    (a,b,c) <- (do
--      (ab,c) <- (do
--        (ab,c) <- append_ooi abc
--        pure (ab,c)
--       )
--      (a,b) <- (do
--        (a,b) <- append_ooi ab
--        pure (a,b)
--       )
--      pure (a,b,c)
--     )
--    guard $ arg1 == a
--    guard $ arg2 == b
--    guard $ arg3 == c
--    pure ()
--   )
--  pure ()

append_iiio arg1 arg2 arg3 = do
  -- solution: a[0,0] a[0] a[] ab[0,4,0,0] ab[0,4,0] ab[0,4] ab[0] ab[] abc[0,4,1,0] abc[0,4,1] abc[0,4] abc[0] abc[] arg4[0,3] arg4[0] arg4[] b[0,1] b[0] b[] c[0,2] c[0] c[] ~a[0,1] ~a[0,2] ~a[0,3] ~a[0,4,0,0] ~a[0,4,0] ~a[0,4,1] ~a[0,4] ~ab[0,0] ~ab[0,1] ~ab[0,2] ~ab[0,3] ~ab[0,4,1,0] ~ab[0,4,1] ~abc[0,0] ~abc[0,1] ~abc[0,2] ~abc[0,3] ~abc[0,4,0] ~arg1[0,0] ~arg1[0,1] ~arg1[0,2] ~arg1[0,3] ~arg1[0,4] ~arg1[0] ~arg1[] ~arg2[0,0] ~arg2[0,1] ~arg2[0,2] ~arg2[0,3] ~arg2[0,4] ~arg2[0] ~arg2[] ~arg3[0,0] ~arg3[0,1] ~arg3[0,2] ~arg3[0,3] ~arg3[0,4] ~arg3[0] ~arg3[] ~arg4[0,0] ~arg4[0,1] ~arg4[0,2] ~arg4[0,4] ~b[0,0] ~b[0,2] ~b[0,3] ~b[0,4,0,0] ~b[0,4,0] ~b[0,4,1] ~b[0,4] ~c[0,0] ~c[0,1] ~c[0,3] ~c[0,4,0] ~c[0,4,1,0] ~c[0,4,1] ~c[0,4]
  (arg4) <- (do
    a <- pure arg1
    b <- pure arg2
    c <- pure arg3
    (abc) <- (do
      (ab) <- (do
        (ab) <- append_iio a b
        pure (ab)
       )
      (abc) <- (do
        (abc) <- append_iio ab c
        pure (abc)
       )
      pure (abc)
     )
    arg4 <- pure abc
    pure (arg4)
   )
  pure (arg4)

append_iioi arg1 arg2 arg4 = do
  -- solution: a[0,0] a[0] a[] ab[0,4,0,0] ab[0,4,0] ab[0,4] ab[0] ab[] abc[0,3] abc[0] abc[] arg3[0,2] arg3[0] arg3[] b[0,1] b[0] b[] c[0,4,1,0] c[0,4,1] c[0,4] c[0] c[] ~a[0,1] ~a[0,2] ~a[0,3] ~a[0,4,0,0] ~a[0,4,0] ~a[0,4,1] ~a[0,4] ~ab[0,0] ~ab[0,1] ~ab[0,2] ~ab[0,3] ~ab[0,4,1,0] ~ab[0,4,1] ~abc[0,0] ~abc[0,1] ~abc[0,2] ~abc[0,4,0] ~abc[0,4,1,0] ~abc[0,4,1] ~abc[0,4] ~arg1[0,0] ~arg1[0,1] ~arg1[0,2] ~arg1[0,3] ~arg1[0,4] ~arg1[0] ~arg1[] ~arg2[0,0] ~arg2[0,1] ~arg2[0,2] ~arg2[0,3] ~arg2[0,4] ~arg2[0] ~arg2[] ~arg3[0,0] ~arg3[0,1] ~arg3[0,3] ~arg3[0,4] ~arg4[0,0] ~arg4[0,1] ~arg4[0,2] ~arg4[0,3] ~arg4[0,4] ~arg4[0] ~arg4[] ~b[0,0] ~b[0,2] ~b[0,3] ~b[0,4,0,0] ~b[0,4,0] ~b[0,4,1] ~b[0,4] ~c[0,0] ~c[0,1] ~c[0,2] ~c[0,3] ~c[0,4,0]
  (arg3) <- (do
    a <- pure arg1
    b <- pure arg2
    abc <- pure arg4
    (c) <- (do
      (ab) <- (do
        (ab) <- append_iio a b
        pure (ab)
       )
      (c) <- (do
        (c) <- append_ioi ab abc
        pure (c)
       )
      pure (c)
     )
    arg3 <- pure c
    pure (arg3)
   )
  pure (arg3)

--append_iioi arg1 arg2 arg4 = do
--  -- solution: a[0,0] a[0] a[] ab[0,4,1,0] ab[0,4,1] ab[0,4] ab[0] ab[] abc[0,3] abc[0] abc[] arg3[0,2] arg3[0] arg3[] b[0,1] b[0] b[] c[0,4,1,0] c[0,4,1] c[0,4] c[0] c[] ~a[0,1] ~a[0,2] ~a[0,3] ~a[0,4,0,0] ~a[0,4,0] ~a[0,4,1] ~a[0,4] ~ab[0,0] ~ab[0,1] ~ab[0,2] ~ab[0,3] ~ab[0,4,0,0] ~ab[0,4,0] ~abc[0,0] ~abc[0,1] ~abc[0,2] ~abc[0,4,0] ~abc[0,4,1,0] ~abc[0,4,1] ~abc[0,4] ~arg1[0,0] ~arg1[0,1] ~arg1[0,2] ~arg1[0,3] ~arg1[0,4] ~arg1[0] ~arg1[] ~arg2[0,0] ~arg2[0,1] ~arg2[0,2] ~arg2[0,3] ~arg2[0,4] ~arg2[0] ~arg2[] ~arg3[0,0] ~arg3[0,1] ~arg3[0,3] ~arg3[0,4] ~arg4[0,0] ~arg4[0,1] ~arg4[0,2] ~arg4[0,3] ~arg4[0,4] ~arg4[0] ~arg4[] ~b[0,0] ~b[0,2] ~b[0,3] ~b[0,4,0,0] ~b[0,4,0] ~b[0,4,1] ~b[0,4] ~c[0,0] ~c[0,1] ~c[0,2] ~c[0,3] ~c[0,4,0]
--  (arg3) <- (do
--    a <- pure arg1
--    b <- pure arg2
--    abc <- pure arg4
--    (c) <- (do
--      (ab,c) <- (do
--        (ab,c) <- append_ooi abc
--        pure (ab,c)
--       )
--      () <- (do
--        () <- append_iii a b ab
--        pure ()
--       )
--      pure (c)
--     )
--    arg3 <- pure c
--    pure (arg3)
--   )
--  pure (arg3)

--append_iioi arg1 arg2 arg4 = do
--  -- solution: a[0,0] a[0] a[] ab[0,4,1,0] ab[0,4,1] ab[0,4] ab[0] ab[] abc[0,3] abc[0] abc[] arg3[0,2] arg3[0] arg3[] b[0,4,0,0] b[0,4,0] b[0,4] b[0] b[] c[0,4,1,0] c[0,4,1] c[0,4] c[0] c[] ~a[0,1] ~a[0,2] ~a[0,3] ~a[0,4,0,0] ~a[0,4,0] ~a[0,4,1] ~a[0,4] ~ab[0,0] ~ab[0,1] ~ab[0,2] ~ab[0,3] ~ab[0,4,0,0] ~ab[0,4,0] ~abc[0,0] ~abc[0,1] ~abc[0,2] ~abc[0,4,0] ~abc[0,4,1,0] ~abc[0,4,1] ~abc[0,4] ~arg1[0,0] ~arg1[0,1] ~arg1[0,2] ~arg1[0,3] ~arg1[0,4] ~arg1[0] ~arg1[] ~arg2[0,0] ~arg2[0,1] ~arg2[0,2] ~arg2[0,3] ~arg2[0,4] ~arg2[0] ~arg2[] ~arg3[0,0] ~arg3[0,1] ~arg3[0,3] ~arg3[0,4] ~arg4[0,0] ~arg4[0,1] ~arg4[0,2] ~arg4[0,3] ~arg4[0,4] ~arg4[0] ~arg4[] ~b[0,0] ~b[0,1] ~b[0,2] ~b[0,3] ~b[0,4,1] ~c[0,0] ~c[0,1] ~c[0,2] ~c[0,3] ~c[0,4,0]
--  (arg3) <- (do
--    a <- pure arg1
--    abc <- pure arg4
--    (b,c) <- (do
--      (ab,c) <- (do
--        (ab,c) <- append_ooi abc
--        pure (ab,c)
--       )
--      (b) <- (do
--        (b) <- append_ioi a ab
--        pure (b)
--       )
--      pure (b,c)
--     )
--    guard $ arg2 == b
--    arg3 <- pure c
--    pure (arg3)
--   )
--  pure (arg3)

--append_iioi arg1 arg2 arg4 = do
--  -- solution: a[0,4,0,0] a[0,4,0] a[0,4] a[0] a[] ab[0,4,1,0] ab[0,4,1] ab[0,4] ab[0] ab[] abc[0,3] abc[0] abc[] arg3[0,2] arg3[0] arg3[] b[0,1] b[0] b[] c[0,4,1,0] c[0,4,1] c[0,4] c[0] c[] ~a[0,0] ~a[0,1] ~a[0,2] ~a[0,3] ~a[0,4,1] ~ab[0,0] ~ab[0,1] ~ab[0,2] ~ab[0,3] ~ab[0,4,0,0] ~ab[0,4,0] ~abc[0,0] ~abc[0,1] ~abc[0,2] ~abc[0,4,0] ~abc[0,4,1,0] ~abc[0,4,1] ~abc[0,4] ~arg1[0,0] ~arg1[0,1] ~arg1[0,2] ~arg1[0,3] ~arg1[0,4] ~arg1[0] ~arg1[] ~arg2[0,0] ~arg2[0,1] ~arg2[0,2] ~arg2[0,3] ~arg2[0,4] ~arg2[0] ~arg2[] ~arg3[0,0] ~arg3[0,1] ~arg3[0,3] ~arg3[0,4] ~arg4[0,0] ~arg4[0,1] ~arg4[0,2] ~arg4[0,3] ~arg4[0,4] ~arg4[0] ~arg4[] ~b[0,0] ~b[0,2] ~b[0,3] ~b[0,4,0,0] ~b[0,4,0] ~b[0,4,1] ~b[0,4] ~c[0,0] ~c[0,1] ~c[0,2] ~c[0,3] ~c[0,4,0]
--  (arg3) <- (do
--    b <- pure arg2
--    abc <- pure arg4
--    (a,c) <- (do
--      (ab,c) <- (do
--        (ab,c) <- append_ooi abc
--        pure (ab,c)
--       )
--      (a) <- (do
--        (a) <- append_oii b ab
--        pure (a)
--       )
--      pure (a,c)
--     )
--    guard $ arg1 == a
--    arg3 <- pure c
--    pure (arg3)
--   )
--  pure (arg3)

--append_iioi arg1 arg2 arg4 = do
--  -- solution: a[0,4,0,0] a[0,4,0] a[0,4] a[0] a[] ab[0,4,1,0] ab[0,4,1] ab[0,4] ab[0] ab[] abc[0,3] abc[0] abc[] arg3[0,2] arg3[0] arg3[] b[0,4,0,0] b[0,4,0] b[0,4] b[0] b[] c[0,4,1,0] c[0,4,1] c[0,4] c[0] c[] ~a[0,0] ~a[0,1] ~a[0,2] ~a[0,3] ~a[0,4,1] ~ab[0,0] ~ab[0,1] ~ab[0,2] ~ab[0,3] ~ab[0,4,0,0] ~ab[0,4,0] ~abc[0,0] ~abc[0,1] ~abc[0,2] ~abc[0,4,0] ~abc[0,4,1,0] ~abc[0,4,1] ~abc[0,4] ~arg1[0,0] ~arg1[0,1] ~arg1[0,2] ~arg1[0,3] ~arg1[0,4] ~arg1[0] ~arg1[] ~arg2[0,0] ~arg2[0,1] ~arg2[0,2] ~arg2[0,3] ~arg2[0,4] ~arg2[0] ~arg2[] ~arg3[0,0] ~arg3[0,1] ~arg3[0,3] ~arg3[0,4] ~arg4[0,0] ~arg4[0,1] ~arg4[0,2] ~arg4[0,3] ~arg4[0,4] ~arg4[0] ~arg4[] ~b[0,0] ~b[0,1] ~b[0,2] ~b[0,3] ~b[0,4,1] ~c[0,0] ~c[0,1] ~c[0,2] ~c[0,3] ~c[0,4,0]
--  (arg3) <- (do
--    abc <- pure arg4
--    (a,b,c) <- (do
--      (ab,c) <- (do
--        (ab,c) <- append_ooi abc
--        pure (ab,c)
--       )
--      (a,b) <- (do
--        (a,b) <- append_ooi ab
--        pure (a,b)
--       )
--      pure (a,b,c)
--     )
--    guard $ arg1 == a
--    guard $ arg2 == b
--    arg3 <- pure c
--    pure (arg3)
--   )
--  pure (arg3)

append_ioii arg1 arg3 arg4 = do
  -- solution: a[0,0] a[0] a[] ab[0,4,1,0] ab[0,4,1] ab[0,4] ab[0] ab[] abc[0,3] abc[0] abc[] arg2[0,1] arg2[0] arg2[] b[0,4,0,0] b[0,4,0] b[0,4] b[0] b[] c[0,2] c[0] c[] ~a[0,1] ~a[0,2] ~a[0,3] ~a[0,4,0,0] ~a[0,4,0] ~a[0,4,1] ~a[0,4] ~ab[0,0] ~ab[0,1] ~ab[0,2] ~ab[0,3] ~ab[0,4,0,0] ~ab[0,4,0] ~abc[0,0] ~abc[0,1] ~abc[0,2] ~abc[0,4,0] ~abc[0,4,1,0] ~abc[0,4,1] ~abc[0,4] ~arg1[0,0] ~arg1[0,1] ~arg1[0,2] ~arg1[0,3] ~arg1[0,4] ~arg1[0] ~arg1[] ~arg2[0,0] ~arg2[0,2] ~arg2[0,3] ~arg2[0,4] ~arg3[0,0] ~arg3[0,1] ~arg3[0,2] ~arg3[0,3] ~arg3[0,4] ~arg3[0] ~arg3[] ~arg4[0,0] ~arg4[0,1] ~arg4[0,2] ~arg4[0,3] ~arg4[0,4] ~arg4[0] ~arg4[] ~b[0,0] ~b[0,1] ~b[0,2] ~b[0,3] ~b[0,4,1] ~c[0,0] ~c[0,1] ~c[0,3] ~c[0,4,0] ~c[0,4,1,0] ~c[0,4,1] ~c[0,4]
  (arg2) <- (do
    a <- pure arg1
    c <- pure arg3
    abc <- pure arg4
    (b) <- (do
      (ab) <- (do
        (ab) <- append_oii c abc
        pure (ab)
       )
      (b) <- (do
        (b) <- append_ioi a ab
        pure (b)
       )
      pure (b)
     )
    arg2 <- pure b
    pure (arg2)
   )
  pure (arg2)

--append_ioii arg1 arg3 arg4 = do
--  -- solution: a[0,0] a[0] a[] ab[0,4,1,0] ab[0,4,1] ab[0,4] ab[0] ab[] abc[0,3] abc[0] abc[] arg2[0,1] arg2[0] arg2[] b[0,4,0,0] b[0,4,0] b[0,4] b[0] b[] c[0,4,1,0] c[0,4,1] c[0,4] c[0] c[] ~a[0,1] ~a[0,2] ~a[0,3] ~a[0,4,0,0] ~a[0,4,0] ~a[0,4,1] ~a[0,4] ~ab[0,0] ~ab[0,1] ~ab[0,2] ~ab[0,3] ~ab[0,4,0,0] ~ab[0,4,0] ~abc[0,0] ~abc[0,1] ~abc[0,2] ~abc[0,4,0] ~abc[0,4,1,0] ~abc[0,4,1] ~abc[0,4] ~arg1[0,0] ~arg1[0,1] ~arg1[0,2] ~arg1[0,3] ~arg1[0,4] ~arg1[0] ~arg1[] ~arg2[0,0] ~arg2[0,2] ~arg2[0,3] ~arg2[0,4] ~arg3[0,0] ~arg3[0,1] ~arg3[0,2] ~arg3[0,3] ~arg3[0,4] ~arg3[0] ~arg3[] ~arg4[0,0] ~arg4[0,1] ~arg4[0,2] ~arg4[0,3] ~arg4[0,4] ~arg4[0] ~arg4[] ~b[0,0] ~b[0,1] ~b[0,2] ~b[0,3] ~b[0,4,1] ~c[0,0] ~c[0,1] ~c[0,2] ~c[0,3] ~c[0,4,0]
--  (arg2) <- (do
--    a <- pure arg1
--    abc <- pure arg4
--    (b,c) <- (do
--      (ab,c) <- (do
--        (ab,c) <- append_ooi abc
--        pure (ab,c)
--       )
--      (b) <- (do
--        (b) <- append_ioi a ab
--        pure (b)
--       )
--      pure (b,c)
--     )
--    arg2 <- pure b
--    guard $ arg3 == c
--    pure (arg2)
--   )
--  pure (arg2)

--append_ioii arg1 arg3 arg4 = do
--  -- solution: a[0,4,0,0] a[0,4,0] a[0,4] a[0] a[] ab[0,4,1,0] ab[0,4,1] ab[0,4] ab[0] ab[] abc[0,3] abc[0] abc[] arg2[0,1] arg2[0] arg2[] b[0,4,0,0] b[0,4,0] b[0,4] b[0] b[] c[0,2] c[0] c[] ~a[0,0] ~a[0,1] ~a[0,2] ~a[0,3] ~a[0,4,1] ~ab[0,0] ~ab[0,1] ~ab[0,2] ~ab[0,3] ~ab[0,4,0,0] ~ab[0,4,0] ~abc[0,0] ~abc[0,1] ~abc[0,2] ~abc[0,4,0] ~abc[0,4,1,0] ~abc[0,4,1] ~abc[0,4] ~arg1[0,0] ~arg1[0,1] ~arg1[0,2] ~arg1[0,3] ~arg1[0,4] ~arg1[0] ~arg1[] ~arg2[0,0] ~arg2[0,2] ~arg2[0,3] ~arg2[0,4] ~arg3[0,0] ~arg3[0,1] ~arg3[0,2] ~arg3[0,3] ~arg3[0,4] ~arg3[0] ~arg3[] ~arg4[0,0] ~arg4[0,1] ~arg4[0,2] ~arg4[0,3] ~arg4[0,4] ~arg4[0] ~arg4[] ~b[0,0] ~b[0,1] ~b[0,2] ~b[0,3] ~b[0,4,1] ~c[0,0] ~c[0,1] ~c[0,3] ~c[0,4,0] ~c[0,4,1,0] ~c[0,4,1] ~c[0,4]
--  (arg2) <- (do
--    c <- pure arg3
--    abc <- pure arg4
--    (a,b) <- (do
--      (ab) <- (do
--        (ab) <- append_oii c abc
--        pure (ab)
--       )
--      (a,b) <- (do
--        (a,b) <- append_ooi ab
--        pure (a,b)
--       )
--      pure (a,b)
--     )
--    guard $ arg1 == a
--    arg2 <- pure b
--    pure (arg2)
--   )
--  pure (arg2)

--append_ioii arg1 arg3 arg4 = do
--  -- solution: a[0,4,0,0] a[0,4,0] a[0,4] a[0] a[] ab[0,4,1,0] ab[0,4,1] ab[0,4] ab[0] ab[] abc[0,3] abc[0] abc[] arg2[0,1] arg2[0] arg2[] b[0,4,0,0] b[0,4,0] b[0,4] b[0] b[] c[0,4,1,0] c[0,4,1] c[0,4] c[0] c[] ~a[0,0] ~a[0,1] ~a[0,2] ~a[0,3] ~a[0,4,1] ~ab[0,0] ~ab[0,1] ~ab[0,2] ~ab[0,3] ~ab[0,4,0,0] ~ab[0,4,0] ~abc[0,0] ~abc[0,1] ~abc[0,2] ~abc[0,4,0] ~abc[0,4,1,0] ~abc[0,4,1] ~abc[0,4] ~arg1[0,0] ~arg1[0,1] ~arg1[0,2] ~arg1[0,3] ~arg1[0,4] ~arg1[0] ~arg1[] ~arg2[0,0] ~arg2[0,2] ~arg2[0,3] ~arg2[0,4] ~arg3[0,0] ~arg3[0,1] ~arg3[0,2] ~arg3[0,3] ~arg3[0,4] ~arg3[0] ~arg3[] ~arg4[0,0] ~arg4[0,1] ~arg4[0,2] ~arg4[0,3] ~arg4[0,4] ~arg4[0] ~arg4[] ~b[0,0] ~b[0,1] ~b[0,2] ~b[0,3] ~b[0,4,1] ~c[0,0] ~c[0,1] ~c[0,2] ~c[0,3] ~c[0,4,0]
--  (arg2) <- (do
--    abc <- pure arg4
--    (a,b,c) <- (do
--      (ab,c) <- (do
--        (ab,c) <- append_ooi abc
--        pure (ab,c)
--       )
--      (a,b) <- (do
--        (a,b) <- append_ooi ab
--        pure (a,b)
--       )
--      pure (a,b,c)
--     )
--    guard $ arg1 == a
--    arg2 <- pure b
--    guard $ arg3 == c
--    pure (arg2)
--   )
--  pure (arg2)

append_iooi arg1 arg4 = do
  -- solution: a[0,0] a[0] a[] ab[0,4,1,0] ab[0,4,1] ab[0,4] ab[0] ab[] abc[0,3] abc[0] abc[] arg2[0,1] arg2[0] arg2[] arg3[0,2] arg3[0] arg3[] b[0,4,0,0] b[0,4,0] b[0,4] b[0] b[] c[0,4,1,0] c[0,4,1] c[0,4] c[0] c[] ~a[0,1] ~a[0,2] ~a[0,3] ~a[0,4,0,0] ~a[0,4,0] ~a[0,4,1] ~a[0,4] ~ab[0,0] ~ab[0,1] ~ab[0,2] ~ab[0,3] ~ab[0,4,0,0] ~ab[0,4,0] ~abc[0,0] ~abc[0,1] ~abc[0,2] ~abc[0,4,0] ~abc[0,4,1,0] ~abc[0,4,1] ~abc[0,4] ~arg1[0,0] ~arg1[0,1] ~arg1[0,2] ~arg1[0,3] ~arg1[0,4] ~arg1[0] ~arg1[] ~arg2[0,0] ~arg2[0,2] ~arg2[0,3] ~arg2[0,4] ~arg3[0,0] ~arg3[0,1] ~arg3[0,3] ~arg3[0,4] ~arg4[0,0] ~arg4[0,1] ~arg4[0,2] ~arg4[0,3] ~arg4[0,4] ~arg4[0] ~arg4[] ~b[0,0] ~b[0,1] ~b[0,2] ~b[0,3] ~b[0,4,1] ~c[0,0] ~c[0,1] ~c[0,2] ~c[0,3] ~c[0,4,0]
  (arg2,arg3) <- (do
    a <- pure arg1
    abc <- pure arg4
    (b,c) <- (do
      (ab,c) <- (do
        (ab,c) <- append_ooi abc
        pure (ab,c)
       )
      (b) <- (do
        (b) <- append_ioi a ab
        pure (b)
       )
      pure (b,c)
     )
    arg2 <- pure b
    arg3 <- pure c
    pure (arg2,arg3)
   )
  pure (arg2,arg3)

--append_iooi arg1 arg4 = do
--  -- solution: a[0,4,0,0] a[0,4,0] a[0,4] a[0] a[] ab[0,4,1,0] ab[0,4,1] ab[0,4] ab[0] ab[] abc[0,3] abc[0] abc[] arg2[0,1] arg2[0] arg2[] arg3[0,2] arg3[0] arg3[] b[0,4,0,0] b[0,4,0] b[0,4] b[0] b[] c[0,4,1,0] c[0,4,1] c[0,4] c[0] c[] ~a[0,0] ~a[0,1] ~a[0,2] ~a[0,3] ~a[0,4,1] ~ab[0,0] ~ab[0,1] ~ab[0,2] ~ab[0,3] ~ab[0,4,0,0] ~ab[0,4,0] ~abc[0,0] ~abc[0,1] ~abc[0,2] ~abc[0,4,0] ~abc[0,4,1,0] ~abc[0,4,1] ~abc[0,4] ~arg1[0,0] ~arg1[0,1] ~arg1[0,2] ~arg1[0,3] ~arg1[0,4] ~arg1[0] ~arg1[] ~arg2[0,0] ~arg2[0,2] ~arg2[0,3] ~arg2[0,4] ~arg3[0,0] ~arg3[0,1] ~arg3[0,3] ~arg3[0,4] ~arg4[0,0] ~arg4[0,1] ~arg4[0,2] ~arg4[0,3] ~arg4[0,4] ~arg4[0] ~arg4[] ~b[0,0] ~b[0,1] ~b[0,2] ~b[0,3] ~b[0,4,1] ~c[0,0] ~c[0,1] ~c[0,2] ~c[0,3] ~c[0,4,0]
--  (arg2,arg3) <- (do
--    abc <- pure arg4
--    (a,b,c) <- (do
--      (ab,c) <- (do
--        (ab,c) <- append_ooi abc
--        pure (ab,c)
--       )
--      (a,b) <- (do
--        (a,b) <- append_ooi ab
--        pure (a,b)
--       )
--      pure (a,b,c)
--     )
--    guard $ arg1 == a
--    arg2 <- pure b
--    arg3 <- pure c
--    pure (arg2,arg3)
--   )
--  pure (arg2,arg3)

append_oiii arg2 arg3 arg4 = do
  -- solution: a[0,4,0,0] a[0,4,0] a[0,4] a[0] a[] ab[0,4,1,0] ab[0,4,1] ab[0,4] ab[0] ab[] abc[0,3] abc[0] abc[] arg1[0,0] arg1[0] arg1[] b[0,1] b[0] b[] c[0,2] c[0] c[] ~a[0,0] ~a[0,1] ~a[0,2] ~a[0,3] ~a[0,4,1] ~ab[0,0] ~ab[0,1] ~ab[0,2] ~ab[0,3] ~ab[0,4,0,0] ~ab[0,4,0] ~abc[0,0] ~abc[0,1] ~abc[0,2] ~abc[0,4,0] ~abc[0,4,1,0] ~abc[0,4,1] ~abc[0,4] ~arg1[0,1] ~arg1[0,2] ~arg1[0,3] ~arg1[0,4] ~arg2[0,0] ~arg2[0,1] ~arg2[0,2] ~arg2[0,3] ~arg2[0,4] ~arg2[0] ~arg2[] ~arg3[0,0] ~arg3[0,1] ~arg3[0,2] ~arg3[0,3] ~arg3[0,4] ~arg3[0] ~arg3[] ~arg4[0,0] ~arg4[0,1] ~arg4[0,2] ~arg4[0,3] ~arg4[0,4] ~arg4[0] ~arg4[] ~b[0,0] ~b[0,2] ~b[0,3] ~b[0,4,0,0] ~b[0,4,0] ~b[0,4,1] ~b[0,4] ~c[0,0] ~c[0,1] ~c[0,3] ~c[0,4,0] ~c[0,4,1,0] ~c[0,4,1] ~c[0,4]
  (arg1) <- (do
    b <- pure arg2
    c <- pure arg3
    abc <- pure arg4
    (a) <- (do
      (ab) <- (do
        (ab) <- append_oii c abc
        pure (ab)
       )
      (a) <- (do
        (a) <- append_oii b ab
        pure (a)
       )
      pure (a)
     )
    arg1 <- pure a
    pure (arg1)
   )
  pure (arg1)

--append_oiii arg2 arg3 arg4 = do
--  -- solution: a[0,4,0,0] a[0,4,0] a[0,4] a[0] a[] ab[0,4,1,0] ab[0,4,1] ab[0,4] ab[0] ab[] abc[0,3] abc[0] abc[] arg1[0,0] arg1[0] arg1[] b[0,1] b[0] b[] c[0,4,1,0] c[0,4,1] c[0,4] c[0] c[] ~a[0,0] ~a[0,1] ~a[0,2] ~a[0,3] ~a[0,4,1] ~ab[0,0] ~ab[0,1] ~ab[0,2] ~ab[0,3] ~ab[0,4,0,0] ~ab[0,4,0] ~abc[0,0] ~abc[0,1] ~abc[0,2] ~abc[0,4,0] ~abc[0,4,1,0] ~abc[0,4,1] ~abc[0,4] ~arg1[0,1] ~arg1[0,2] ~arg1[0,3] ~arg1[0,4] ~arg2[0,0] ~arg2[0,1] ~arg2[0,2] ~arg2[0,3] ~arg2[0,4] ~arg2[0] ~arg2[] ~arg3[0,0] ~arg3[0,1] ~arg3[0,2] ~arg3[0,3] ~arg3[0,4] ~arg3[0] ~arg3[] ~arg4[0,0] ~arg4[0,1] ~arg4[0,2] ~arg4[0,3] ~arg4[0,4] ~arg4[0] ~arg4[] ~b[0,0] ~b[0,2] ~b[0,3] ~b[0,4,0,0] ~b[0,4,0] ~b[0,4,1] ~b[0,4] ~c[0,0] ~c[0,1] ~c[0,2] ~c[0,3] ~c[0,4,0]
--  (arg1) <- (do
--    b <- pure arg2
--    abc <- pure arg4
--    (a,c) <- (do
--      (ab,c) <- (do
--        (ab,c) <- append_ooi abc
--        pure (ab,c)
--       )
--      (a) <- (do
--        (a) <- append_oii b ab
--        pure (a)
--       )
--      pure (a,c)
--     )
--    arg1 <- pure a
--    guard $ arg3 == c
--    pure (arg1)
--   )
--  pure (arg1)

--append_oiii arg2 arg3 arg4 = do
--  -- solution: a[0,4,0,0] a[0,4,0] a[0,4] a[0] a[] ab[0,4,1,0] ab[0,4,1] ab[0,4] ab[0] ab[] abc[0,3] abc[0] abc[] arg1[0,0] arg1[0] arg1[] b[0,4,0,0] b[0,4,0] b[0,4] b[0] b[] c[0,2] c[0] c[] ~a[0,0] ~a[0,1] ~a[0,2] ~a[0,3] ~a[0,4,1] ~ab[0,0] ~ab[0,1] ~ab[0,2] ~ab[0,3] ~ab[0,4,0,0] ~ab[0,4,0] ~abc[0,0] ~abc[0,1] ~abc[0,2] ~abc[0,4,0] ~abc[0,4,1,0] ~abc[0,4,1] ~abc[0,4] ~arg1[0,1] ~arg1[0,2] ~arg1[0,3] ~arg1[0,4] ~arg2[0,0] ~arg2[0,1] ~arg2[0,2] ~arg2[0,3] ~arg2[0,4] ~arg2[0] ~arg2[] ~arg3[0,0] ~arg3[0,1] ~arg3[0,2] ~arg3[0,3] ~arg3[0,4] ~arg3[0] ~arg3[] ~arg4[0,0] ~arg4[0,1] ~arg4[0,2] ~arg4[0,3] ~arg4[0,4] ~arg4[0] ~arg4[] ~b[0,0] ~b[0,1] ~b[0,2] ~b[0,3] ~b[0,4,1] ~c[0,0] ~c[0,1] ~c[0,3] ~c[0,4,0] ~c[0,4,1,0] ~c[0,4,1] ~c[0,4]
--  (arg1) <- (do
--    c <- pure arg3
--    abc <- pure arg4
--    (a,b) <- (do
--      (ab) <- (do
--        (ab) <- append_oii c abc
--        pure (ab)
--       )
--      (a,b) <- (do
--        (a,b) <- append_ooi ab
--        pure (a,b)
--       )
--      pure (a,b)
--     )
--    arg1 <- pure a
--    guard $ arg2 == b
--    pure (arg1)
--   )
--  pure (arg1)

--append_oiii arg2 arg3 arg4 = do
--  -- solution: a[0,4,0,0] a[0,4,0] a[0,4] a[0] a[] ab[0,4,1,0] ab[0,4,1] ab[0,4] ab[0] ab[] abc[0,3] abc[0] abc[] arg1[0,0] arg1[0] arg1[] b[0,4,0,0] b[0,4,0] b[0,4] b[0] b[] c[0,4,1,0] c[0,4,1] c[0,4] c[0] c[] ~a[0,0] ~a[0,1] ~a[0,2] ~a[0,3] ~a[0,4,1] ~ab[0,0] ~ab[0,1] ~ab[0,2] ~ab[0,3] ~ab[0,4,0,0] ~ab[0,4,0] ~abc[0,0] ~abc[0,1] ~abc[0,2] ~abc[0,4,0] ~abc[0,4,1,0] ~abc[0,4,1] ~abc[0,4] ~arg1[0,1] ~arg1[0,2] ~arg1[0,3] ~arg1[0,4] ~arg2[0,0] ~arg2[0,1] ~arg2[0,2] ~arg2[0,3] ~arg2[0,4] ~arg2[0] ~arg2[] ~arg3[0,0] ~arg3[0,1] ~arg3[0,2] ~arg3[0,3] ~arg3[0,4] ~arg3[0] ~arg3[] ~arg4[0,0] ~arg4[0,1] ~arg4[0,2] ~arg4[0,3] ~arg4[0,4] ~arg4[0] ~arg4[] ~b[0,0] ~b[0,1] ~b[0,2] ~b[0,3] ~b[0,4,1] ~c[0,0] ~c[0,1] ~c[0,2] ~c[0,3] ~c[0,4,0]
--  (arg1) <- (do
--    abc <- pure arg4
--    (a,b,c) <- (do
--      (ab,c) <- (do
--        (ab,c) <- append_ooi abc
--        pure (ab,c)
--       )
--      (a,b) <- (do
--        (a,b) <- append_ooi ab
--        pure (a,b)
--       )
--      pure (a,b,c)
--     )
--    arg1 <- pure a
--    guard $ arg2 == b
--    guard $ arg3 == c
--    pure (arg1)
--   )
--  pure (arg1)

append_oioi arg2 arg4 = do
  -- solution: a[0,4,0,0] a[0,4,0] a[0,4] a[0] a[] ab[0,4,1,0] ab[0,4,1] ab[0,4] ab[0] ab[] abc[0,3] abc[0] abc[] arg1[0,0] arg1[0] arg1[] arg3[0,2] arg3[0] arg3[] b[0,1] b[0] b[] c[0,4,1,0] c[0,4,1] c[0,4] c[0] c[] ~a[0,0] ~a[0,1] ~a[0,2] ~a[0,3] ~a[0,4,1] ~ab[0,0] ~ab[0,1] ~ab[0,2] ~ab[0,3] ~ab[0,4,0,0] ~ab[0,4,0] ~abc[0,0] ~abc[0,1] ~abc[0,2] ~abc[0,4,0] ~abc[0,4,1,0] ~abc[0,4,1] ~abc[0,4] ~arg1[0,1] ~arg1[0,2] ~arg1[0,3] ~arg1[0,4] ~arg2[0,0] ~arg2[0,1] ~arg2[0,2] ~arg2[0,3] ~arg2[0,4] ~arg2[0] ~arg2[] ~arg3[0,0] ~arg3[0,1] ~arg3[0,3] ~arg3[0,4] ~arg4[0,0] ~arg4[0,1] ~arg4[0,2] ~arg4[0,3] ~arg4[0,4] ~arg4[0] ~arg4[] ~b[0,0] ~b[0,2] ~b[0,3] ~b[0,4,0,0] ~b[0,4,0] ~b[0,4,1] ~b[0,4] ~c[0,0] ~c[0,1] ~c[0,2] ~c[0,3] ~c[0,4,0]
  (arg1,arg3) <- (do
    b <- pure arg2
    abc <- pure arg4
    (a,c) <- (do
      (ab,c) <- (do
        (ab,c) <- append_ooi abc
        pure (ab,c)
       )
      (a) <- (do
        (a) <- append_oii b ab
        pure (a)
       )
      pure (a,c)
     )
    arg1 <- pure a
    arg3 <- pure c
    pure (arg1,arg3)
   )
  pure (arg1,arg3)

--append_oioi arg2 arg4 = do
--  -- solution: a[0,4,0,0] a[0,4,0] a[0,4] a[0] a[] ab[0,4,1,0] ab[0,4,1] ab[0,4] ab[0] ab[] abc[0,3] abc[0] abc[] arg1[0,0] arg1[0] arg1[] arg3[0,2] arg3[0] arg3[] b[0,4,0,0] b[0,4,0] b[0,4] b[0] b[] c[0,4,1,0] c[0,4,1] c[0,4] c[0] c[] ~a[0,0] ~a[0,1] ~a[0,2] ~a[0,3] ~a[0,4,1] ~ab[0,0] ~ab[0,1] ~ab[0,2] ~ab[0,3] ~ab[0,4,0,0] ~ab[0,4,0] ~abc[0,0] ~abc[0,1] ~abc[0,2] ~abc[0,4,0] ~abc[0,4,1,0] ~abc[0,4,1] ~abc[0,4] ~arg1[0,1] ~arg1[0,2] ~arg1[0,3] ~arg1[0,4] ~arg2[0,0] ~arg2[0,1] ~arg2[0,2] ~arg2[0,3] ~arg2[0,4] ~arg2[0] ~arg2[] ~arg3[0,0] ~arg3[0,1] ~arg3[0,3] ~arg3[0,4] ~arg4[0,0] ~arg4[0,1] ~arg4[0,2] ~arg4[0,3] ~arg4[0,4] ~arg4[0] ~arg4[] ~b[0,0] ~b[0,1] ~b[0,2] ~b[0,3] ~b[0,4,1] ~c[0,0] ~c[0,1] ~c[0,2] ~c[0,3] ~c[0,4,0]
--  (arg1,arg3) <- (do
--    abc <- pure arg4
--    (a,b,c) <- (do
--      (ab,c) <- (do
--        (ab,c) <- append_ooi abc
--        pure (ab,c)
--       )
--      (a,b) <- (do
--        (a,b) <- append_ooi ab
--        pure (a,b)
--       )
--      pure (a,b,c)
--     )
--    arg1 <- pure a
--    guard $ arg2 == b
--    arg3 <- pure c
--    pure (arg1,arg3)
--   )
--  pure (arg1,arg3)

append_ooii arg3 arg4 = do
  -- solution: a[0,4,0,0] a[0,4,0] a[0,4] a[0] a[] ab[0,4,1,0] ab[0,4,1] ab[0,4] ab[0] ab[] abc[0,3] abc[0] abc[] arg1[0,0] arg1[0] arg1[] arg2[0,1] arg2[0] arg2[] b[0,4,0,0] b[0,4,0] b[0,4] b[0] b[] c[0,2] c[0] c[] ~a[0,0] ~a[0,1] ~a[0,2] ~a[0,3] ~a[0,4,1] ~ab[0,0] ~ab[0,1] ~ab[0,2] ~ab[0,3] ~ab[0,4,0,0] ~ab[0,4,0] ~abc[0,0] ~abc[0,1] ~abc[0,2] ~abc[0,4,0] ~abc[0,4,1,0] ~abc[0,4,1] ~abc[0,4] ~arg1[0,1] ~arg1[0,2] ~arg1[0,3] ~arg1[0,4] ~arg2[0,0] ~arg2[0,2] ~arg2[0,3] ~arg2[0,4] ~arg3[0,0] ~arg3[0,1] ~arg3[0,2] ~arg3[0,3] ~arg3[0,4] ~arg3[0] ~arg3[] ~arg4[0,0] ~arg4[0,1] ~arg4[0,2] ~arg4[0,3] ~arg4[0,4] ~arg4[0] ~arg4[] ~b[0,0] ~b[0,1] ~b[0,2] ~b[0,3] ~b[0,4,1] ~c[0,0] ~c[0,1] ~c[0,3] ~c[0,4,0] ~c[0,4,1,0] ~c[0,4,1] ~c[0,4]
  (arg1,arg2) <- (do
    c <- pure arg3
    abc <- pure arg4
    (a,b) <- (do
      (ab) <- (do
        (ab) <- append_oii c abc
        pure (ab)
       )
      (a,b) <- (do
        (a,b) <- append_ooi ab
        pure (a,b)
       )
      pure (a,b)
     )
    arg1 <- pure a
    arg2 <- pure b
    pure (arg1,arg2)
   )
  pure (arg1,arg2)

--append_ooii arg3 arg4 = do
--  -- solution: a[0,4,0,0] a[0,4,0] a[0,4] a[0] a[] ab[0,4,1,0] ab[0,4,1] ab[0,4] ab[0] ab[] abc[0,3] abc[0] abc[] arg1[0,0] arg1[0] arg1[] arg2[0,1] arg2[0] arg2[] b[0,4,0,0] b[0,4,0] b[0,4] b[0] b[] c[0,4,1,0] c[0,4,1] c[0,4] c[0] c[] ~a[0,0] ~a[0,1] ~a[0,2] ~a[0,3] ~a[0,4,1] ~ab[0,0] ~ab[0,1] ~ab[0,2] ~ab[0,3] ~ab[0,4,0,0] ~ab[0,4,0] ~abc[0,0] ~abc[0,1] ~abc[0,2] ~abc[0,4,0] ~abc[0,4,1,0] ~abc[0,4,1] ~abc[0,4] ~arg1[0,1] ~arg1[0,2] ~arg1[0,3] ~arg1[0,4] ~arg2[0,0] ~arg2[0,2] ~arg2[0,3] ~arg2[0,4] ~arg3[0,0] ~arg3[0,1] ~arg3[0,2] ~arg3[0,3] ~arg3[0,4] ~arg3[0] ~arg3[] ~arg4[0,0] ~arg4[0,1] ~arg4[0,2] ~arg4[0,3] ~arg4[0,4] ~arg4[0] ~arg4[] ~b[0,0] ~b[0,1] ~b[0,2] ~b[0,3] ~b[0,4,1] ~c[0,0] ~c[0,1] ~c[0,2] ~c[0,3] ~c[0,4,0]
--  (arg1,arg2) <- (do
--    abc <- pure arg4
--    (a,b,c) <- (do
--      (ab,c) <- (do
--        (ab,c) <- append_ooi abc
--        pure (ab,c)
--       )
--      (a,b) <- (do
--        (a,b) <- append_ooi ab
--        pure (a,b)
--       )
--      pure (a,b,c)
--     )
--    arg1 <- pure a
--    arg2 <- pure b
--    guard $ arg3 == c
--    pure (arg1,arg2)
--   )
--  pure (arg1,arg2)

append_oooi arg4 = do
  -- solution: a[0,4,0,0] a[0,4,0] a[0,4] a[0] a[] ab[0,4,1,0] ab[0,4,1] ab[0,4] ab[0] ab[] abc[0,3] abc[0] abc[] arg1[0,0] arg1[0] arg1[] arg2[0,1] arg2[0] arg2[] arg3[0,2] arg3[0] arg3[] b[0,4,0,0] b[0,4,0] b[0,4] b[0] b[] c[0,4,1,0] c[0,4,1] c[0,4] c[0] c[] ~a[0,0] ~a[0,1] ~a[0,2] ~a[0,3] ~a[0,4,1] ~ab[0,0] ~ab[0,1] ~ab[0,2] ~ab[0,3] ~ab[0,4,0,0] ~ab[0,4,0] ~abc[0,0] ~abc[0,1] ~abc[0,2] ~abc[0,4,0] ~abc[0,4,1,0] ~abc[0,4,1] ~abc[0,4] ~arg1[0,1] ~arg1[0,2] ~arg1[0,3] ~arg1[0,4] ~arg2[0,0] ~arg2[0,2] ~arg2[0,3] ~arg2[0,4] ~arg3[0,0] ~arg3[0,1] ~arg3[0,3] ~arg3[0,4] ~arg4[0,0] ~arg4[0,1] ~arg4[0,2] ~arg4[0,3] ~arg4[0,4] ~arg4[0] ~arg4[] ~b[0,0] ~b[0,1] ~b[0,2] ~b[0,3] ~b[0,4,1] ~c[0,0] ~c[0,1] ~c[0,2] ~c[0,3] ~c[0,4,0]
  (arg1,arg2,arg3) <- (do
    abc <- pure arg4
    (a,b,c) <- (do
      (ab,c) <- (do
        (ab,c) <- append_ooi abc
        pure (ab,c)
       )
      (a,b) <- (do
        (a,b) <- append_ooi ab
        pure (a,b)
       )
      pure (a,b,c)
     )
    arg1 <- pure a
    arg2 <- pure b
    arg3 <- pure c
    pure (arg1,arg2,arg3)
   )
  pure (arg1,arg2,arg3)

{- reverse/2
reverse arg1 arg2 :- (((arg1 = []), (arg2 = []), ()); ((arg1 = h0 : t, h0 = h), arg2 = l, ((reverse t r), ((append r data1 l), (data0 = []), (data1 = h1 : data0, h1 = h))))).
constraints:
data0[1,2,1]
data0[1,2]
data0[1]
data0[]
data1[1,2,1]
data1[1,2]
data1[1]
data1[]
h0[1,0]
h0[1]
h0[]
h1[1,2,1,2]
h1[1,2,1]
h1[1,2]
h1[1]
h1[]
h[1]
h[]
l[1]
l[]
r[1,2]
r[1]
r[]
t[1]
t[]
~arg1[0,1]
~arg1[0,2]
~arg1[1,0,1]
~arg1[1,1]
~arg1[1,2]
~arg2[0,0]
~arg2[0,2]
~arg2[1,0]
~arg2[1,2]
~data0[0]
~data0[1,0]
~data0[1,1]
~data0[1,2,0]
~data0[1,2,1,0]
~data0[1,2,1,2,1]
~data1[0]
~data1[1,0]
~data1[1,1]
~data1[1,2,0]
~data1[1,2,1,1]
~data1[1,2,1,2,1]
~h0[0]
~h0[1,1]
~h0[1,2]
~h1[0]
~h1[1,0]
~h1[1,1]
~h1[1,2,0]
~h1[1,2,1,0]
~h1[1,2,1,1]
~h[0]
~h[1,0,0]
~h[1,1]
~h[1,2,0]
~h[1,2,1,0]
~h[1,2,1,1]
~h[1,2,1,2,0]
~l[0]
~l[1,0]
~l[1,2,0]
~l[1,2,1,1]
~l[1,2,1,2]
~r[0]
~r[1,0]
~r[1,1]
~r[1,2,1,1]
~r[1,2,1,2]
~t[0]
~t[1,0,1]
~t[1,1]
~t[1,2,1]
~(arg1[1,0,0] & h0[1,0,0])
~(arg2[1,1] & l[1,1])
~(data0[1,2,1,1] & data0[1,2,1,2])
~(data1[1,2,1,0] & data1[1,2,1,2])
~(data1[1,2,1,2,0] & h1[1,2,1,2,0])
~(h0[1,0,0] & h0[1,0,1])
~(h0[1,0,1] & h[1,0,1])
~(h1[1,2,1,2,0] & h1[1,2,1,2,1])
~(h1[1,2,1,2,1] & h[1,2,1,2,1])
~(h[1,0] & h[1,2])
~(l[1,1] & l[1,2])
~(r[1,2,0] & r[1,2,1])
~(t[1,0] & t[1,2])
((r[1,2,1,0,0] & (data1[1,2,1,0,0] & ~l[1,2,1,0,0])) | ((r[1,2,1,0,0] & (~data1[1,2,1,0,0] & ~l[1,2,1,0,0])) | ((~r[1,2,1,0,0] & (data1[1,2,1,0,0] & ~l[1,2,1,0,0])) | ((~r[1,2,1,0,0] & (~data1[1,2,1,0,0] & l[1,2,1,0,0])) | (~r[1,2,1,0,0] & (~data1[1,2,1,0,0] & ~l[1,2,1,0,0]))))))
(arg1[0,0] <-> arg1[0,0,0])
(arg1[0] <-> arg1[0,0])
(arg1[1,0] <-> arg1[1,0,0])
(arg1[1] <-> arg1[1,0])
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg2[0,1] <-> arg2[0,1,0])
(arg2[0] <-> arg2[0,1])
(arg2[1] <-> arg2[1,1])
(arg2[] <-> arg2[0])
(arg2[] <-> arg2[1])
(data0[1,2,1,1] <-> data0[1,2,1,1,0])
(data0[1,2,1,2] <-> data0[1,2,1,2,0])
(data0[1,2,1] <-> (data0[1,2,1,1] | data0[1,2,1,2]))
(data0[1,2] <-> data0[1,2,1])
(data0[1] <-> data0[1,2])
(data1[1,2,1,0] <-> data1[1,2,1,0,0])
(data1[1,2,1,2] <-> data1[1,2,1,2,0])
(data1[1,2,1] <-> (data1[1,2,1,0] | data1[1,2,1,2]))
(data1[1,2] <-> data1[1,2,1])
(data1[1] <-> data1[1,2])
(h0[1,0,0] <-> t[1,0,0])
(h0[1,0] <-> (h0[1,0,0] | h0[1,0,1]))
(h0[1] <-> h0[1,0])
(h1[1,2,1,2,0] <-> data0[1,2,1,2,0])
(h1[1,2,1,2] <-> (h1[1,2,1,2,0] | h1[1,2,1,2,1]))
(h1[1,2,1] <-> h1[1,2,1,2])
(h1[1,2] <-> h1[1,2,1])
(h1[1] <-> h1[1,2])
(h[1,0] <-> h[1,0,1])
(h[1,2,1,2] <-> h[1,2,1,2,1])
(h[1,2,1] <-> h[1,2,1,2])
(h[1,2] <-> h[1,2,1])
(h[1] <-> (h[1,0] | h[1,2]))
(l[1,2,1,0] <-> l[1,2,1,0,0])
(l[1,2,1] <-> l[1,2,1,0])
(l[1,2] <-> l[1,2,1])
(l[1] <-> (l[1,1] | l[1,2]))
(r[1,2,0,0] <-> arg2[])
(r[1,2,0] <-> r[1,2,0,0])
(r[1,2,1,0] <-> r[1,2,1,0,0])
(r[1,2,1] <-> r[1,2,1,0])
(r[1,2] <-> (r[1,2,0] | r[1,2,1]))
(r[1] <-> r[1,2])
(t[1,0] <-> t[1,0,0])
(t[1,2,0,0] <-> arg1[])
(t[1,2,0] <-> t[1,2,0,0])
(t[1,2] <-> t[1,2,0])
(t[1] <-> (t[1,0] | t[1,2]))
-}
-- mode ordering failure, cyclic dependency: [2] (((append r::out data1::out l::in), (data1::in = h1::out : data0::out, h1::in = h::out), (data0::in = [])), (reverse t::in r::in)) -> [0] (arg1::in = h0::out : t::out, h0::in = h::in)
reverse_ii arg1 arg2 = do
  -- solution: data0[1,2,1,1,0] data0[1,2,1,1] data0[1,2,1] data0[1,2] data0[1] data0[] data1[1,2,1,0,0] data1[1,2,1,0] data1[1,2,1] data1[1,2] data1[1] data1[] h0[1,0,0] h0[1,0] h0[1] h0[] h1[1,2,1,2,1] h1[1,2,1,2] h1[1,2,1] h1[1,2] h1[1] h1[] h[1,0,1] h[1,0] h[1] h[] l[1,1] l[1] l[] r[1,2,1,0,0] r[1,2,1,0] r[1,2,1] r[1,2] r[1] r[] t[1,0,0] t[1,0] t[1] t[] ~arg1[0,0,0] ~arg1[0,0] ~arg1[0,1] ~arg1[0,2] ~arg1[0] ~arg1[1,0,0] ~arg1[1,0,1] ~arg1[1,0] ~arg1[1,1] ~arg1[1,2] ~arg1[1] ~arg1[] ~arg2[0,0] ~arg2[0,1,0] ~arg2[0,1] ~arg2[0,2] ~arg2[0] ~arg2[1,0] ~arg2[1,1] ~arg2[1,2] ~arg2[1] ~arg2[] ~data0[0] ~data0[1,0] ~data0[1,1] ~data0[1,2,0] ~data0[1,2,1,0] ~data0[1,2,1,2,0] ~data0[1,2,1,2,1] ~data0[1,2,1,2] ~data1[0] ~data1[1,0] ~data1[1,1] ~data1[1,2,0] ~data1[1,2,1,1] ~data1[1,2,1,2,0] ~data1[1,2,1,2,1] ~data1[1,2,1,2] ~h0[0] ~h0[1,0,1] ~h0[1,1] ~h0[1,2] ~h1[0] ~h1[1,0] ~h1[1,1] ~h1[1,2,0] ~h1[1,2,1,0] ~h1[1,2,1,1] ~h1[1,2,1,2,0] ~h[0] ~h[1,0,0] ~h[1,1] ~h[1,2,0] ~h[1,2,1,0] ~h[1,2,1,1] ~h[1,2,1,2,0] ~h[1,2,1,2,1] ~h[1,2,1,2] ~h[1,2,1] ~h[1,2] ~l[0] ~l[1,0] ~l[1,2,0] ~l[1,2,1,0,0] ~l[1,2,1,0] ~l[1,2,1,1] ~l[1,2,1,2] ~l[1,2,1] ~l[1,2] ~r[0] ~r[1,0] ~r[1,1] ~r[1,2,0,0] ~r[1,2,0] ~r[1,2,1,1] ~r[1,2,1,2] ~t[0] ~t[1,0,1] ~t[1,1] ~t[1,2,0,0] ~t[1,2,0] ~t[1,2,1] ~t[1,2]
  () <- (do
    () <- (do
      guard $ arg1 == []
      pure ()
     )
    () <- (do
      guard $ arg2 == []
      pure ()
     )
    () <- (do
      
      pure ()
     )
    pure ()
   ) <|> (do
    (h,t) <- (do
      (h0:t) <- pure arg1
      h <- pure h0
      pure (h,t)
     )
    l <- pure arg2
    () <- (do
      (r) <- (do
        (data1,r) <- (do
          (r,data1) <- append_ooi l
          pure (data1,r)
         )
        (data0) <- (do
          data0 <- pure []
          pure (data0)
         )
        () <- (do
          h1 <- pure h
          guard $ data1 == (h1:data0)
          pure ()
         )
        pure (r)
       )
      () <- (do
        () <- reverse_ii t r
        pure ()
       )
      pure ()
     )
    pure ()
   )
  pure ()

--reverse_ii arg1 arg2 = do
--  -- solution: data0[1,2,1,1,0] data0[1,2,1,1] data0[1,2,1] data0[1,2] data0[1] data0[] data1[1,2,1,2,0] data1[1,2,1,2] data1[1,2,1] data1[1,2] data1[1] data1[] h0[1,0,0] h0[1,0] h0[1] h0[] h1[1,2,1,2,1] h1[1,2,1,2] h1[1,2,1] h1[1,2] h1[1] h1[] h[1,0,1] h[1,0] h[1] h[] l[1,1] l[1] l[] r[1,2,1,0,0] r[1,2,1,0] r[1,2,1] r[1,2] r[1] r[] t[1,0,0] t[1,0] t[1] t[] ~arg1[0,0,0] ~arg1[0,0] ~arg1[0,1] ~arg1[0,2] ~arg1[0] ~arg1[1,0,0] ~arg1[1,0,1] ~arg1[1,0] ~arg1[1,1] ~arg1[1,2] ~arg1[1] ~arg1[] ~arg2[0,0] ~arg2[0,1,0] ~arg2[0,1] ~arg2[0,2] ~arg2[0] ~arg2[1,0] ~arg2[1,1] ~arg2[1,2] ~arg2[1] ~arg2[] ~data0[0] ~data0[1,0] ~data0[1,1] ~data0[1,2,0] ~data0[1,2,1,0] ~data0[1,2,1,2,0] ~data0[1,2,1,2,1] ~data0[1,2,1,2] ~data1[0] ~data1[1,0] ~data1[1,1] ~data1[1,2,0] ~data1[1,2,1,0,0] ~data1[1,2,1,0] ~data1[1,2,1,1] ~data1[1,2,1,2,1] ~h0[0] ~h0[1,0,1] ~h0[1,1] ~h0[1,2] ~h1[0] ~h1[1,0] ~h1[1,1] ~h1[1,2,0] ~h1[1,2,1,0] ~h1[1,2,1,1] ~h1[1,2,1,2,0] ~h[0] ~h[1,0,0] ~h[1,1] ~h[1,2,0] ~h[1,2,1,0] ~h[1,2,1,1] ~h[1,2,1,2,0] ~h[1,2,1,2,1] ~h[1,2,1,2] ~h[1,2,1] ~h[1,2] ~l[0] ~l[1,0] ~l[1,2,0] ~l[1,2,1,0,0] ~l[1,2,1,0] ~l[1,2,1,1] ~l[1,2,1,2] ~l[1,2,1] ~l[1,2] ~r[0] ~r[1,0] ~r[1,1] ~r[1,2,0,0] ~r[1,2,0] ~r[1,2,1,1] ~r[1,2,1,2] ~t[0] ~t[1,0,1] ~t[1,1] ~t[1,2,0,0] ~t[1,2,0] ~t[1,2,1] ~t[1,2]
--  () <- (do
--    () <- (do
--      guard $ arg1 == []
--      pure ()
--     )
--    () <- (do
--      guard $ arg2 == []
--      pure ()
--     )
--    () <- (do
--      
--      pure ()
--     )
--    pure ()
--   ) <|> (do
--    (h,t) <- (do
--      (h0:t) <- pure arg1
--      h <- pure h0
--      pure (h,t)
--     )
--    l <- pure arg2
--    () <- (do
--      (r) <- (do
--        (data0) <- (do
--          data0 <- pure []
--          pure (data0)
--         )
--        (data1) <- (do
--          h1 <- pure h
--          data1 <- pure (h1:data0)
--          pure (data1)
--         )
--        (r) <- (do
--          (r) <- append_oii data1 l
--          pure (r)
--         )
--        pure (r)
--       )
--      () <- (do
--        () <- reverse_ii t r
--        pure ()
--       )
--      pure ()
--     )
--    pure ()
--   )
--  pure ()

--reverse_ii arg1 arg2 = do
--  -- solution: data0[1,2,1,2,0] data0[1,2,1,2] data0[1,2,1] data0[1,2] data0[1] data0[] data1[1,2,1,0,0] data1[1,2,1,0] data1[1,2,1] data1[1,2] data1[1] data1[] h0[1,0,0] h0[1,0] h0[1] h0[] h1[1,2,1,2,0] h1[1,2,1,2] h1[1,2,1] h1[1,2] h1[1] h1[] h[1,0,1] h[1,0] h[1] h[] l[1,1] l[1] l[] r[1,2,1,0,0] r[1,2,1,0] r[1,2,1] r[1,2] r[1] r[] t[1,0,0] t[1,0] t[1] t[] ~arg1[0,0,0] ~arg1[0,0] ~arg1[0,1] ~arg1[0,2] ~arg1[0] ~arg1[1,0,0] ~arg1[1,0,1] ~arg1[1,0] ~arg1[1,1] ~arg1[1,2] ~arg1[1] ~arg1[] ~arg2[0,0] ~arg2[0,1,0] ~arg2[0,1] ~arg2[0,2] ~arg2[0] ~arg2[1,0] ~arg2[1,1] ~arg2[1,2] ~arg2[1] ~arg2[] ~data0[0] ~data0[1,0] ~data0[1,1] ~data0[1,2,0] ~data0[1,2,1,0] ~data0[1,2,1,1,0] ~data0[1,2,1,1] ~data0[1,2,1,2,1] ~data1[0] ~data1[1,0] ~data1[1,1] ~data1[1,2,0] ~data1[1,2,1,1] ~data1[1,2,1,2,0] ~data1[1,2,1,2,1] ~data1[1,2,1,2] ~h0[0] ~h0[1,0,1] ~h0[1,1] ~h0[1,2] ~h1[0] ~h1[1,0] ~h1[1,1] ~h1[1,2,0] ~h1[1,2,1,0] ~h1[1,2,1,1] ~h1[1,2,1,2,1] ~h[0] ~h[1,0,0] ~h[1,1] ~h[1,2,0] ~h[1,2,1,0] ~h[1,2,1,1] ~h[1,2,1,2,0] ~h[1,2,1,2,1] ~h[1,2,1,2] ~h[1,2,1] ~h[1,2] ~l[0] ~l[1,0] ~l[1,2,0] ~l[1,2,1,0,0] ~l[1,2,1,0] ~l[1,2,1,1] ~l[1,2,1,2] ~l[1,2,1] ~l[1,2] ~r[0] ~r[1,0] ~r[1,1] ~r[1,2,0,0] ~r[1,2,0] ~r[1,2,1,1] ~r[1,2,1,2] ~t[0] ~t[1,0,1] ~t[1,1] ~t[1,2,0,0] ~t[1,2,0] ~t[1,2,1] ~t[1,2]
--  () <- (do
--    () <- (do
--      guard $ arg1 == []
--      pure ()
--     )
--    () <- (do
--      guard $ arg2 == []
--      pure ()
--     )
--    () <- (do
--      
--      pure ()
--     )
--    pure ()
--   ) <|> (do
--    (h,t) <- (do
--      (h0:t) <- pure arg1
--      h <- pure h0
--      pure (h,t)
--     )
--    l <- pure arg2
--    () <- (do
--      (r) <- (do
--        (data1,r) <- (do
--          (r,data1) <- append_ooi l
--          pure (data1,r)
--         )
--        (data0) <- (do
--          (h1:data0) <- pure data1
--          guard $ h1 == h
--          pure (data0)
--         )
--        () <- (do
--          guard $ data0 == []
--          pure ()
--         )
--        pure (r)
--       )
--      () <- (do
--        () <- reverse_ii t r
--        pure ()
--       )
--      pure ()
--     )
--    pure ()
--   )
--  pure ()

reverse_io arg1 = do
  -- solution: arg2[0,1,0] arg2[0,1] arg2[0] arg2[1,1] arg2[1] arg2[] data0[1,2,1,1,0] data0[1,2,1,1] data0[1,2,1] data0[1,2] data0[1] data0[] data1[1,2,1,2,0] data1[1,2,1,2] data1[1,2,1] data1[1,2] data1[1] data1[] h0[1,0,0] h0[1,0] h0[1] h0[] h1[1,2,1,2,1] h1[1,2,1,2] h1[1,2,1] h1[1,2] h1[1] h1[] h[1,0,1] h[1,0] h[1] h[] l[1,2,1,0,0] l[1,2,1,0] l[1,2,1] l[1,2] l[1] l[] r[1,2,0,0] r[1,2,0] r[1,2] r[1] r[] t[1,0,0] t[1,0] t[1] t[] ~arg1[0,0,0] ~arg1[0,0] ~arg1[0,1] ~arg1[0,2] ~arg1[0] ~arg1[1,0,0] ~arg1[1,0,1] ~arg1[1,0] ~arg1[1,1] ~arg1[1,2] ~arg1[1] ~arg1[] ~arg2[0,0] ~arg2[0,2] ~arg2[1,0] ~arg2[1,2] ~data0[0] ~data0[1,0] ~data0[1,1] ~data0[1,2,0] ~data0[1,2,1,0] ~data0[1,2,1,2,0] ~data0[1,2,1,2,1] ~data0[1,2,1,2] ~data1[0] ~data1[1,0] ~data1[1,1] ~data1[1,2,0] ~data1[1,2,1,0,0] ~data1[1,2,1,0] ~data1[1,2,1,1] ~data1[1,2,1,2,1] ~h0[0] ~h0[1,0,1] ~h0[1,1] ~h0[1,2] ~h1[0] ~h1[1,0] ~h1[1,1] ~h1[1,2,0] ~h1[1,2,1,0] ~h1[1,2,1,1] ~h1[1,2,1,2,0] ~h[0] ~h[1,0,0] ~h[1,1] ~h[1,2,0] ~h[1,2,1,0] ~h[1,2,1,1] ~h[1,2,1,2,0] ~h[1,2,1,2,1] ~h[1,2,1,2] ~h[1,2,1] ~h[1,2] ~l[0] ~l[1,0] ~l[1,1] ~l[1,2,0] ~l[1,2,1,1] ~l[1,2,1,2] ~r[0] ~r[1,0] ~r[1,1] ~r[1,2,1,0,0] ~r[1,2,1,0] ~r[1,2,1,1] ~r[1,2,1,2] ~r[1,2,1] ~t[0] ~t[1,0,1] ~t[1,1] ~t[1,2,0,0] ~t[1,2,0] ~t[1,2,1] ~t[1,2]
  (arg2) <- (do
    () <- (do
      guard $ arg1 == []
      pure ()
     )
    (arg2) <- (do
      arg2 <- pure []
      pure (arg2)
     )
    () <- (do
      
      pure ()
     )
    pure (arg2)
   ) <|> (do
    (h,t) <- (do
      (h0:t) <- pure arg1
      h <- pure h0
      pure (h,t)
     )
    (l) <- (do
      (r) <- (do
        (r) <- reverse_io t
        pure (r)
       )
      (l) <- (do
        (data0) <- (do
          data0 <- pure []
          pure (data0)
         )
        (data1) <- (do
          h1 <- pure h
          data1 <- pure (h1:data0)
          pure (data1)
         )
        (l) <- (do
          (l) <- append_iio r data1
          pure (l)
         )
        pure (l)
       )
      pure (l)
     )
    arg2 <- pure l
    pure (arg2)
   )
  pure (arg2)

reverse_oi arg2 = do
  -- solution: arg1[0,0,0] arg1[0,0] arg1[0] arg1[1,0,0] arg1[1,0] arg1[1] arg1[] data0[1,2,1,2,0] data0[1,2,1,2] data0[1,2,1] data0[1,2] data0[1] data0[] data1[1,2,1,0,0] data1[1,2,1,0] data1[1,2,1] data1[1,2] data1[1] data1[] h0[1,0,1] h0[1,0] h0[1] h0[] h1[1,2,1,2,0] h1[1,2,1,2] h1[1,2,1] h1[1,2] h1[1] h1[] h[1,2,1,2,1] h[1,2,1,2] h[1,2,1] h[1,2] h[1] h[] l[1,1] l[1] l[] r[1,2,1,0,0] r[1,2,1,0] r[1,2,1] r[1,2] r[1] r[] t[1,2,0,0] t[1,2,0] t[1,2] t[1] t[] ~arg1[0,1] ~arg1[0,2] ~arg1[1,0,1] ~arg1[1,1] ~arg1[1,2] ~arg2[0,0] ~arg2[0,1,0] ~arg2[0,1] ~arg2[0,2] ~arg2[0] ~arg2[1,0] ~arg2[1,1] ~arg2[1,2] ~arg2[1] ~arg2[] ~data0[0] ~data0[1,0] ~data0[1,1] ~data0[1,2,0] ~data0[1,2,1,0] ~data0[1,2,1,1,0] ~data0[1,2,1,1] ~data0[1,2,1,2,1] ~data1[0] ~data1[1,0] ~data1[1,1] ~data1[1,2,0] ~data1[1,2,1,1] ~data1[1,2,1,2,0] ~data1[1,2,1,2,1] ~data1[1,2,1,2] ~h0[0] ~h0[1,0,0] ~h0[1,1] ~h0[1,2] ~h1[0] ~h1[1,0] ~h1[1,1] ~h1[1,2,0] ~h1[1,2,1,0] ~h1[1,2,1,1] ~h1[1,2,1,2,1] ~h[0] ~h[1,0,0] ~h[1,0,1] ~h[1,0] ~h[1,1] ~h[1,2,0] ~h[1,2,1,0] ~h[1,2,1,1] ~h[1,2,1,2,0] ~l[0] ~l[1,0] ~l[1,2,0] ~l[1,2,1,0,0] ~l[1,2,1,0] ~l[1,2,1,1] ~l[1,2,1,2] ~l[1,2,1] ~l[1,2] ~r[0] ~r[1,0] ~r[1,1] ~r[1,2,0,0] ~r[1,2,0] ~r[1,2,1,1] ~r[1,2,1,2] ~t[0] ~t[1,0,0] ~t[1,0,1] ~t[1,0] ~t[1,1] ~t[1,2,1]
  (arg1) <- (do
    (arg1) <- (do
      arg1 <- pure []
      pure (arg1)
     )
    () <- (do
      guard $ arg2 == []
      pure ()
     )
    () <- (do
      
      pure ()
     )
    pure (arg1)
   ) <|> (do
    l <- pure arg2
    (h,t) <- (do
      (h,r) <- (do
        (data1,r) <- (do
          (r,data1) <- append_ooi l
          pure (data1,r)
         )
        (data0,h) <- (do
          (h1:data0) <- pure data1
          h <- pure h1
          pure (data0,h)
         )
        () <- (do
          guard $ data0 == []
          pure ()
         )
        pure (h,r)
       )
      (t) <- (do
        (t) <- reverse_oi r
        pure (t)
       )
      pure (h,t)
     )
    (arg1) <- (do
      h0 <- pure h
      arg1 <- pure (h0:t)
      pure (arg1)
     )
    pure (arg1)
   )
  pure (arg1)

{- palindrome/1
palindrome arg1 :- ((arg1 = a, ((reverse a0 a1, a0 = a, a1 = a)))).
constraints:
a0[0,1,0]
a0[0,1]
a0[0]
a0[]
a1[0,1,0]
a1[0,1]
a1[0]
a1[]
a[0]
a[]
~a0[0,0]
~a0[0,1,0,2]
~a1[0,0]
~a1[0,1,0,1]
~a[0,1,0,0]
~arg1[0,1]
~(a0[0,1,0,0] & a0[0,1,0,1])
~(a0[0,1,0,1] & a[0,1,0,1])
~(a1[0,1,0,0] & a1[0,1,0,2])
~(a1[0,1,0,2] & a[0,1,0,2])
~(a[0,0] & a[0,1])
~(a[0,1,0,1] & a[0,1,0,2])
~(arg1[0,0] & a[0,0])
((a0[0,1,0,0] & ~a1[0,1,0,0]) | ((~a0[0,1,0,0] & a1[0,1,0,0]) | (~a0[0,1,0,0] & ~a1[0,1,0,0])))
(a0[0,1,0] <-> (a0[0,1,0,0] | a0[0,1,0,1]))
(a0[0,1] <-> a0[0,1,0])
(a0[0] <-> a0[0,1])
(a1[0,1,0] <-> (a1[0,1,0,0] | a1[0,1,0,2]))
(a1[0,1] <-> a1[0,1,0])
(a1[0] <-> a1[0,1])
(a[0,1,0] <-> (a[0,1,0,1] | a[0,1,0,2]))
(a[0,1] <-> a[0,1,0])
(a[0] <-> (a[0,0] | a[0,1]))
(arg1[0] <-> arg1[0,0])
(arg1[] <-> arg1[0])
-}
-- mode ordering failure, cyclic dependency: [2] a1::in = a::out -> [1] a0::out = a::in -> [0] reverse a0::in a1::out
-- mode ordering failure, cyclic dependency: [2] a1::in = a::out -> [1] a0::out = a::in -> [0] reverse a0::in a1::out

-- mode ordering failure, cyclic dependency: [2] a1::out = a::in -> [0] reverse a0::out a1::in -> [1] a0::in = a::out

-- mode ordering failure, cyclic dependency: [2] a1::out = a::in -> [0] reverse a0::out a1::in -> [1] a0::in = a::out

palindrome_i arg1 = do
  -- solution: a0[0,1,0,0] a0[0,1,0] a0[0,1] a0[0] a0[] a1[0,1,0,2] a1[0,1,0] a1[0,1] a1[0] a1[] a[0,0] a[0] a[] ~a0[0,0] ~a0[0,1,0,1] ~a0[0,1,0,2] ~a1[0,0] ~a1[0,1,0,0] ~a1[0,1,0,1] ~a[0,1,0,0] ~a[0,1,0,1] ~a[0,1,0,2] ~a[0,1,0] ~a[0,1] ~arg1[0,0] ~arg1[0,1] ~arg1[0] ~arg1[]
  () <- (do
    a <- pure arg1
    () <- (do
      () <- (do
        a1 <- pure a
        (a0) <- reverse_oi a1
        guard $ a0 == a
        pure ()
       )
      pure ()
     )
    pure ()
   )
  pure ()

--palindrome_i arg1 = do
--  -- solution: a0[0,1,0,1] a0[0,1,0] a0[0,1] a0[0] a0[] a1[0,1,0,0] a1[0,1,0] a1[0,1] a1[0] a1[] a[0,0] a[0] a[] ~a0[0,0] ~a0[0,1,0,0] ~a0[0,1,0,2] ~a1[0,0] ~a1[0,1,0,1] ~a1[0,1,0,2] ~a[0,1,0,0] ~a[0,1,0,1] ~a[0,1,0,2] ~a[0,1,0] ~a[0,1] ~arg1[0,0] ~arg1[0,1] ~arg1[0] ~arg1[]
--  () <- (do
--    a <- pure arg1
--    () <- (do
--      () <- (do
--        a0 <- pure a
--        (a1) <- reverse_io a0
--        guard $ a1 == a
--        pure ()
--       )
--      pure ()
--     )
--    pure ()
--   )
--  pure ()

--palindrome_i arg1 = do
--  -- solution: a0[0,1,0,1] a0[0,1,0] a0[0,1] a0[0] a0[] a1[0,1,0,2] a1[0,1,0] a1[0,1] a1[0] a1[] a[0,0] a[0] a[] ~a0[0,0] ~a0[0,1,0,0] ~a0[0,1,0,2] ~a1[0,0] ~a1[0,1,0,0] ~a1[0,1,0,1] ~a[0,1,0,0] ~a[0,1,0,1] ~a[0,1,0,2] ~a[0,1,0] ~a[0,1] ~arg1[0,0] ~arg1[0,1] ~arg1[0] ~arg1[]
--  () <- (do
--    a <- pure arg1
--    () <- (do
--      () <- (do
--        a0 <- pure a
--        a1 <- pure a
--        () <- reverse_ii a0 a1
--        pure ()
--       )
--      pure ()
--     )
--    pure ()
--   )
--  pure ()

{- duplicate/2
duplicate arg1 arg2 :- ((arg1 = a, arg2 = b, ((append a0 a1 b, a0 = a, a1 = a)))).
constraints:
a0[0,2,0]
a0[0,2]
a0[0]
a0[]
a1[0,2,0]
a1[0,2]
a1[0]
a1[]
a[0]
a[]
b[0]
b[]
~a0[0,0]
~a0[0,1]
~a0[0,2,0,2]
~a1[0,0]
~a1[0,1]
~a1[0,2,0,1]
~a[0,1]
~a[0,2,0,0]
~arg1[0,1]
~arg1[0,2]
~arg2[0,0]
~arg2[0,2]
~b[0,0]
~b[0,2,0,1]
~b[0,2,0,2]
~(a0[0,2,0,0] & a0[0,2,0,1])
~(a0[0,2,0,1] & a[0,2,0,1])
~(a1[0,2,0,0] & a1[0,2,0,2])
~(a1[0,2,0,2] & a[0,2,0,2])
~(a[0,0] & a[0,2])
~(a[0,2,0,1] & a[0,2,0,2])
~(arg1[0,0] & a[0,0])
~(arg2[0,1] & b[0,1])
~(b[0,1] & b[0,2])
((a0[0,2,0,0] & (a1[0,2,0,0] & ~b[0,2,0,0])) | ((a0[0,2,0,0] & (~a1[0,2,0,0] & ~b[0,2,0,0])) | ((~a0[0,2,0,0] & (a1[0,2,0,0] & ~b[0,2,0,0])) | ((~a0[0,2,0,0] & (~a1[0,2,0,0] & b[0,2,0,0])) | (~a0[0,2,0,0] & (~a1[0,2,0,0] & ~b[0,2,0,0]))))))
(a0[0,2,0] <-> (a0[0,2,0,0] | a0[0,2,0,1]))
(a0[0,2] <-> a0[0,2,0])
(a0[0] <-> a0[0,2])
(a1[0,2,0] <-> (a1[0,2,0,0] | a1[0,2,0,2]))
(a1[0,2] <-> a1[0,2,0])
(a1[0] <-> a1[0,2])
(a[0,2,0] <-> (a[0,2,0,1] | a[0,2,0,2]))
(a[0,2] <-> a[0,2,0])
(a[0] <-> (a[0,0] | a[0,2]))
(arg1[0] <-> arg1[0,0])
(arg1[] <-> arg1[0])
(arg2[0] <-> arg2[0,1])
(arg2[] <-> arg2[0])
(b[0,2,0] <-> b[0,2,0,0])
(b[0,2] <-> b[0,2,0])
(b[0] <-> (b[0,1] | b[0,2]))
-}
-- mode ordering failure, cyclic dependency: [2] a1::in = a::out -> [1] a0::out = a::in -> [0] append a0::in a1::out b::in
-- mode ordering failure, cyclic dependency: [2] a1::in = a::out -> [1] a0::out = a::in -> [0] append a0::in a1::out b::in

-- mode ordering failure, cyclic dependency: [2] a1::out = a::in -> [0] append a0::out a1::in b::in -> [1] a0::in = a::out

-- mode ordering failure, cyclic dependency: [2] a1::out = a::in -> [0] append a0::out a1::in b::in -> [1] a0::in = a::out

duplicate_ii arg1 arg2 = do
  -- solution: a0[0,2,0,0] a0[0,2,0] a0[0,2] a0[0] a0[] a1[0,2,0,0] a1[0,2,0] a1[0,2] a1[0] a1[] a[0,0] a[0] a[] b[0,1] b[0] b[] ~a0[0,0] ~a0[0,1] ~a0[0,2,0,1] ~a0[0,2,0,2] ~a1[0,0] ~a1[0,1] ~a1[0,2,0,1] ~a1[0,2,0,2] ~a[0,1] ~a[0,2,0,0] ~a[0,2,0,1] ~a[0,2,0,2] ~a[0,2,0] ~a[0,2] ~arg1[0,0] ~arg1[0,1] ~arg1[0,2] ~arg1[0] ~arg1[] ~arg2[0,0] ~arg2[0,1] ~arg2[0,2] ~arg2[0] ~arg2[] ~b[0,0] ~b[0,2,0,0] ~b[0,2,0,1] ~b[0,2,0,2] ~b[0,2,0] ~b[0,2]
  () <- (do
    a <- pure arg1
    b <- pure arg2
    () <- (do
      () <- (do
        (a0,a1) <- append_ooi b
        guard $ a0 == a
        guard $ a1 == a
        pure ()
       )
      pure ()
     )
    pure ()
   )
  pure ()

--duplicate_ii arg1 arg2 = do
--  -- solution: a0[0,2,0,0] a0[0,2,0] a0[0,2] a0[0] a0[] a1[0,2,0,0] a1[0,2,0] a1[0,2] a1[0] a1[] a[0,2,0,1] a[0,2,0] a[0,2] a[0] a[] b[0,1] b[0] b[] ~a0[0,0] ~a0[0,1] ~a0[0,2,0,1] ~a0[0,2,0,2] ~a1[0,0] ~a1[0,1] ~a1[0,2,0,1] ~a1[0,2,0,2] ~a[0,0] ~a[0,1] ~a[0,2,0,0] ~a[0,2,0,2] ~arg1[0,0] ~arg1[0,1] ~arg1[0,2] ~arg1[0] ~arg1[] ~arg2[0,0] ~arg2[0,1] ~arg2[0,2] ~arg2[0] ~arg2[] ~b[0,0] ~b[0,2,0,0] ~b[0,2,0,1] ~b[0,2,0,2] ~b[0,2,0] ~b[0,2]
--  () <- (do
--    b <- pure arg2
--    (a) <- (do
--      (a) <- (do
--        (a0,a1) <- append_ooi b
--        a <- pure a0
--        guard $ a1 == a
--        pure (a)
--       )
--      pure (a)
--     )
--    guard $ arg1 == a
--    pure ()
--   )
--  pure ()

--duplicate_ii arg1 arg2 = do
--  -- solution: a0[0,2,0,0] a0[0,2,0] a0[0,2] a0[0] a0[] a1[0,2,0,0] a1[0,2,0] a1[0,2] a1[0] a1[] a[0,2,0,2] a[0,2,0] a[0,2] a[0] a[] b[0,1] b[0] b[] ~a0[0,0] ~a0[0,1] ~a0[0,2,0,1] ~a0[0,2,0,2] ~a1[0,0] ~a1[0,1] ~a1[0,2,0,1] ~a1[0,2,0,2] ~a[0,0] ~a[0,1] ~a[0,2,0,0] ~a[0,2,0,1] ~arg1[0,0] ~arg1[0,1] ~arg1[0,2] ~arg1[0] ~arg1[] ~arg2[0,0] ~arg2[0,1] ~arg2[0,2] ~arg2[0] ~arg2[] ~b[0,0] ~b[0,2,0,0] ~b[0,2,0,1] ~b[0,2,0,2] ~b[0,2,0] ~b[0,2]
--  () <- (do
--    b <- pure arg2
--    (a) <- (do
--      (a) <- (do
--        (a0,a1) <- append_ooi b
--        a <- pure a1
--        guard $ a0 == a
--        pure (a)
--       )
--      pure (a)
--     )
--    guard $ arg1 == a
--    pure ()
--   )
--  pure ()

--duplicate_ii arg1 arg2 = do
--  -- solution: a0[0,2,0,0] a0[0,2,0] a0[0,2] a0[0] a0[] a1[0,2,0,2] a1[0,2,0] a1[0,2] a1[0] a1[] a[0,0] a[0] a[] b[0,1] b[0] b[] ~a0[0,0] ~a0[0,1] ~a0[0,2,0,1] ~a0[0,2,0,2] ~a1[0,0] ~a1[0,1] ~a1[0,2,0,0] ~a1[0,2,0,1] ~a[0,1] ~a[0,2,0,0] ~a[0,2,0,1] ~a[0,2,0,2] ~a[0,2,0] ~a[0,2] ~arg1[0,0] ~arg1[0,1] ~arg1[0,2] ~arg1[0] ~arg1[] ~arg2[0,0] ~arg2[0,1] ~arg2[0,2] ~arg2[0] ~arg2[] ~b[0,0] ~b[0,2,0,0] ~b[0,2,0,1] ~b[0,2,0,2] ~b[0,2,0] ~b[0,2]
--  () <- (do
--    a <- pure arg1
--    b <- pure arg2
--    () <- (do
--      () <- (do
--        a1 <- pure a
--        (a0) <- append_oii a1 b
--        guard $ a0 == a
--        pure ()
--       )
--      pure ()
--     )
--    pure ()
--   )
--  pure ()

--duplicate_ii arg1 arg2 = do
--  -- solution: a0[0,2,0,1] a0[0,2,0] a0[0,2] a0[0] a0[] a1[0,2,0,0] a1[0,2,0] a1[0,2] a1[0] a1[] a[0,0] a[0] a[] b[0,1] b[0] b[] ~a0[0,0] ~a0[0,1] ~a0[0,2,0,0] ~a0[0,2,0,2] ~a1[0,0] ~a1[0,1] ~a1[0,2,0,1] ~a1[0,2,0,2] ~a[0,1] ~a[0,2,0,0] ~a[0,2,0,1] ~a[0,2,0,2] ~a[0,2,0] ~a[0,2] ~arg1[0,0] ~arg1[0,1] ~arg1[0,2] ~arg1[0] ~arg1[] ~arg2[0,0] ~arg2[0,1] ~arg2[0,2] ~arg2[0] ~arg2[] ~b[0,0] ~b[0,2,0,0] ~b[0,2,0,1] ~b[0,2,0,2] ~b[0,2,0] ~b[0,2]
--  () <- (do
--    a <- pure arg1
--    b <- pure arg2
--    () <- (do
--      () <- (do
--        a0 <- pure a
--        (a1) <- append_ioi a0 b
--        guard $ a1 == a
--        pure ()
--       )
--      pure ()
--     )
--    pure ()
--   )
--  pure ()

--duplicate_ii arg1 arg2 = do
--  -- solution: a0[0,2,0,1] a0[0,2,0] a0[0,2] a0[0] a0[] a1[0,2,0,2] a1[0,2,0] a1[0,2] a1[0] a1[] a[0,0] a[0] a[] b[0,1] b[0] b[] ~a0[0,0] ~a0[0,1] ~a0[0,2,0,0] ~a0[0,2,0,2] ~a1[0,0] ~a1[0,1] ~a1[0,2,0,0] ~a1[0,2,0,1] ~a[0,1] ~a[0,2,0,0] ~a[0,2,0,1] ~a[0,2,0,2] ~a[0,2,0] ~a[0,2] ~arg1[0,0] ~arg1[0,1] ~arg1[0,2] ~arg1[0] ~arg1[] ~arg2[0,0] ~arg2[0,1] ~arg2[0,2] ~arg2[0] ~arg2[] ~b[0,0] ~b[0,2,0,0] ~b[0,2,0,1] ~b[0,2,0,2] ~b[0,2,0] ~b[0,2]
--  () <- (do
--    a <- pure arg1
--    b <- pure arg2
--    () <- (do
--      () <- (do
--        a0 <- pure a
--        a1 <- pure a
--        () <- append_iii a0 a1 b
--        pure ()
--       )
--      pure ()
--     )
--    pure ()
--   )
--  pure ()

--duplicate_ii arg1 arg2 = do
--  -- solution: a0[0,2,0,1] a0[0,2,0] a0[0,2] a0[0] a0[] a1[0,2,0,2] a1[0,2,0] a1[0,2] a1[0] a1[] a[0,0] a[0] a[] b[0,2,0,0] b[0,2,0] b[0,2] b[0] b[] ~a0[0,0] ~a0[0,1] ~a0[0,2,0,0] ~a0[0,2,0,2] ~a1[0,0] ~a1[0,1] ~a1[0,2,0,0] ~a1[0,2,0,1] ~a[0,1] ~a[0,2,0,0] ~a[0,2,0,1] ~a[0,2,0,2] ~a[0,2,0] ~a[0,2] ~arg1[0,0] ~arg1[0,1] ~arg1[0,2] ~arg1[0] ~arg1[] ~arg2[0,0] ~arg2[0,1] ~arg2[0,2] ~arg2[0] ~arg2[] ~b[0,0] ~b[0,1] ~b[0,2,0,1] ~b[0,2,0,2]
--  () <- (do
--    a <- pure arg1
--    (b) <- (do
--      (b) <- (do
--        a0 <- pure a
--        a1 <- pure a
--        (b) <- append_iio a0 a1
--        pure (b)
--       )
--      pure (b)
--     )
--    guard $ arg2 == b
--    pure ()
--   )
--  pure ()

duplicate_io arg1 = do
  -- solution: a0[0,2,0,1] a0[0,2,0] a0[0,2] a0[0] a0[] a1[0,2,0,2] a1[0,2,0] a1[0,2] a1[0] a1[] a[0,0] a[0] a[] arg2[0,1] arg2[0] arg2[] b[0,2,0,0] b[0,2,0] b[0,2] b[0] b[] ~a0[0,0] ~a0[0,1] ~a0[0,2,0,0] ~a0[0,2,0,2] ~a1[0,0] ~a1[0,1] ~a1[0,2,0,0] ~a1[0,2,0,1] ~a[0,1] ~a[0,2,0,0] ~a[0,2,0,1] ~a[0,2,0,2] ~a[0,2,0] ~a[0,2] ~arg1[0,0] ~arg1[0,1] ~arg1[0,2] ~arg1[0] ~arg1[] ~arg2[0,0] ~arg2[0,2] ~b[0,0] ~b[0,1] ~b[0,2,0,1] ~b[0,2,0,2]
  (arg2) <- (do
    a <- pure arg1
    (b) <- (do
      (b) <- (do
        a0 <- pure a
        a1 <- pure a
        (b) <- append_iio a0 a1
        pure (b)
       )
      pure (b)
     )
    arg2 <- pure b
    pure (arg2)
   )
  pure (arg2)

duplicate_oi arg2 = do
  -- solution: a0[0,2,0,0] a0[0,2,0] a0[0,2] a0[0] a0[] a1[0,2,0,0] a1[0,2,0] a1[0,2] a1[0] a1[] a[0,2,0,1] a[0,2,0] a[0,2] a[0] a[] arg1[0,0] arg1[0] arg1[] b[0,1] b[0] b[] ~a0[0,0] ~a0[0,1] ~a0[0,2,0,1] ~a0[0,2,0,2] ~a1[0,0] ~a1[0,1] ~a1[0,2,0,1] ~a1[0,2,0,2] ~a[0,0] ~a[0,1] ~a[0,2,0,0] ~a[0,2,0,2] ~arg1[0,1] ~arg1[0,2] ~arg2[0,0] ~arg2[0,1] ~arg2[0,2] ~arg2[0] ~arg2[] ~b[0,0] ~b[0,2,0,0] ~b[0,2,0,1] ~b[0,2,0,2] ~b[0,2,0] ~b[0,2]
  (arg1) <- (do
    b <- pure arg2
    (a) <- (do
      (a) <- (do
        (a0,a1) <- append_ooi b
        a <- pure a0
        guard $ a1 == a
        pure (a)
       )
      pure (a)
     )
    arg1 <- pure a
    pure (arg1)
   )
  pure (arg1)

--duplicate_oi arg2 = do
--  -- solution: a0[0,2,0,0] a0[0,2,0] a0[0,2] a0[0] a0[] a1[0,2,0,0] a1[0,2,0] a1[0,2] a1[0] a1[] a[0,2,0,2] a[0,2,0] a[0,2] a[0] a[] arg1[0,0] arg1[0] arg1[] b[0,1] b[0] b[] ~a0[0,0] ~a0[0,1] ~a0[0,2,0,1] ~a0[0,2,0,2] ~a1[0,0] ~a1[0,1] ~a1[0,2,0,1] ~a1[0,2,0,2] ~a[0,0] ~a[0,1] ~a[0,2,0,0] ~a[0,2,0,1] ~arg1[0,1] ~arg1[0,2] ~arg2[0,0] ~arg2[0,1] ~arg2[0,2] ~arg2[0] ~arg2[] ~b[0,0] ~b[0,2,0,0] ~b[0,2,0,1] ~b[0,2,0,2] ~b[0,2,0] ~b[0,2]
--  (arg1) <- (do
--    b <- pure arg2
--    (a) <- (do
--      (a) <- (do
--        (a0,a1) <- append_ooi b
--        a <- pure a1
--        guard $ a0 == a
--        pure (a)
--       )
--      pure (a)
--     )
--    arg1 <- pure a
--    pure (arg1)
--   )
--  pure (arg1)

{- classify/2
classify arg1 arg2 :- ((arg1 = xs, arg2 = r, (if (xs = []) then (r = Nothing) else ((r = Just data0), (data0 = 42))))).
constraints:
data0[0,2,0,2]
data0[0,2,0]
data0[0,2]
data0[0]
data0[]
r[0]
r[]
xs[0]
xs[]
~arg1[0,1]
~arg1[0,2]
~arg2[0,0]
~arg2[0,2]
~data0[0,0]
~data0[0,1]
~data0[0,2,0,0]
~data0[0,2,0,1]
~r[0,0]
~r[0,2,0,0]
~r[0,2,0,2,1]
~xs[0,1]
~xs[0,2,0,0]
~xs[0,2,0,1]
~xs[0,2,0,2]
~(arg1[0,0] & xs[0,0])
~(arg2[0,1] & r[0,1])
~(data0[0,2,0,0] & data0[0,2,0,1])
~(data0[0,2,0,2,0] & data0[0,2,0,2,1])
~(r[0,1] & r[0,2])
~(r[0,2,0,0] & r[0,2,0,1])
~(r[0,2,0,2,0,0] & data0[0,2,0,2,0,0])
~(xs[0,0] & xs[0,2])
~(xs[0,2,0,0] & xs[0,2,0,1])
(arg1[0] <-> arg1[0,0])
(arg1[] <-> arg1[0])
(arg2[0] <-> arg2[0,1])
(arg2[] <-> arg2[0])
(data0[0,2,0,2,0] <-> data0[0,2,0,2,0,0])
(data0[0,2,0,2,1] <-> data0[0,2,0,2,1,0])
(data0[0,2,0,2] <-> (data0[0,2,0,2,0] | data0[0,2,0,2,1]))
(data0[0,2,0] <-> ((data0[0,2,0,0] | data0[0,2,0,1]) | data0[0,2,0,2]))
(data0[0,2] <-> data0[0,2,0])
(data0[0] <-> data0[0,2])
(r[0,2,0,1] <-> r[0,2,0,1,0])
(r[0,2,0,1] <-> r[0,2,0,2])
(r[0,2,0,2,0] <-> r[0,2,0,2,0,0])
(r[0,2,0,2] <-> r[0,2,0,2,0])
(r[0,2,0] <-> ((r[0,2,0,0] | r[0,2,0,1]) | r[0,2,0,2]))
(r[0,2] <-> r[0,2,0])
(r[0] <-> (r[0,1] | r[0,2]))
(xs[0,2,0,0] <-> xs[0,2,0,0,0])
(xs[0,2,0,1] <-> xs[0,2,0,2])
(xs[0,2,0] <-> ((xs[0,2,0,0] | xs[0,2,0,1]) | xs[0,2,0,2]))
(xs[0,2] <-> xs[0,2,0])
(xs[0] <-> (xs[0,0] | xs[0,2]))
-}
classify_ii arg1 arg2 = do
  -- solution: data0[0,2,0,2,0,0] data0[0,2,0,2,0] data0[0,2,0,2] data0[0,2,0] data0[0,2] data0[0] data0[] r[0,1] r[0] r[] xs[0,0] xs[0] xs[] ~arg1[0,0] ~arg1[0,1] ~arg1[0,2] ~arg1[0] ~arg1[] ~arg2[0,0] ~arg2[0,1] ~arg2[0,2] ~arg2[0] ~arg2[] ~data0[0,0] ~data0[0,1] ~data0[0,2,0,0] ~data0[0,2,0,1] ~data0[0,2,0,2,1,0] ~data0[0,2,0,2,1] ~r[0,0] ~r[0,2,0,0] ~r[0,2,0,1,0] ~r[0,2,0,1] ~r[0,2,0,2,0,0] ~r[0,2,0,2,0] ~r[0,2,0,2,1] ~r[0,2,0,2] ~r[0,2,0] ~r[0,2] ~xs[0,1] ~xs[0,2,0,0,0] ~xs[0,2,0,0] ~xs[0,2,0,1] ~xs[0,2,0,2] ~xs[0,2,0] ~xs[0,2]
  () <- (do
    xs <- pure arg1
    r <- pure arg2
    () <- (do
      () <- ifte ((do
        guard $ xs == []
        pure ()
       )) (\() -> (do
        guard $ r == Nothing
        pure ()
       )) ((do
        (data0) <- (do
          (Just data0) <- pure r
          pure (data0)
         )
        () <- (do
          guard $ data0 == 42
          pure ()
         )
        pure ()
       ))
      pure ()
     )
    pure ()
   )
  pure ()

--classify_ii arg1 arg2 = do
--  -- solution: data0[0,2,0,2,1,0] data0[0,2,0,2,1] data0[0,2,0,2] data0[0,2,0] data0[0,2] data0[0] data0[] r[0,1] r[0] r[] xs[0,0] xs[0] xs[] ~arg1[0,0] ~arg1[0,1] ~arg1[0,2] ~arg1[0] ~arg1[] ~arg2[0,0] ~arg2[0,1] ~arg2[0,2] ~arg2[0] ~arg2[] ~data0[0,0] ~data0[0,1] ~data0[0,2,0,0] ~data0[0,2,0,1] ~data0[0,2,0,2,0,0] ~data0[0,2,0,2,0] ~r[0,0] ~r[0,2,0,0] ~r[0,2,0,1,0] ~r[0,2,0,1] ~r[0,2,0,2,0,0] ~r[0,2,0,2,0] ~r[0,2,0,2,1] ~r[0,2,0,2] ~r[0,2,0] ~r[0,2] ~xs[0,1] ~xs[0,2,0,0,0] ~xs[0,2,0,0] ~xs[0,2,0,1] ~xs[0,2,0,2] ~xs[0,2,0] ~xs[0,2]
--  () <- (do
--    xs <- pure arg1
--    r <- pure arg2
--    () <- (do
--      () <- ifte ((do
--        guard $ xs == []
--        pure ()
--       )) (\() -> (do
--        guard $ r == Nothing
--        pure ()
--       )) ((do
--        (data0) <- (do
--          data0 <- pure 42
--          pure (data0)
--         )
--        () <- (do
--          guard $ r == (Just data0)
--          pure ()
--         )
--        pure ()
--       ))
--      pure ()
--     )
--    pure ()
--   )
--  pure ()

--classify_ii arg1 arg2 = do
--  -- solution: data0[0,2,0,2,1,0] data0[0,2,0,2,1] data0[0,2,0,2] data0[0,2,0] data0[0,2] data0[0] data0[] r[0,2,0,1,0] r[0,2,0,1] r[0,2,0,2,0,0] r[0,2,0,2,0] r[0,2,0,2] r[0,2,0] r[0,2] r[0] r[] xs[0,0] xs[0] xs[] ~arg1[0,0] ~arg1[0,1] ~arg1[0,2] ~arg1[0] ~arg1[] ~arg2[0,0] ~arg2[0,1] ~arg2[0,2] ~arg2[0] ~arg2[] ~data0[0,0] ~data0[0,1] ~data0[0,2,0,0] ~data0[0,2,0,1] ~data0[0,2,0,2,0,0] ~data0[0,2,0,2,0] ~r[0,0] ~r[0,1] ~r[0,2,0,0] ~r[0,2,0,2,1] ~xs[0,1] ~xs[0,2,0,0,0] ~xs[0,2,0,0] ~xs[0,2,0,1] ~xs[0,2,0,2] ~xs[0,2,0] ~xs[0,2]
--  () <- (do
--    xs <- pure arg1
--    (r) <- (do
--      (r) <- ifte ((do
--        guard $ xs == []
--        pure ()
--       )) (\() -> (do
--        r <- pure Nothing
--        pure (r)
--       )) ((do
--        (data0) <- (do
--          data0 <- pure 42
--          pure (data0)
--         )
--        (r) <- (do
--          r <- pure (Just data0)
--          pure (r)
--         )
--        pure (r)
--       ))
--      pure (r)
--     )
--    guard $ arg2 == r
--    pure ()
--   )
--  pure ()

classify_io arg1 = do
  -- solution: arg2[0,1] arg2[0] arg2[] data0[0,2,0,2,1,0] data0[0,2,0,2,1] data0[0,2,0,2] data0[0,2,0] data0[0,2] data0[0] data0[] r[0,2,0,1,0] r[0,2,0,1] r[0,2,0,2,0,0] r[0,2,0,2,0] r[0,2,0,2] r[0,2,0] r[0,2] r[0] r[] xs[0,0] xs[0] xs[] ~arg1[0,0] ~arg1[0,1] ~arg1[0,2] ~arg1[0] ~arg1[] ~arg2[0,0] ~arg2[0,2] ~data0[0,0] ~data0[0,1] ~data0[0,2,0,0] ~data0[0,2,0,1] ~data0[0,2,0,2,0,0] ~data0[0,2,0,2,0] ~r[0,0] ~r[0,1] ~r[0,2,0,0] ~r[0,2,0,2,1] ~xs[0,1] ~xs[0,2,0,0,0] ~xs[0,2,0,0] ~xs[0,2,0,1] ~xs[0,2,0,2] ~xs[0,2,0] ~xs[0,2]
  (arg2) <- (do
    xs <- pure arg1
    (r) <- (do
      (r) <- ifte ((do
        guard $ xs == []
        pure ()
       )) (\() -> (do
        r <- pure Nothing
        pure (r)
       )) ((do
        (data0) <- (do
          data0 <- pure 42
          pure (data0)
         )
        (r) <- (do
          r <- pure (Just data0)
          pure (r)
         )
        pure (r)
       ))
      pure (r)
     )
    arg2 <- pure r
    pure (arg2)
   )
  pure (arg2)
