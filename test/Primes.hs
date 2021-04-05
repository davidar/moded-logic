module Primes where
import Control.Applicative
import Control.Monad.Logic

succ_io a = pure (succ a)
mod_iio a b = pure (mod a b)

{- integers/3
integers arg1 arg2 arg3 :- ((arg1 = low, arg2 = high, arg3 = result, (if (((<=) low high)) then ((succ low m), (integers m high rest), (result = low : rest)) else ((result = []))))).
constraints:
~high[0,3,0,0,0]
~high[0,3,0,1,1]
~high[0,3,0]
~low[0,3,0,0,0]
~low[0,3,0]
~(arg1[0,0] & low[0,0])
~(arg2[0,1] & high[0,1])
~(arg3[0,2] & result[0,2])
~(high[0,1] & high[0,3])
~(low[0,0] & low[0,3])
~(low[0,3,0,1,0] & low[0,3,0,1,2])
~(m[0,3,0,1,0] & m[0,3,0,1,1])
~(rest[0,3,0,1,1] & rest[0,3,0,1,2])
~(result[0,2] & result[0,3])
~(result[0,3,0,1,2,0] & low[0,3,0,1,2,0])
~(low[0,3,0,1,0] | low[0,3,0,1,2])
(~low[0,3,0,0,0,0] & ~high[0,3,0,0,0,0])
(high[0,1] | high[0,3])
(low[0,0] | low[0,3])
(m[0,3,0,1,0] | m[0,3,0,1,1])
(rest[0,3,0,1,1] | rest[0,3,0,1,2])
(result[0,2] | result[0,3])
((low[0,3,0,1,0,0] & ~m[0,3,0,1,0,0]) | ((~low[0,3,0,1,0,0] & m[0,3,0,1,0,0]) | (~low[0,3,0,1,0,0] & ~m[0,3,0,1,0,0])))
(arg1[0] <-> arg1[0,0])
(arg1[] <-> arg1[0])
(arg2[0] <-> arg2[0,1])
(arg2[] <-> arg2[0])
(arg3[0] <-> arg3[0,2])
(arg3[] <-> arg3[0])
(high[0,3,0,0,0] <-> high[0,3,0,0,0,0])
(high[0,3,0,1,1,0] <-> arg2[])
(high[0,3,0,1,1] <-> high[0,3,0,1,1,0])
(high[0,3] <-> high[0,3,0])
(low[0,3,0,0,0] <-> low[0,3,0,0,0,0])
(low[0,3,0,1,0] <-> low[0,3,0,1,0,0])
(low[0,3,0,1,2,0] <-> rest[0,3,0,1,2,0])
(low[0,3,0,1,2] <-> low[0,3,0,1,2,0])
(low[0,3] <-> low[0,3,0])
(m[0,3,0,1,0] <-> m[0,3,0,1,0,0])
(m[0,3,0,1,1,0] <-> arg1[])
(m[0,3,0,1,1] <-> m[0,3,0,1,1,0])
(rest[0,3,0,1,1,0] <-> arg3[])
(rest[0,3,0,1,1] <-> rest[0,3,0,1,1,0])
(rest[0,3,0,1,2] <-> rest[0,3,0,1,2,0])
(result[0,3,0,1,2] <-> result[0,3,0,1,2,0])
(result[0,3,0,1] <-> result[0,3,0,1,2])
(result[0,3,0,1] <-> result[0,3,0,2])
(result[0,3,0,2,0] <-> result[0,3,0,2,0,0])
(result[0,3,0,2] <-> result[0,3,0,2,0])
(result[0,3,0] <-> (result[0,3,0,1] | result[0,3,0,2]))
(result[0,3] <-> result[0,3,0])
1
-}
integers_iio arg1 arg2 = do
  -- solution: arg3[0,2] arg3[0] arg3[] high[0,1] low[0,0] m[0,3,0,1,0,0] m[0,3,0,1,0] rest[0,3,0,1,1,0] rest[0,3,0,1,1] result[0,3,0,1,2,0] result[0,3,0,1,2] result[0,3,0,1] result[0,3,0,2,0,0] result[0,3,0,2,0] result[0,3,0,2] result[0,3,0] result[0,3] ~arg1[0,0] ~arg1[0] ~arg1[] ~arg2[0,1] ~arg2[0] ~arg2[] ~high[0,3,0,0,0,0] ~high[0,3,0,0,0] ~high[0,3,0,1,1,0] ~high[0,3,0,1,1] ~high[0,3,0] ~high[0,3] ~low[0,3,0,0,0,0] ~low[0,3,0,0,0] ~low[0,3,0,1,0,0] ~low[0,3,0,1,0] ~low[0,3,0,1,2,0] ~low[0,3,0,1,2] ~low[0,3,0] ~low[0,3] ~m[0,3,0,1,1,0] ~m[0,3,0,1,1] ~rest[0,3,0,1,2,0] ~rest[0,3,0,1,2] ~result[0,2]
  (arg3) <- (do
    low <- pure arg1
    high <- pure arg2
    (result) <- (do
      (result) <- ifte ((do
        () <- (do
          () <- if (<=) low high then pure () else empty
          pure ()
         )
        pure ()
       )) (\() -> (do
        (m) <- (do
          (m) <- succ_io low
          pure (m)
         )
        (rest) <- (do
          (rest) <- integers_iio m high
          pure (rest)
         )
        (result) <- (do
          result <- pure (low:rest)
          pure (result)
         )
        pure (result)
       )) ((do
        (result) <- (do
          result <- pure []
          pure (result)
         )
        pure (result)
       ))
      pure (result)
     )
    arg3 <- pure result
    pure (arg3)
   )
  pure (arg3)

{- remove/3
remove arg1 arg2 arg3 :- (((arg2 = []), (arg3 = []), ()); (arg1 = p, (arg2 = j0 : js, j0 = j), arg3 = result, ((mod j p m), (remove p js njs), if ((m = 0)) then (result = njs) else ((result = j1 : njs, j1 = j))))).
constraints:
~arg1[]
~j[1,3,2,2]
~m[1,3,2,0,0]
~m[1,3,2]
~(arg1[1,0] & p[1,0])
~(arg2[1,1,0] & j0[1,1,0])
~(arg3[1,2] & result[1,2])
~(j0[1,1,0] & j0[1,1,1])
~(j0[1,1,1] & j[1,1,1])
~(j1[1,3,2,2,0,0] & j1[1,3,2,2,0,1])
~(j1[1,3,2,2,0,1] & j[1,3,2,2,0,1])
~(j[1,1] & j[1,3])
~(j[1,3,0] & j[1,3,2])
~(js[1,1] & js[1,3])
~(m[1,3,0] & m[1,3,2])
~(njs[1,3,1] & njs[1,3,2])
~(p[1,0] & p[1,3])
~(p[1,3,0] & p[1,3,1])
~(result[1,2] & result[1,3])
~(result[1,3,2,1,0] & njs[1,3,2,1,0])
~(result[1,3,2,2,0,0] & j1[1,3,2,2,0,0])
(j0[1,1,0] | j0[1,1,1])
(j1[1,3,2,2,0,0] | j1[1,3,2,2,0,1])
(j[1,1] | j[1,3])
(js[1,1] | js[1,3])
(m[1,3,0] | m[1,3,2])
(njs[1,3,1] | njs[1,3,2])
(p[1,0] | p[1,3])
(result[1,2] | result[1,3])
((~j[1,3,0,0] & (~p[1,3,0,0] & m[1,3,0,0])) | (~j[1,3,0,0] & (~p[1,3,0,0] & ~m[1,3,0,0])))
(arg1[1] <-> arg1[1,0])
(arg1[] <-> arg1[1])
(arg2[0,0] <-> arg2[0,0,0])
(arg2[0] <-> arg2[0,0])
(arg2[1,1] <-> arg2[1,1,0])
(arg2[1] <-> arg2[1,1])
(arg2[] <-> arg2[0])
(arg2[] <-> arg2[1])
(arg3[0,1] <-> arg3[0,1,0])
(arg3[0] <-> arg3[0,1])
(arg3[1] <-> arg3[1,2])
(arg3[] <-> arg3[0])
(arg3[] <-> arg3[1])
(j0[1,1,0] <-> js[1,1,0])
(j1[1,3,2,2,0,0] <-> njs[1,3,2,2,0,0])
(j[1,1] <-> j[1,1,1])
(j[1,3,0] <-> j[1,3,0,0])
(j[1,3,2,2,0] <-> j[1,3,2,2,0,1])
(j[1,3,2,2] <-> j[1,3,2,2,0])
(j[1,3,2] <-> j[1,3,2,2])
(j[1,3] <-> (j[1,3,0] | j[1,3,2]))
(js[1,1] <-> js[1,1,0])
(js[1,3,1,0] <-> arg2[])
(js[1,3,1] <-> js[1,3,1,0])
(js[1,3] <-> js[1,3,1])
(m[1,3,0] <-> m[1,3,0,0])
(m[1,3,2,0,0] <-> m[1,3,2,0,0,0])
(njs[1,3,1,0] <-> arg3[])
(njs[1,3,1] <-> njs[1,3,1,0])
(njs[1,3,2,1] <-> njs[1,3,2,1,0])
(njs[1,3,2,1] <-> njs[1,3,2,2])
(njs[1,3,2,2,0] <-> njs[1,3,2,2,0,0])
(njs[1,3,2,2] <-> njs[1,3,2,2,0])
(njs[1,3,2] <-> (njs[1,3,2,1] | njs[1,3,2,2]))
(p[1,3,0] <-> p[1,3,0,0])
(p[1,3,1,0] <-> arg1[])
(p[1,3,1] <-> p[1,3,1,0])
(p[1,3] <-> (p[1,3,0] | p[1,3,1]))
(result[1,3,2,1] <-> result[1,3,2,1,0])
(result[1,3,2,1] <-> result[1,3,2,2])
(result[1,3,2,2,0] <-> result[1,3,2,2,0,0])
(result[1,3,2,2] <-> result[1,3,2,2,0])
(result[1,3,2] <-> (result[1,3,2,1] | result[1,3,2,2]))
(result[1,3] <-> result[1,3,2])
1
-}
remove_iii arg1 arg2 arg3 = do
  -- solution: j0[1,1,0] j1[1,3,2,2,0,0] j[1,1,1] j[1,1] js[1,1,0] js[1,1] m[1,3,0,0] m[1,3,0] njs[1,3,2,1,0] njs[1,3,2,1] njs[1,3,2,2,0,0] njs[1,3,2,2,0] njs[1,3,2,2] njs[1,3,2] p[1,0] result[1,2] ~arg1[1,0] ~arg1[1] ~arg1[] ~arg2[0,0,0] ~arg2[0,0] ~arg2[0] ~arg2[1,1,0] ~arg2[1,1] ~arg2[1] ~arg2[] ~arg3[0,1,0] ~arg3[0,1] ~arg3[0] ~arg3[1,2] ~arg3[1] ~arg3[] ~j0[1,1,1] ~j1[1,3,2,2,0,1] ~j[1,3,0,0] ~j[1,3,0] ~j[1,3,2,2,0,1] ~j[1,3,2,2,0] ~j[1,3,2,2] ~j[1,3,2] ~j[1,3] ~js[1,3,1,0] ~js[1,3,1] ~js[1,3] ~m[1,3,2,0,0,0] ~m[1,3,2,0,0] ~m[1,3,2] ~njs[1,3,1,0] ~njs[1,3,1] ~p[1,3,0,0] ~p[1,3,0] ~p[1,3,1,0] ~p[1,3,1] ~p[1,3] ~result[1,3,2,1,0] ~result[1,3,2,1] ~result[1,3,2,2,0,0] ~result[1,3,2,2,0] ~result[1,3,2,2] ~result[1,3,2] ~result[1,3]
  () <- (do
    () <- (do
      guard $ arg2 == []
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
    p <- pure arg1
    (j,js) <- (do
      (j0:js) <- pure arg2
      j <- pure j0
      pure (j,js)
     )
    result <- pure arg3
    () <- (do
      (m) <- (do
        (m) <- mod_iio j p
        pure (m)
       )
      (njs) <- ifte ((do
        () <- (do
          guard $ m == 0
          pure ()
         )
        pure ()
       )) (\() -> (do
        njs <- pure result
        pure (njs)
       )) ((do
        (njs) <- (do
          (j1:njs) <- pure result
          guard $ j1 == j
          pure (njs)
         )
        pure (njs)
       ))
      () <- (do
        () <- remove_iii p js njs
        pure ()
       )
      pure ()
     )
    pure ()
   )
  pure ()

remove_iio arg1 arg2 = do
  -- solution: arg3[0,1,0] arg3[0,1] arg3[0] arg3[1,2] arg3[1] arg3[] j0[1,1,0] j1[1,3,2,2,0,1] j[1,1,1] j[1,1] js[1,1,0] js[1,1] m[1,3,0,0] m[1,3,0] njs[1,3,1,0] njs[1,3,1] p[1,0] result[1,3,2,1,0] result[1,3,2,1] result[1,3,2,2,0,0] result[1,3,2,2,0] result[1,3,2,2] result[1,3,2] result[1,3] ~arg1[1,0] ~arg1[1] ~arg1[] ~arg2[0,0,0] ~arg2[0,0] ~arg2[0] ~arg2[1,1,0] ~arg2[1,1] ~arg2[1] ~arg2[] ~j0[1,1,1] ~j1[1,3,2,2,0,0] ~j[1,3,0,0] ~j[1,3,0] ~j[1,3,2,2,0,1] ~j[1,3,2,2,0] ~j[1,3,2,2] ~j[1,3,2] ~j[1,3] ~js[1,3,1,0] ~js[1,3,1] ~js[1,3] ~m[1,3,2,0,0,0] ~m[1,3,2,0,0] ~m[1,3,2] ~njs[1,3,2,1,0] ~njs[1,3,2,1] ~njs[1,3,2,2,0,0] ~njs[1,3,2,2,0] ~njs[1,3,2,2] ~njs[1,3,2] ~p[1,3,0,0] ~p[1,3,0] ~p[1,3,1,0] ~p[1,3,1] ~p[1,3] ~result[1,2]
  (arg3) <- (do
    () <- (do
      guard $ arg2 == []
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
    p <- pure arg1
    (j,js) <- (do
      (j0:js) <- pure arg2
      j <- pure j0
      pure (j,js)
     )
    (result) <- (do
      (m) <- (do
        (m) <- mod_iio j p
        pure (m)
       )
      (njs) <- (do
        (njs) <- remove_iio p js
        pure (njs)
       )
      (result) <- ifte ((do
        () <- (do
          guard $ m == 0
          pure ()
         )
        pure ()
       )) (\() -> (do
        result <- pure njs
        pure (result)
       )) ((do
        (result) <- (do
          j1 <- pure j
          result <- pure (j1:njs)
          pure (result)
         )
        pure (result)
       ))
      pure (result)
     )
    arg3 <- pure result
    pure (arg3)
   )
  pure (arg3)

{- sift/2
sift arg1 arg2 :- (((arg1 = []), (arg2 = []), ()); ((arg1 = p0 : js, p0 = p), (arg2 = p1 : ps, p1 = p), ((remove p js new), (sift new ps)))).
constraints:
~(arg1[1,0,0] & p0[1,0,0])
~(arg2[1,1,0] & p1[1,1,0])
~(js[1,0] & js[1,2])
~(new[1,2,0] & new[1,2,1])
~(p0[1,0,0] & p0[1,0,1])
~(p0[1,0,1] & p[1,0,1])
~(p1[1,1,0] & p1[1,1,1])
~(p1[1,1,1] & p[1,1,1])
~(p[1,0] & p[1,1])
~(p[1,0] & p[1,2])
~(p[1,1] & p[1,2])
~(ps[1,1] & ps[1,2])
(js[1,0] | js[1,2])
(new[1,2,0] | new[1,2,1])
(p0[1,0,0] | p0[1,0,1])
(p1[1,1,0] | p1[1,1,1])
(p[1,0] | (p[1,1] | p[1,2]))
(ps[1,1] | ps[1,2])
((~p[1,2,0,0] & (~js[1,2,0,0] & new[1,2,0,0])) | (~p[1,2,0,0] & (~js[1,2,0,0] & ~new[1,2,0,0])))
(arg1[0,0] <-> arg1[0,0,0])
(arg1[0] <-> arg1[0,0])
(arg1[1,0] <-> arg1[1,0,0])
(arg1[1] <-> arg1[1,0])
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg2[0,1] <-> arg2[0,1,0])
(arg2[0] <-> arg2[0,1])
(arg2[1,1] <-> arg2[1,1,0])
(arg2[1] <-> arg2[1,1])
(arg2[] <-> arg2[0])
(arg2[] <-> arg2[1])
(js[1,0] <-> js[1,0,0])
(js[1,2,0] <-> js[1,2,0,0])
(js[1,2] <-> js[1,2,0])
(new[1,2,0] <-> new[1,2,0,0])
(new[1,2,1,0] <-> arg1[])
(new[1,2,1] <-> new[1,2,1,0])
(p0[1,0,0] <-> js[1,0,0])
(p1[1,1,0] <-> ps[1,1,0])
(p[1,0] <-> p[1,0,1])
(p[1,1] <-> p[1,1,1])
(p[1,2,0] <-> p[1,2,0,0])
(p[1,2] <-> p[1,2,0])
(ps[1,1] <-> ps[1,1,0])
(ps[1,2,1,0] <-> arg2[])
(ps[1,2,1] <-> ps[1,2,1,0])
(ps[1,2] <-> ps[1,2,1])
1
-}
sift_ii arg1 arg2 = do
  -- solution: js[1,0,0] js[1,0] new[1,2,0,0] new[1,2,0] p0[1,0,0] p1[1,1,0] p[1,0,1] p[1,0] ps[1,1,0] ps[1,1] ~arg1[0,0,0] ~arg1[0,0] ~arg1[0] ~arg1[1,0,0] ~arg1[1,0] ~arg1[1] ~arg1[] ~arg2[0,1,0] ~arg2[0,1] ~arg2[0] ~arg2[1,1,0] ~arg2[1,1] ~arg2[1] ~arg2[] ~js[1,2,0,0] ~js[1,2,0] ~js[1,2] ~new[1,2,1,0] ~new[1,2,1] ~p0[1,0,1] ~p1[1,1,1] ~p[1,1,1] ~p[1,1] ~p[1,2,0,0] ~p[1,2,0] ~p[1,2] ~ps[1,2,1,0] ~ps[1,2,1] ~ps[1,2]
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
    (js,p) <- (do
      (p0:js) <- pure arg1
      p <- pure p0
      pure (js,p)
     )
    (ps) <- (do
      (p1:ps) <- pure arg2
      guard $ p1 == p
      pure (ps)
     )
    () <- (do
      (new) <- (do
        (new) <- remove_iio p js
        pure (new)
       )
      () <- (do
        () <- sift_ii new ps
        pure ()
       )
      pure ()
     )
    pure ()
   )
  pure ()

--sift_ii arg1 arg2 = do
--  -- solution: js[1,0,0] js[1,0] new[1,2,0,0] new[1,2,0] p0[1,0,0] p1[1,1,0] p[1,1,1] p[1,1] ps[1,1,0] ps[1,1] ~arg1[0,0,0] ~arg1[0,0] ~arg1[0] ~arg1[1,0,0] ~arg1[1,0] ~arg1[1] ~arg1[] ~arg2[0,1,0] ~arg2[0,1] ~arg2[0] ~arg2[1,1,0] ~arg2[1,1] ~arg2[1] ~arg2[] ~js[1,2,0,0] ~js[1,2,0] ~js[1,2] ~new[1,2,1,0] ~new[1,2,1] ~p0[1,0,1] ~p1[1,1,1] ~p[1,0,1] ~p[1,0] ~p[1,2,0,0] ~p[1,2,0] ~p[1,2] ~ps[1,2,1,0] ~ps[1,2,1] ~ps[1,2]
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
--    (p,ps) <- (do
--      (p1:ps) <- pure arg2
--      p <- pure p1
--      pure (p,ps)
--     )
--    (js) <- (do
--      (p0:js) <- pure arg1
--      guard $ p0 == p
--      pure (js)
--     )
--    () <- (do
--      (new) <- (do
--        (new) <- remove_iio p js
--        pure (new)
--       )
--      () <- (do
--        () <- sift_ii new ps
--        pure ()
--       )
--      pure ()
--     )
--    pure ()
--   )
--  pure ()

sift_io arg1 = do
  -- solution: arg2[0,1,0] arg2[0,1] arg2[0] arg2[1,1,0] arg2[1,1] arg2[1] arg2[] js[1,0,0] js[1,0] new[1,2,0,0] new[1,2,0] p0[1,0,0] p1[1,1,1] p[1,0,1] p[1,0] ps[1,2,1,0] ps[1,2,1] ps[1,2] ~arg1[0,0,0] ~arg1[0,0] ~arg1[0] ~arg1[1,0,0] ~arg1[1,0] ~arg1[1] ~arg1[] ~js[1,2,0,0] ~js[1,2,0] ~js[1,2] ~new[1,2,1,0] ~new[1,2,1] ~p0[1,0,1] ~p1[1,1,0] ~p[1,1,1] ~p[1,1] ~p[1,2,0,0] ~p[1,2,0] ~p[1,2] ~ps[1,1,0] ~ps[1,1]
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
    (js,p) <- (do
      (p0:js) <- pure arg1
      p <- pure p0
      pure (js,p)
     )
    (ps) <- (do
      (new) <- (do
        (new) <- remove_iio p js
        pure (new)
       )
      (ps) <- (do
        (ps) <- sift_io new
        pure (ps)
       )
      pure (ps)
     )
    (arg2) <- (do
      p1 <- pure p
      arg2 <- pure (p1:ps)
      pure (arg2)
     )
    pure (arg2)
   )
  pure (arg2)

{- primes/2
primes arg1 arg2 :- ((arg1 = limit, arg2 = ps, (((integers data0 limit js), (data0 = 2)), (sift js ps)))).
constraints:
~(arg1[0,0] & limit[0,0])
~(arg2[0,1] & ps[0,1])
~(data0[0,2,0,0] & data0[0,2,0,1])
~(js[0,2,0] & js[0,2,1])
~(limit[0,0] & limit[0,2])
~(ps[0,1] & ps[0,2])
(~data0[0,2,0,0,0] & (~limit[0,2,0,0,0] & js[0,2,0,0,0]))
(data0[0,2,0,0] | data0[0,2,0,1])
(js[0,2,0] | js[0,2,1])
(limit[0,0] | limit[0,2])
(ps[0,1] | ps[0,2])
((~js[0,2,1,0] & ps[0,2,1,0]) | (~js[0,2,1,0] & ~ps[0,2,1,0]))
(arg1[0] <-> arg1[0,0])
(arg1[] <-> arg1[0])
(arg2[0] <-> arg2[0,1])
(arg2[] <-> arg2[0])
(data0[0,2,0,0] <-> data0[0,2,0,0,0])
(data0[0,2,0,1] <-> data0[0,2,0,1,0])
(js[0,2,0,0] <-> js[0,2,0,0,0])
(js[0,2,0] <-> js[0,2,0,0])
(js[0,2,1] <-> js[0,2,1,0])
(limit[0,2,0,0] <-> limit[0,2,0,0,0])
(limit[0,2,0] <-> limit[0,2,0,0])
(limit[0,2] <-> limit[0,2,0])
(ps[0,2,1] <-> ps[0,2,1,0])
(ps[0,2] <-> ps[0,2,1])
1
-}
primes_ii arg1 arg2 = do
  -- solution: data0[0,2,0,1,0] data0[0,2,0,1] js[0,2,0,0,0] js[0,2,0,0] js[0,2,0] limit[0,0] ps[0,1] ~arg1[0,0] ~arg1[0] ~arg1[] ~arg2[0,1] ~arg2[0] ~arg2[] ~data0[0,2,0,0,0] ~data0[0,2,0,0] ~js[0,2,1,0] ~js[0,2,1] ~limit[0,2,0,0,0] ~limit[0,2,0,0] ~limit[0,2,0] ~limit[0,2] ~ps[0,2,1,0] ~ps[0,2,1] ~ps[0,2]
  () <- (do
    limit <- pure arg1
    ps <- pure arg2
    () <- (do
      (js) <- (do
        (data0) <- (do
          data0 <- pure 2
          pure (data0)
         )
        (js) <- (do
          (js) <- integers_iio data0 limit
          pure (js)
         )
        pure (js)
       )
      () <- (do
        () <- sift_ii js ps
        pure ()
       )
      pure ()
     )
    pure ()
   )
  pure ()

--primes_ii arg1 arg2 = do
--  -- solution: data0[0,2,0,1,0] data0[0,2,0,1] js[0,2,0,0,0] js[0,2,0,0] js[0,2,0] limit[0,0] ps[0,2,1,0] ps[0,2,1] ps[0,2] ~arg1[0,0] ~arg1[0] ~arg1[] ~arg2[0,1] ~arg2[0] ~arg2[] ~data0[0,2,0,0,0] ~data0[0,2,0,0] ~js[0,2,1,0] ~js[0,2,1] ~limit[0,2,0,0,0] ~limit[0,2,0,0] ~limit[0,2,0] ~limit[0,2] ~ps[0,1]
--  () <- (do
--    limit <- pure arg1
--    (ps) <- (do
--      (js) <- (do
--        (data0) <- (do
--          data0 <- pure 2
--          pure (data0)
--         )
--        (js) <- (do
--          (js) <- integers_iio data0 limit
--          pure (js)
--         )
--        pure (js)
--       )
--      (ps) <- (do
--        (ps) <- sift_io js
--        pure (ps)
--       )
--      pure (ps)
--     )
--    guard $ arg2 == ps
--    pure ()
--   )
--  pure ()

primes_io arg1 = do
  -- solution: arg2[0,1] arg2[0] arg2[] data0[0,2,0,1,0] data0[0,2,0,1] js[0,2,0,0,0] js[0,2,0,0] js[0,2,0] limit[0,0] ps[0,2,1,0] ps[0,2,1] ps[0,2] ~arg1[0,0] ~arg1[0] ~arg1[] ~data0[0,2,0,0,0] ~data0[0,2,0,0] ~js[0,2,1,0] ~js[0,2,1] ~limit[0,2,0,0,0] ~limit[0,2,0,0] ~limit[0,2,0] ~limit[0,2] ~ps[0,1]
  (arg2) <- (do
    limit <- pure arg1
    (ps) <- (do
      (js) <- (do
        (data0) <- (do
          data0 <- pure 2
          pure (data0)
         )
        (js) <- (do
          (js) <- integers_iio data0 limit
          pure (js)
         )
        pure (js)
       )
      (ps) <- (do
        (ps) <- sift_io js
        pure (ps)
       )
      pure (ps)
     )
    arg2 <- pure ps
    pure (arg2)
   )
  pure (arg2)
