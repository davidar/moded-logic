module Sort where
import Control.Applicative
import Control.Monad.Logic
import Control.Monad.Logic.Moded.Prelude

{- partition/4
partition arg1 arg2 arg3 arg4 :- (((arg1 = []), (arg3 = []), (arg4 = []), ()); ((arg1 = h0 : t, h0 = h), arg2 = p, arg3 = lo, arg4 = hi, (if (((<=) h p)) then ((partition t p lo1 hi), (lo = h1 : lo1, h1 = h)) else ((partition t p lo hi1), (hi = h2 : hi1, h2 = h))))).
constraints:
~arg2[]
~h[1,4,0,0,0]
~h[1,4,0,1,1]
~h[1,4,0,2]
~p[1,4,0,0,0]
~p[1,4,0,1,0]
~p[1,4,0,2]
~(arg1[1,0,0] & h0[1,0,0])
~(arg2[1,1] & p[1,1])
~(arg3[1,2] & lo[1,2])
~(arg4[1,3] & hi[1,3])
~(h0[1,0,0] & h0[1,0,1])
~(h0[1,0,1] & h[1,0,1])
~(h1[1,4,0,1,1,0] & h1[1,4,0,1,1,1])
~(h1[1,4,0,1,1,1] & h[1,4,0,1,1,1])
~(h2[1,4,0,2,1,0] & h2[1,4,0,2,1,1])
~(h2[1,4,0,2,1,1] & h[1,4,0,2,1,1])
~(h[1,0] & h[1,4])
~(hi1[1,4,0,2,0] & hi1[1,4,0,2,1])
~(hi[1,3] & hi[1,4])
~(hi[1,4,0,2,1,0] & h2[1,4,0,2,1,0])
~(lo1[1,4,0,1,0] & lo1[1,4,0,1,1])
~(lo[1,2] & lo[1,4])
~(lo[1,4,0,1,1,0] & h1[1,4,0,1,1,0])
~(p[1,1] & p[1,4])
~(t[1,0] & t[1,4])
(~h[1,4,0,0,0,0] & ~p[1,4,0,0,0,0])
(h0[1,0,0] | h0[1,0,1])
(h1[1,4,0,1,1,0] | h1[1,4,0,1,1,1])
(h2[1,4,0,2,1,0] | h2[1,4,0,2,1,1])
(h[1,0] | h[1,4])
(hi1[1,4,0,2,0] | hi1[1,4,0,2,1])
(hi[1,3] | hi[1,4])
(lo1[1,4,0,1,0] | lo1[1,4,0,1,1])
(lo[1,2] | lo[1,4])
(p[1,1] | p[1,4])
(t[1,0] | t[1,4])
(arg1[0,0] <-> arg1[0,0,0])
(arg1[0] <-> arg1[0,0])
(arg1[1,0] <-> arg1[1,0,0])
(arg1[1] <-> arg1[1,0])
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg2[1] <-> arg2[1,1])
(arg2[] <-> arg2[1])
(arg3[0,1] <-> arg3[0,1,0])
(arg3[0] <-> arg3[0,1])
(arg3[1] <-> arg3[1,2])
(arg3[] <-> arg3[0])
(arg3[] <-> arg3[1])
(arg4[0,2] <-> arg4[0,2,0])
(arg4[0] <-> arg4[0,2])
(arg4[1] <-> arg4[1,3])
(arg4[] <-> arg4[0])
(arg4[] <-> arg4[1])
(h0[1,0,0] <-> t[1,0,0])
(h1[1,4,0,1,1,0] <-> lo1[1,4,0,1,1,0])
(h2[1,4,0,2,1,0] <-> hi1[1,4,0,2,1,0])
(h[1,0] <-> h[1,0,1])
(h[1,4,0,0,0] <-> h[1,4,0,0,0,0])
(h[1,4,0,1,1] <-> h[1,4,0,1,1,1])
(h[1,4,0,2,1] <-> h[1,4,0,2,1,1])
(h[1,4,0,2] <-> h[1,4,0,2,1])
(h[1,4,0] <-> h[1,4,0,2])
(h[1,4] <-> h[1,4,0])
(hi1[1,4,0,2,0,0] <-> arg4[])
(hi1[1,4,0,2,0] <-> hi1[1,4,0,2,0,0])
(hi1[1,4,0,2,1] <-> hi1[1,4,0,2,1,0])
(hi[1,4,0,1,0,0] <-> arg4[])
(hi[1,4,0,1,0] <-> hi[1,4,0,1,0,0])
(hi[1,4,0,1] <-> hi[1,4,0,1,0])
(hi[1,4,0,1] <-> hi[1,4,0,2])
(hi[1,4,0,2,1] <-> hi[1,4,0,2,1,0])
(hi[1,4,0,2] <-> hi[1,4,0,2,1])
(hi[1,4,0] <-> (hi[1,4,0,1] | hi[1,4,0,2]))
(hi[1,4] <-> hi[1,4,0])
(lo1[1,4,0,1,0,0] <-> arg3[])
(lo1[1,4,0,1,0] <-> lo1[1,4,0,1,0,0])
(lo1[1,4,0,1,1] <-> lo1[1,4,0,1,1,0])
(lo[1,4,0,1,1] <-> lo[1,4,0,1,1,0])
(lo[1,4,0,1] <-> lo[1,4,0,1,1])
(lo[1,4,0,1] <-> lo[1,4,0,2])
(lo[1,4,0,2,0,0] <-> arg3[])
(lo[1,4,0,2,0] <-> lo[1,4,0,2,0,0])
(lo[1,4,0,2] <-> lo[1,4,0,2,0])
(lo[1,4,0] <-> (lo[1,4,0,1] | lo[1,4,0,2]))
(lo[1,4] <-> lo[1,4,0])
(p[1,4,0,0,0] <-> p[1,4,0,0,0,0])
(p[1,4,0,1,0,0] <-> arg2[])
(p[1,4,0,1,0] <-> p[1,4,0,1,0,0])
(p[1,4,0,2,0,0] <-> arg2[])
(p[1,4,0,2,0] <-> p[1,4,0,2,0,0])
(p[1,4,0,2] <-> p[1,4,0,2,0])
(p[1,4,0] <-> p[1,4,0,2])
(p[1,4] <-> p[1,4,0])
(t[1,0] <-> t[1,0,0])
(t[1,4,0,1,0,0] <-> arg1[])
(t[1,4,0,1,0] <-> t[1,4,0,1,0,0])
(t[1,4,0,1] <-> t[1,4,0,1,0])
(t[1,4,0,1] <-> t[1,4,0,2])
(t[1,4,0,2,0,0] <-> arg1[])
(t[1,4,0,2,0] <-> t[1,4,0,2,0,0])
(t[1,4,0,2] <-> t[1,4,0,2,0])
(t[1,4,0] <-> (t[1,4,0,1] | t[1,4,0,2]))
(t[1,4] <-> t[1,4,0])
1
-}
partition_iiii arg1 arg2 arg3 arg4 = do
  -- solution: h0[1,0,0] h1[1,4,0,1,1,0] h2[1,4,0,2,1,0] h[1,0,1] h[1,0] hi1[1,4,0,2,1,0] hi1[1,4,0,2,1] hi[1,3] lo1[1,4,0,1,1,0] lo1[1,4,0,1,1] lo[1,2] p[1,1] t[1,0,0] t[1,0] ~arg1[0,0,0] ~arg1[0,0] ~arg1[0] ~arg1[1,0,0] ~arg1[1,0] ~arg1[1] ~arg1[] ~arg2[1,1] ~arg2[1] ~arg2[] ~arg3[0,1,0] ~arg3[0,1] ~arg3[0] ~arg3[1,2] ~arg3[1] ~arg3[] ~arg4[0,2,0] ~arg4[0,2] ~arg4[0] ~arg4[1,3] ~arg4[1] ~arg4[] ~h0[1,0,1] ~h1[1,4,0,1,1,1] ~h2[1,4,0,2,1,1] ~h[1,4,0,0,0,0] ~h[1,4,0,0,0] ~h[1,4,0,1,1,1] ~h[1,4,0,1,1] ~h[1,4,0,2,1,1] ~h[1,4,0,2,1] ~h[1,4,0,2] ~h[1,4,0] ~h[1,4] ~hi1[1,4,0,2,0,0] ~hi1[1,4,0,2,0] ~hi[1,4,0,1,0,0] ~hi[1,4,0,1,0] ~hi[1,4,0,1] ~hi[1,4,0,2,1,0] ~hi[1,4,0,2,1] ~hi[1,4,0,2] ~hi[1,4,0] ~hi[1,4] ~lo1[1,4,0,1,0,0] ~lo1[1,4,0,1,0] ~lo[1,4,0,1,1,0] ~lo[1,4,0,1,1] ~lo[1,4,0,1] ~lo[1,4,0,2,0,0] ~lo[1,4,0,2,0] ~lo[1,4,0,2] ~lo[1,4,0] ~lo[1,4] ~p[1,4,0,0,0,0] ~p[1,4,0,0,0] ~p[1,4,0,1,0,0] ~p[1,4,0,1,0] ~p[1,4,0,2,0,0] ~p[1,4,0,2,0] ~p[1,4,0,2] ~p[1,4,0] ~p[1,4] ~t[1,4,0,1,0,0] ~t[1,4,0,1,0] ~t[1,4,0,1] ~t[1,4,0,2,0,0] ~t[1,4,0,2,0] ~t[1,4,0,2] ~t[1,4,0] ~t[1,4]
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
      guard $ arg4 == []
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
    p <- pure arg2
    lo <- pure arg3
    hi <- pure arg4
    () <- (do
      () <- ifte ((do
        () <- (do
          () <- if (<=) h p then pure () else empty
          pure ()
         )
        pure ()
       )) (\() -> (do
        (lo1) <- (do
          (h1:lo1) <- pure lo
          guard $ h1 == h
          pure (lo1)
         )
        () <- (do
          () <- partition_iiii t p lo1 hi
          pure ()
         )
        pure ()
       )) ((do
        (hi1) <- (do
          (h2:hi1) <- pure hi
          guard $ h2 == h
          pure (hi1)
         )
        () <- (do
          () <- partition_iiii t p lo hi1
          pure ()
         )
        pure ()
       ))
      pure ()
     )
    pure ()
   )
  pure ()

partition_iiio arg1 arg2 arg3 = do
  -- solution: arg4[0,2,0] arg4[0,2] arg4[0] arg4[1,3] arg4[1] arg4[] h0[1,0,0] h1[1,4,0,1,1,0] h2[1,4,0,2,1,1] h[1,0,1] h[1,0] hi1[1,4,0,2,0,0] hi1[1,4,0,2,0] hi[1,4,0,1,0,0] hi[1,4,0,1,0] hi[1,4,0,1] hi[1,4,0,2,1,0] hi[1,4,0,2,1] hi[1,4,0,2] hi[1,4,0] hi[1,4] lo1[1,4,0,1,1,0] lo1[1,4,0,1,1] lo[1,2] p[1,1] t[1,0,0] t[1,0] ~arg1[0,0,0] ~arg1[0,0] ~arg1[0] ~arg1[1,0,0] ~arg1[1,0] ~arg1[1] ~arg1[] ~arg2[1,1] ~arg2[1] ~arg2[] ~arg3[0,1,0] ~arg3[0,1] ~arg3[0] ~arg3[1,2] ~arg3[1] ~arg3[] ~h0[1,0,1] ~h1[1,4,0,1,1,1] ~h2[1,4,0,2,1,0] ~h[1,4,0,0,0,0] ~h[1,4,0,0,0] ~h[1,4,0,1,1,1] ~h[1,4,0,1,1] ~h[1,4,0,2,1,1] ~h[1,4,0,2,1] ~h[1,4,0,2] ~h[1,4,0] ~h[1,4] ~hi1[1,4,0,2,1,0] ~hi1[1,4,0,2,1] ~hi[1,3] ~lo1[1,4,0,1,0,0] ~lo1[1,4,0,1,0] ~lo[1,4,0,1,1,0] ~lo[1,4,0,1,1] ~lo[1,4,0,1] ~lo[1,4,0,2,0,0] ~lo[1,4,0,2,0] ~lo[1,4,0,2] ~lo[1,4,0] ~lo[1,4] ~p[1,4,0,0,0,0] ~p[1,4,0,0,0] ~p[1,4,0,1,0,0] ~p[1,4,0,1,0] ~p[1,4,0,2,0,0] ~p[1,4,0,2,0] ~p[1,4,0,2] ~p[1,4,0] ~p[1,4] ~t[1,4,0,1,0,0] ~t[1,4,0,1,0] ~t[1,4,0,1] ~t[1,4,0,2,0,0] ~t[1,4,0,2,0] ~t[1,4,0,2] ~t[1,4,0] ~t[1,4]
  (arg4) <- (do
    () <- (do
      guard $ arg1 == []
      pure ()
     )
    () <- (do
      guard $ arg3 == []
      pure ()
     )
    (arg4) <- (do
      arg4 <- pure []
      pure (arg4)
     )
    () <- (do
      
      pure ()
     )
    pure (arg4)
   ) <|> (do
    (h,t) <- (do
      (h0:t) <- pure arg1
      h <- pure h0
      pure (h,t)
     )
    p <- pure arg2
    lo <- pure arg3
    (hi) <- (do
      (hi) <- ifte ((do
        () <- (do
          () <- if (<=) h p then pure () else empty
          pure ()
         )
        pure ()
       )) (\() -> (do
        (lo1) <- (do
          (h1:lo1) <- pure lo
          guard $ h1 == h
          pure (lo1)
         )
        (hi) <- (do
          (hi) <- partition_iiio t p lo1
          pure (hi)
         )
        pure (hi)
       )) ((do
        (hi1) <- (do
          (hi1) <- partition_iiio t p lo
          pure (hi1)
         )
        (hi) <- (do
          h2 <- pure h
          hi <- pure (h2:hi1)
          pure (hi)
         )
        pure (hi)
       ))
      pure (hi)
     )
    arg4 <- pure hi
    pure (arg4)
   )
  pure (arg4)

partition_iioi arg1 arg2 arg4 = do
  -- solution: arg3[0,1,0] arg3[0,1] arg3[0] arg3[1,2] arg3[1] arg3[] h0[1,0,0] h1[1,4,0,1,1,1] h2[1,4,0,2,1,0] h[1,0,1] h[1,0] hi1[1,4,0,2,1,0] hi1[1,4,0,2,1] hi[1,3] lo1[1,4,0,1,0,0] lo1[1,4,0,1,0] lo[1,4,0,1,1,0] lo[1,4,0,1,1] lo[1,4,0,1] lo[1,4,0,2,0,0] lo[1,4,0,2,0] lo[1,4,0,2] lo[1,4,0] lo[1,4] p[1,1] t[1,0,0] t[1,0] ~arg1[0,0,0] ~arg1[0,0] ~arg1[0] ~arg1[1,0,0] ~arg1[1,0] ~arg1[1] ~arg1[] ~arg2[1,1] ~arg2[1] ~arg2[] ~arg4[0,2,0] ~arg4[0,2] ~arg4[0] ~arg4[1,3] ~arg4[1] ~arg4[] ~h0[1,0,1] ~h1[1,4,0,1,1,0] ~h2[1,4,0,2,1,1] ~h[1,4,0,0,0,0] ~h[1,4,0,0,0] ~h[1,4,0,1,1,1] ~h[1,4,0,1,1] ~h[1,4,0,2,1,1] ~h[1,4,0,2,1] ~h[1,4,0,2] ~h[1,4,0] ~h[1,4] ~hi1[1,4,0,2,0,0] ~hi1[1,4,0,2,0] ~hi[1,4,0,1,0,0] ~hi[1,4,0,1,0] ~hi[1,4,0,1] ~hi[1,4,0,2,1,0] ~hi[1,4,0,2,1] ~hi[1,4,0,2] ~hi[1,4,0] ~hi[1,4] ~lo1[1,4,0,1,1,0] ~lo1[1,4,0,1,1] ~lo[1,2] ~p[1,4,0,0,0,0] ~p[1,4,0,0,0] ~p[1,4,0,1,0,0] ~p[1,4,0,1,0] ~p[1,4,0,2,0,0] ~p[1,4,0,2,0] ~p[1,4,0,2] ~p[1,4,0] ~p[1,4] ~t[1,4,0,1,0,0] ~t[1,4,0,1,0] ~t[1,4,0,1] ~t[1,4,0,2,0,0] ~t[1,4,0,2,0] ~t[1,4,0,2] ~t[1,4,0] ~t[1,4]
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
      guard $ arg4 == []
      pure ()
     )
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
    p <- pure arg2
    hi <- pure arg4
    (lo) <- (do
      (lo) <- ifte ((do
        () <- (do
          () <- if (<=) h p then pure () else empty
          pure ()
         )
        pure ()
       )) (\() -> (do
        (lo1) <- (do
          (lo1) <- partition_iioi t p hi
          pure (lo1)
         )
        (lo) <- (do
          h1 <- pure h
          lo <- pure (h1:lo1)
          pure (lo)
         )
        pure (lo)
       )) ((do
        (hi1) <- (do
          (h2:hi1) <- pure hi
          guard $ h2 == h
          pure (hi1)
         )
        (lo) <- (do
          (lo) <- partition_iioi t p hi1
          pure (lo)
         )
        pure (lo)
       ))
      pure (lo)
     )
    arg3 <- pure lo
    pure (arg3)
   )
  pure (arg3)

partition_iioo arg1 arg2 = do
  -- solution: arg3[0,1,0] arg3[0,1] arg3[0] arg3[1,2] arg3[1] arg3[] arg4[0,2,0] arg4[0,2] arg4[0] arg4[1,3] arg4[1] arg4[] h0[1,0,0] h1[1,4,0,1,1,1] h2[1,4,0,2,1,1] h[1,0,1] h[1,0] hi1[1,4,0,2,0,0] hi1[1,4,0,2,0] hi[1,4,0,1,0,0] hi[1,4,0,1,0] hi[1,4,0,1] hi[1,4,0,2,1,0] hi[1,4,0,2,1] hi[1,4,0,2] hi[1,4,0] hi[1,4] lo1[1,4,0,1,0,0] lo1[1,4,0,1,0] lo[1,4,0,1,1,0] lo[1,4,0,1,1] lo[1,4,0,1] lo[1,4,0,2,0,0] lo[1,4,0,2,0] lo[1,4,0,2] lo[1,4,0] lo[1,4] p[1,1] t[1,0,0] t[1,0] ~arg1[0,0,0] ~arg1[0,0] ~arg1[0] ~arg1[1,0,0] ~arg1[1,0] ~arg1[1] ~arg1[] ~arg2[1,1] ~arg2[1] ~arg2[] ~h0[1,0,1] ~h1[1,4,0,1,1,0] ~h2[1,4,0,2,1,0] ~h[1,4,0,0,0,0] ~h[1,4,0,0,0] ~h[1,4,0,1,1,1] ~h[1,4,0,1,1] ~h[1,4,0,2,1,1] ~h[1,4,0,2,1] ~h[1,4,0,2] ~h[1,4,0] ~h[1,4] ~hi1[1,4,0,2,1,0] ~hi1[1,4,0,2,1] ~hi[1,3] ~lo1[1,4,0,1,1,0] ~lo1[1,4,0,1,1] ~lo[1,2] ~p[1,4,0,0,0,0] ~p[1,4,0,0,0] ~p[1,4,0,1,0,0] ~p[1,4,0,1,0] ~p[1,4,0,2,0,0] ~p[1,4,0,2,0] ~p[1,4,0,2] ~p[1,4,0] ~p[1,4] ~t[1,4,0,1,0,0] ~t[1,4,0,1,0] ~t[1,4,0,1] ~t[1,4,0,2,0,0] ~t[1,4,0,2,0] ~t[1,4,0,2] ~t[1,4,0] ~t[1,4]
  (arg3,arg4) <- (do
    () <- (do
      guard $ arg1 == []
      pure ()
     )
    (arg3) <- (do
      arg3 <- pure []
      pure (arg3)
     )
    (arg4) <- (do
      arg4 <- pure []
      pure (arg4)
     )
    () <- (do
      
      pure ()
     )
    pure (arg3,arg4)
   ) <|> (do
    (h,t) <- (do
      (h0:t) <- pure arg1
      h <- pure h0
      pure (h,t)
     )
    p <- pure arg2
    (hi,lo) <- (do
      (hi,lo) <- ifte ((do
        () <- (do
          () <- if (<=) h p then pure () else empty
          pure ()
         )
        pure ()
       )) (\() -> (do
        (hi,lo1) <- (do
          (lo1,hi) <- partition_iioo t p
          pure (hi,lo1)
         )
        (lo) <- (do
          h1 <- pure h
          lo <- pure (h1:lo1)
          pure (lo)
         )
        pure (hi,lo)
       )) ((do
        (hi1,lo) <- (do
          (lo,hi1) <- partition_iioo t p
          pure (hi1,lo)
         )
        (hi) <- (do
          h2 <- pure h
          hi <- pure (h2:hi1)
          pure (hi)
         )
        pure (hi,lo)
       ))
      pure (hi,lo)
     )
    arg3 <- pure lo
    arg4 <- pure hi
    pure (arg3,arg4)
   )
  pure (arg3,arg4)

{- qsort/3
qsort arg1 arg2 arg3 :- (((arg1 = []), arg2 = r, arg3 = r, ()); ((arg1 = x0 : xs, x0 = x), arg2 = r, arg3 = r0, ((partition xs x ys zs), (qsort zs r1 r0), ((qsort ys r data0), (data0 = x1 : r1, x1 = x))))).
constraints:
~(arg1[1,0,0] & x0[1,0,0])
~(arg2[0,1] & r[0,1])
~(arg2[1,1] & r[1,1])
~(arg3[0,2] & r[0,2])
~(arg3[1,2] & r0[1,2])
~(data0[1,3,2,0] & data0[1,3,2,1])
~(data0[1,3,2,1,0] & x1[1,3,2,1,0])
~(r0[1,2] & r0[1,3])
~(r1[1,3,1] & r1[1,3,2])
~(r[0,1] & r[0,2])
~(r[1,1] & r[1,3])
~(x0[1,0,0] & x0[1,0,1])
~(x0[1,0,1] & x[1,0,1])
~(x1[1,3,2,1,0] & x1[1,3,2,1,1])
~(x1[1,3,2,1,1] & x[1,3,2,1,1])
~(x[1,0] & x[1,3])
~(x[1,3,0] & x[1,3,2])
~(xs[1,0] & xs[1,3])
~(ys[1,3,0] & ys[1,3,2])
~(zs[1,3,0] & zs[1,3,1])
(data0[1,3,2,0] | data0[1,3,2,1])
(r0[1,2] | r0[1,3])
(r1[1,3,1] | r1[1,3,2])
(r[0,1] | r[0,2])
(r[1,1] | r[1,3])
(x0[1,0,0] | x0[1,0,1])
(x1[1,3,2,1,0] | x1[1,3,2,1,1])
(x[1,0] | x[1,3])
(xs[1,0] | xs[1,3])
(ys[1,3,0] | ys[1,3,2])
(zs[1,3,0] | zs[1,3,1])
((~xs[1,3,0,0] & (~x[1,3,0,0] & (ys[1,3,0,0] & zs[1,3,0,0]))) | ((~xs[1,3,0,0] & (~x[1,3,0,0] & (ys[1,3,0,0] & ~zs[1,3,0,0]))) | ((~xs[1,3,0,0] & (~x[1,3,0,0] & (~ys[1,3,0,0] & zs[1,3,0,0]))) | (~xs[1,3,0,0] & (~x[1,3,0,0] & (~ys[1,3,0,0] & ~zs[1,3,0,0]))))))
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
(arg3[1] <-> arg3[1,2])
(arg3[] <-> arg3[0])
(arg3[] <-> arg3[1])
(data0[1,3,2,0,0] <-> arg3[])
(data0[1,3,2,0] <-> data0[1,3,2,0,0])
(data0[1,3,2,1] <-> data0[1,3,2,1,0])
(r0[1,3,1,0] <-> arg3[])
(r0[1,3,1] <-> r0[1,3,1,0])
(r0[1,3] <-> r0[1,3,1])
(r1[1,3,1,0] <-> arg2[])
(r1[1,3,1] <-> r1[1,3,1,0])
(r1[1,3,2,1] <-> r1[1,3,2,1,0])
(r1[1,3,2] <-> r1[1,3,2,1])
(r[1,3,2,0,0] <-> arg2[])
(r[1,3,2,0] <-> r[1,3,2,0,0])
(r[1,3,2] <-> r[1,3,2,0])
(r[1,3] <-> r[1,3,2])
(x0[1,0,0] <-> xs[1,0,0])
(x1[1,3,2,1,0] <-> r1[1,3,2,1,0])
(x[1,0] <-> x[1,0,1])
(x[1,3,0] <-> x[1,3,0,0])
(x[1,3,2,1] <-> x[1,3,2,1,1])
(x[1,3,2] <-> x[1,3,2,1])
(x[1,3] <-> (x[1,3,0] | x[1,3,2]))
(xs[1,0] <-> xs[1,0,0])
(xs[1,3,0] <-> xs[1,3,0,0])
(xs[1,3] <-> xs[1,3,0])
(ys[1,3,0] <-> ys[1,3,0,0])
(ys[1,3,2,0,0] <-> arg1[])
(ys[1,3,2,0] <-> ys[1,3,2,0,0])
(ys[1,3,2] <-> ys[1,3,2,0])
(zs[1,3,0] <-> zs[1,3,0,0])
(zs[1,3,1,0] <-> arg1[])
(zs[1,3,1] <-> zs[1,3,1,0])
1
-}
-- mode ordering failure, cyclic dependency: [2] ((qsort ys::in r::in data0::out), (data0::in = x1::out : r1::out, x1::in = x::out)) -> [0] (partition xs::in x::in ys::out zs::out)
qsort_iio arg1 arg2 = do
  -- solution: arg3[0,2] arg3[0] arg3[1,2] arg3[1] arg3[] data0[1,3,2,0,0] data0[1,3,2,0] r0[1,3,1,0] r0[1,3,1] r0[1,3] r1[1,3,2,1,0] r1[1,3,2,1] r1[1,3,2] r[0,1] r[1,1] x0[1,0,0] x1[1,3,2,1,0] x[1,0,1] x[1,0] xs[1,0,0] xs[1,0] ys[1,3,0,0] ys[1,3,0] zs[1,3,0,0] zs[1,3,0] ~arg1[0,0,0] ~arg1[0,0] ~arg1[0] ~arg1[1,0,0] ~arg1[1,0] ~arg1[1] ~arg1[] ~arg2[0,1] ~arg2[0] ~arg2[1,1] ~arg2[1] ~arg2[] ~data0[1,3,2,1,0] ~data0[1,3,2,1] ~r0[1,2] ~r1[1,3,1,0] ~r1[1,3,1] ~r[0,2] ~r[1,3,2,0,0] ~r[1,3,2,0] ~r[1,3,2] ~r[1,3] ~x0[1,0,1] ~x1[1,3,2,1,1] ~x[1,3,0,0] ~x[1,3,0] ~x[1,3,2,1,1] ~x[1,3,2,1] ~x[1,3,2] ~x[1,3] ~xs[1,3,0,0] ~xs[1,3,0] ~xs[1,3] ~ys[1,3,2,0,0] ~ys[1,3,2,0] ~ys[1,3,2] ~zs[1,3,1,0] ~zs[1,3,1]
  (arg3) <- (do
    () <- (do
      guard $ arg1 == []
      pure ()
     )
    r <- pure arg2
    arg3 <- pure r
    () <- (do
      
      pure ()
     )
    pure (arg3)
   ) <|> (do
    (x,xs) <- (do
      (x0:xs) <- pure arg1
      x <- pure x0
      pure (x,xs)
     )
    r <- pure arg2
    (r0) <- (do
      (ys,zs) <- (do
        (ys,zs) <- partition_iioo xs x
        pure (ys,zs)
       )
      (r1) <- (do
        (data0) <- (do
          (data0) <- qsort_iio ys r
          pure (data0)
         )
        (r1) <- (do
          (x1:r1) <- pure data0
          guard $ x1 == x
          pure (r1)
         )
        pure (r1)
       )
      (r0) <- (do
        (r0) <- qsort_iio zs r1
        pure (r0)
       )
      pure (r0)
     )
    arg3 <- pure r0
    pure (arg3)
   )
  pure (arg3)

qsort_ioi arg1 arg3 = do
  -- solution: arg2[0,1] arg2[0] arg2[1,1] arg2[1] arg2[] data0[1,3,2,1,0] data0[1,3,2,1] r0[1,2] r1[1,3,1,0] r1[1,3,1] r[0,2] r[1,3,2,0,0] r[1,3,2,0] r[1,3,2] r[1,3] x0[1,0,0] x1[1,3,2,1,1] x[1,0,1] x[1,0] xs[1,0,0] xs[1,0] ys[1,3,0,0] ys[1,3,0] zs[1,3,0,0] zs[1,3,0] ~arg1[0,0,0] ~arg1[0,0] ~arg1[0] ~arg1[1,0,0] ~arg1[1,0] ~arg1[1] ~arg1[] ~arg3[0,2] ~arg3[0] ~arg3[1,2] ~arg3[1] ~arg3[] ~data0[1,3,2,0,0] ~data0[1,3,2,0] ~r0[1,3,1,0] ~r0[1,3,1] ~r0[1,3] ~r1[1,3,2,1,0] ~r1[1,3,2,1] ~r1[1,3,2] ~r[0,1] ~r[1,1] ~x0[1,0,1] ~x1[1,3,2,1,0] ~x[1,3,0,0] ~x[1,3,0] ~x[1,3,2,1,1] ~x[1,3,2,1] ~x[1,3,2] ~x[1,3] ~xs[1,3,0,0] ~xs[1,3,0] ~xs[1,3] ~ys[1,3,2,0,0] ~ys[1,3,2,0] ~ys[1,3,2] ~zs[1,3,1,0] ~zs[1,3,1]
  (arg2) <- (do
    () <- (do
      guard $ arg1 == []
      pure ()
     )
    r <- pure arg3
    arg2 <- pure r
    () <- (do
      
      pure ()
     )
    pure (arg2)
   ) <|> (do
    (x,xs) <- (do
      (x0:xs) <- pure arg1
      x <- pure x0
      pure (x,xs)
     )
    r0 <- pure arg3
    (r) <- (do
      (ys,zs) <- (do
        (ys,zs) <- partition_iioo xs x
        pure (ys,zs)
       )
      (r1) <- (do
        (r1) <- qsort_ioi zs r0
        pure (r1)
       )
      (r) <- (do
        (data0) <- (do
          x1 <- pure x
          data0 <- pure (x1:r1)
          pure (data0)
         )
        (r) <- (do
          (r) <- qsort_ioi ys data0
          pure (r)
         )
        pure (r)
       )
      pure (r)
     )
    arg2 <- pure r
    pure (arg2)
   )
  pure (arg2)

{- sort/2
sort arg1 arg2 :- ((arg1 = list, arg2 = sorted, (((qsort list sorted data0), (data0 = []))))).
constraints:
~(arg1[0,0] & list[0,0])
~(arg2[0,1] & sorted[0,1])
~(data0[0,2,0,0] & data0[0,2,0,1])
~(list[0,0] & list[0,2])
~(sorted[0,1] & sorted[0,2])
(data0[0,2,0,0] | data0[0,2,0,1])
(list[0,0] | list[0,2])
(sorted[0,1] | sorted[0,2])
((~list[0,2,0,0,0] & (sorted[0,2,0,0,0] & ~data0[0,2,0,0,0])) | (~list[0,2,0,0,0] & (~sorted[0,2,0,0,0] & data0[0,2,0,0,0])))
(arg1[0] <-> arg1[0,0])
(arg1[] <-> arg1[0])
(arg2[0] <-> arg2[0,1])
(arg2[] <-> arg2[0])
(data0[0,2,0,0] <-> data0[0,2,0,0,0])
(data0[0,2,0,1] <-> data0[0,2,0,1,0])
(list[0,2,0,0] <-> list[0,2,0,0,0])
(list[0,2,0] <-> list[0,2,0,0])
(list[0,2] <-> list[0,2,0])
(sorted[0,2,0,0] <-> sorted[0,2,0,0,0])
(sorted[0,2,0] <-> sorted[0,2,0,0])
(sorted[0,2] <-> sorted[0,2,0])
1
-}
sort_ii arg1 arg2 = do
  -- solution: data0[0,2,0,0,0] data0[0,2,0,0] list[0,0] sorted[0,1] ~arg1[0,0] ~arg1[0] ~arg1[] ~arg2[0,1] ~arg2[0] ~arg2[] ~data0[0,2,0,1,0] ~data0[0,2,0,1] ~list[0,2,0,0,0] ~list[0,2,0,0] ~list[0,2,0] ~list[0,2] ~sorted[0,2,0,0,0] ~sorted[0,2,0,0] ~sorted[0,2,0] ~sorted[0,2]
  () <- (do
    list <- pure arg1
    sorted <- pure arg2
    () <- (do
      () <- (do
        (data0) <- (do
          (data0) <- qsort_iio list sorted
          pure (data0)
         )
        () <- (do
          guard $ data0 == []
          pure ()
         )
        pure ()
       )
      pure ()
     )
    pure ()
   )
  pure ()

--sort_ii arg1 arg2 = do
--  -- solution: data0[0,2,0,1,0] data0[0,2,0,1] list[0,0] sorted[0,2,0,0,0] sorted[0,2,0,0] sorted[0,2,0] sorted[0,2] ~arg1[0,0] ~arg1[0] ~arg1[] ~arg2[0,1] ~arg2[0] ~arg2[] ~data0[0,2,0,0,0] ~data0[0,2,0,0] ~list[0,2,0,0,0] ~list[0,2,0,0] ~list[0,2,0] ~list[0,2] ~sorted[0,1]
--  () <- (do
--    list <- pure arg1
--    (sorted) <- (do
--      (sorted) <- (do
--        (data0) <- (do
--          data0 <- pure []
--          pure (data0)
--         )
--        (sorted) <- (do
--          (sorted) <- qsort_ioi list data0
--          pure (sorted)
--         )
--        pure (sorted)
--       )
--      pure (sorted)
--     )
--    guard $ arg2 == sorted
--    pure ()
--   )
--  pure ()

sort_io arg1 = do
  -- solution: arg2[0,1] arg2[0] arg2[] data0[0,2,0,1,0] data0[0,2,0,1] list[0,0] sorted[0,2,0,0,0] sorted[0,2,0,0] sorted[0,2,0] sorted[0,2] ~arg1[0,0] ~arg1[0] ~arg1[] ~data0[0,2,0,0,0] ~data0[0,2,0,0] ~list[0,2,0,0,0] ~list[0,2,0,0] ~list[0,2,0] ~list[0,2] ~sorted[0,1]
  (arg2) <- (do
    list <- pure arg1
    (sorted) <- (do
      (sorted) <- (do
        (data0) <- (do
          data0 <- pure []
          pure (data0)
         )
        (sorted) <- (do
          (sorted) <- qsort_ioi list data0
          pure (sorted)
         )
        pure (sorted)
       )
      pure (sorted)
     )
    arg2 <- pure sorted
    pure (arg2)
   )
  pure (arg2)
