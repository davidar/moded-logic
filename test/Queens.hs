{-# LANGUAGE DataKinds, FlexibleContexts, NoImplicitPrelude, NoMonomorphismRestriction, TypeApplications #-}
module Queens where

import qualified Control.Monad.Logic as Logic
import Control.Monad.Logic.Moded.Prelude

{- qdelete/3
qdelete arg1 arg2 arg3 :- ((arg2 = h0:t1, h0 = h, t1 = t, arg1 = h, arg3 = t); (arg2 = h2:t3, h2 = h, t3 = t, arg3 = h4:r, h4 = h, qdelete x t r, arg1 = x)).
constraints:
~(arg1[0,3] & h[0,3])
~(arg1[1,6] & x[1,6])
~(arg2[0,0] & h0[0,0])
~(arg2[1,0] & h2[1,0])
~(arg3[0,4] & t[0,4])
~(arg3[1,3] & h4[1,3])
~(h[0,1] & h[0,3])
~(h[1,1] & h[1,4])
~(h0[0,0] & h0[0,1])
~(h0[0,1] & h[0,1])
~(h2[1,0] & h2[1,1])
~(h2[1,1] & h[1,1])
~(h4[1,3] & h4[1,4])
~(h4[1,4] & h[1,4])
~(r[1,3] & r[1,5])
~(t[0,2] & t[0,4])
~(t[1,2] & t[1,5])
~(t1[0,0] & t1[0,2])
~(t1[0,2] & t[0,2])
~(t3[1,0] & t3[1,2])
~(t3[1,2] & t[1,2])
~(x[1,5] & x[1,6])
(h[0,1] | h[0,3])
(h[1,1] | h[1,4])
(h0[0,0] | h0[0,1])
(h2[1,0] | h2[1,1])
(h4[1,3] | h4[1,4])
(r[1,3] | r[1,5])
(t[0,2] | t[0,4])
(t[1,2] | t[1,5])
(t1[0,0] | t1[0,2])
(t3[1,0] | t3[1,2])
(x[1,5] | x[1,6])
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg1[0] <-> arg1[0,3])
(arg1[1] <-> arg1[1,6])
(arg2[] <-> arg2[0])
(arg2[] <-> arg2[1])
(arg2[0] <-> arg2[0,0])
(arg2[1] <-> arg2[1,0])
(arg3[] <-> arg3[0])
(arg3[] <-> arg3[1])
(arg3[0] <-> arg3[0,4])
(arg3[1] <-> arg3[1,3])
(h0[0,0] <-> t1[0,0])
(h2[1,0] <-> t3[1,0])
(h4[1,3] <-> r[1,3])
(r[1,5] <-> arg3[])
(t[1,5] <-> arg2[])
(x[1,5] <-> arg1[])
1
-}

qdelete = rget $ (procedure @'[ 'In, 'In, 'In ] qdeleteIII) :& (procedure @'[ 'In, 'In, 'Out ] qdeleteIIO) :& (procedure @'[ 'In, 'Out, 'In ] qdeleteIOI) :& (procedure @'[ 'Out, 'In, 'In ] qdeleteOII) :& (procedure @'[ 'Out, 'In, 'Out ] qdeleteOIO) :& RNil
  where
    qdeleteIII = \arg1 arg2 arg3 -> Logic.once $ do
      -- solution: h[0,1] h[1,1] h0[0,0] h2[1,0] h4[1,3] r[1,3] t[0,2] t[1,2] t1[0,0] t3[1,0] x[1,6] ~arg1[] ~arg1[0] ~arg1[0,3] ~arg1[1] ~arg1[1,6] ~arg2[] ~arg2[0] ~arg2[0,0] ~arg2[1] ~arg2[1,0] ~arg3[] ~arg3[0] ~arg3[0,4] ~arg3[1] ~arg3[1,3] ~h[0,3] ~h[1,4] ~h0[0,1] ~h2[1,1] ~h4[1,4] ~r[1,5] ~t[0,4] ~t[1,5] ~t1[0,2] ~t3[1,2] ~x[1,5]
      -- cost: 1
      () <- (do
        (h0:t1) <- pure arg2
        h <- pure h0
        guard $ arg1 == h
        t <- pure t1
        guard $ arg3 == t
        pure ()
       ) <|> (do
        x <- pure arg1
        (h2:t3) <- pure arg2
        h <- pure h2
        t <- pure t3
        (h4:r) <- pure arg3
        guard $ h4 == h
        () <- qdeleteIII x t r
        pure ()
       )
      pure ()
    
    qdeleteIIO = \arg1 arg2 -> do
      -- solution: arg3[] arg3[0] arg3[0,4] arg3[1] arg3[1,3] h[0,1] h[1,1] h0[0,0] h2[1,0] h4[1,4] r[1,5] t[0,2] t[1,2] t1[0,0] t3[1,0] x[1,6] ~arg1[] ~arg1[0] ~arg1[0,3] ~arg1[1] ~arg1[1,6] ~arg2[] ~arg2[0] ~arg2[0,0] ~arg2[1] ~arg2[1,0] ~h[0,3] ~h[1,4] ~h0[0,1] ~h2[1,1] ~h4[1,3] ~r[1,3] ~t[0,4] ~t[1,5] ~t1[0,2] ~t3[1,2] ~x[1,5]
      -- cost: 2
      (arg3) <- (do
        (h0:t1) <- pure arg2
        h <- pure h0
        guard $ arg1 == h
        t <- pure t1
        arg3 <- pure t
        pure (arg3)
       ) <|> (do
        x <- pure arg1
        (h2:t3) <- pure arg2
        h <- pure h2
        h4 <- pure h
        t <- pure t3
        (OneTuple (r)) <- qdeleteIIO x t
        arg3 <- pure (h4:r)
        pure (arg3)
       )
      pure (OneTuple (arg3))
    
    qdeleteIOI = \arg1 arg3 -> do
      -- solution: arg2[] arg2[0] arg2[0,0] arg2[1] arg2[1,0] h[0,3] h[1,4] h0[0,1] h2[1,1] h4[1,3] r[1,3] t[0,4] t[1,5] t1[0,2] t3[1,2] x[1,6] ~arg1[] ~arg1[0] ~arg1[0,3] ~arg1[1] ~arg1[1,6] ~arg3[] ~arg3[0] ~arg3[0,4] ~arg3[1] ~arg3[1,3] ~h[0,1] ~h[1,1] ~h0[0,0] ~h2[1,0] ~h4[1,4] ~r[1,5] ~t[0,2] ~t[1,2] ~t1[0,0] ~t3[1,0] ~x[1,5]
      -- cost: 2
      (arg2) <- (do
        h <- pure arg1
        t <- pure arg3
        h0 <- pure h
        t1 <- pure t
        arg2 <- pure (h0:t1)
        pure (arg2)
       ) <|> (do
        x <- pure arg1
        (h4:r) <- pure arg3
        h <- pure h4
        h2 <- pure h
        (OneTuple (t)) <- qdeleteIOI x r
        t3 <- pure t
        arg2 <- pure (h2:t3)
        pure (arg2)
       )
      pure (OneTuple (arg2))
    
    qdeleteOII = \arg2 arg3 -> do
      -- solution: arg1[] arg1[0] arg1[0,3] arg1[1] arg1[1,6] h[0,1] h[1,1] h0[0,0] h2[1,0] h4[1,3] r[1,3] t[0,2] t[1,2] t1[0,0] t3[1,0] x[1,5] ~arg2[] ~arg2[0] ~arg2[0,0] ~arg2[1] ~arg2[1,0] ~arg3[] ~arg3[0] ~arg3[0,4] ~arg3[1] ~arg3[1,3] ~h[0,3] ~h[1,4] ~h0[0,1] ~h2[1,1] ~h4[1,4] ~r[1,5] ~t[0,4] ~t[1,5] ~t1[0,2] ~t3[1,2] ~x[1,6]
      -- cost: 2
      (arg1) <- (do
        (h0:t1) <- pure arg2
        h <- pure h0
        arg1 <- pure h
        t <- pure t1
        guard $ arg3 == t
        pure (arg1)
       ) <|> (do
        (h2:t3) <- pure arg2
        h <- pure h2
        t <- pure t3
        (h4:r) <- pure arg3
        guard $ h4 == h
        (OneTuple (x)) <- qdeleteOII t r
        arg1 <- pure x
        pure (arg1)
       )
      pure (OneTuple (arg1))
    
    qdeleteOIO = \arg2 -> do
      -- solution: arg1[] arg1[0] arg1[0,3] arg1[1] arg1[1,6] arg3[] arg3[0] arg3[0,4] arg3[1] arg3[1,3] h[0,1] h[1,1] h0[0,0] h2[1,0] h4[1,4] r[1,5] t[0,2] t[1,2] t1[0,0] t3[1,0] x[1,5] ~arg2[] ~arg2[0] ~arg2[0,0] ~arg2[1] ~arg2[1,0] ~h[0,3] ~h[1,4] ~h0[0,1] ~h2[1,1] ~h4[1,3] ~r[1,3] ~t[0,4] ~t[1,5] ~t1[0,2] ~t3[1,2] ~x[1,6]
      -- cost: 3
      (arg1,arg3) <- (do
        (h0:t1) <- pure arg2
        h <- pure h0
        arg1 <- pure h
        t <- pure t1
        arg3 <- pure t
        pure (arg1,arg3)
       ) <|> (do
        (h2:t3) <- pure arg2
        h <- pure h2
        h4 <- pure h
        t <- pure t3
        (x,r) <- qdeleteOIO t
        arg1 <- pure x
        arg3 <- pure (h4:r)
        pure (arg1,arg3)
       )
      pure (arg1,arg3)
    
{- qperm/2
qperm arg1 arg2 :- ((arg1 = [], arg2 = []); (arg2 = h:t, qdelete h xs ys, qperm ys t, arg1 = xs)).
constraints:
~(arg1[1,3] & xs[1,3])
~(arg2[1,0] & h[1,0])
~(h[1,0] & h[1,1])
~(t[1,0] & t[1,2])
~(xs[1,1] & xs[1,3])
~(ys[1,1] & ys[1,2])
(h[1,0] | h[1,1])
(t[1,0] | t[1,2])
(xs[1,1] | xs[1,3])
(ys[1,1] | ys[1,2])
((h[1,1] & (~xs[1,1] & ys[1,1])) | ((h[1,1] & (~xs[1,1] & ~ys[1,1])) | ((~h[1,1] & (xs[1,1] & ~ys[1,1])) | ((~h[1,1] & (~xs[1,1] & ys[1,1])) | (~h[1,1] & (~xs[1,1] & ~ys[1,1]))))))
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg1[0] <-> arg1[0,0])
(arg1[1] <-> arg1[1,3])
(arg2[] <-> arg2[0])
(arg2[] <-> arg2[1])
(arg2[0] <-> arg2[0,1])
(arg2[1] <-> arg2[1,0])
(h[1,0] <-> t[1,0])
(t[1,2] <-> arg2[])
(ys[1,2] <-> arg1[])
1
-}

qperm = rget $ (procedure @'[ 'In, 'In ] qpermII) :& (procedure @'[ 'In, 'Out ] qpermIO) :& (procedure @'[ 'Out, 'In ] qpermOI) :& RNil
  where
    qpermII = \arg1 arg2 -> Logic.once $ do
      -- solution: h[1,0] t[1,0] xs[1,3] ys[1,1] ~arg1[] ~arg1[0] ~arg1[0,0] ~arg1[1] ~arg1[1,3] ~arg2[] ~arg2[0] ~arg2[0,1] ~arg2[1] ~arg2[1,0] ~h[1,1] ~t[1,2] ~xs[1,1] ~ys[1,2]
      -- cost: 3
      () <- (do
        guard $ arg1 == []
        guard $ arg2 == []
        pure ()
       ) <|> (do
        xs <- pure arg1
        (h:t) <- pure arg2
        (OneTuple (ys)) <- runProcedure @'[ 'In, 'In, 'Out ] qdelete h xs
        () <- qpermII ys t
        pure ()
       )
      pure ()
    
    qpermIO = \arg1 -> do
      -- solution: arg2[] arg2[0] arg2[0,1] arg2[1] arg2[1,0] h[1,1] t[1,2] xs[1,3] ys[1,1] ~arg1[] ~arg1[0] ~arg1[0,0] ~arg1[1] ~arg1[1,3] ~h[1,0] ~t[1,0] ~xs[1,1] ~ys[1,2]
      -- cost: 5
      (arg2) <- (do
        guard $ arg1 == []
        arg2 <- pure []
        pure (arg2)
       ) <|> (do
        xs <- pure arg1
        (h,ys) <- runProcedure @'[ 'Out, 'In, 'Out ] qdelete xs
        (OneTuple (t)) <- qpermIO ys
        arg2 <- pure (h:t)
        pure (arg2)
       )
      pure (OneTuple (arg2))
    
    qpermOI = \arg2 -> do
      -- solution: arg1[] arg1[0] arg1[0,0] arg1[1] arg1[1,3] h[1,0] t[1,0] xs[1,1] ys[1,2] ~arg2[] ~arg2[0] ~arg2[0,1] ~arg2[1] ~arg2[1,0] ~h[1,1] ~t[1,2] ~xs[1,3] ~ys[1,1]
      -- cost: 4
      (arg1) <- (do
        arg1 <- pure []
        guard $ arg2 == []
        pure (arg1)
       ) <|> (do
        (h:t) <- pure arg2
        (OneTuple (ys)) <- qpermOI t
        (OneTuple (xs)) <- runProcedure @'[ 'In, 'Out, 'In ] qdelete h ys
        arg1 <- pure xs
        pure (arg1)
       )
      pure (OneTuple (arg1))
    
{- nodiag/3
nodiag arg1 arg2 arg3 :- ((arg3 = []); (arg3 = h:t, plus hmb b h, plus bmh h b, succ d d1, if (d = hmb) then (empty) else (if (d = bmh) then (empty) else (nodiag b d1 t)), arg1 = b, arg2 = d)).
constraints:
~arg1[]
~arg2[]
~b[1,4,2]
~b[1,4,2,0,2]
~bmh[1,4,2]
~bmh[1,4,2,0]
~bmh[1,4,2,0,0,0]
~d[1,4,0,0]
~d[1,4,2]
~d[1,4,2,0]
~d[1,4,2,0,0,0]
~d1[1,4,2]
~d1[1,4,2,0,2]
~hmb[1,4]
~hmb[1,4,0,0]
~t[1,4,2]
~t[1,4,2,0,2]
~(arg1[1,5] & b[1,5])
~(arg2[1,6] & d[1,6])
~(arg3[1,0] & h[1,0])
~(b[1,1] & b[1,2])
~(b[1,1] & b[1,4])
~(b[1,1] & b[1,5])
~(b[1,2] & b[1,4])
~(b[1,2] & b[1,5])
~(b[1,4] & b[1,5])
~(bmh[1,2] & bmh[1,4])
~(d[1,3] & d[1,4])
~(d[1,3] & d[1,6])
~(d[1,4] & d[1,6])
~(d[1,4,0,0] & hmb[1,4,0,0])
~(d[1,4,2,0,0,0] & bmh[1,4,2,0,0,0])
~(d1[1,3] & d1[1,4])
~(h[1,0] & h[1,1])
~(h[1,0] & h[1,2])
~(h[1,1] & h[1,2])
~(hmb[1,1] & hmb[1,4])
~(t[1,0] & t[1,4])
(b[1,1] | (b[1,2] | (b[1,4] | b[1,5])))
(bmh[1,2] | bmh[1,4])
(d[1,3] | (d[1,4] | d[1,6]))
(d1[1,3] | d1[1,4])
(h[1,0] | (h[1,1] | h[1,2]))
(hmb[1,1] | hmb[1,4])
(t[1,0] | t[1,4])
((bmh[1,2] & (~h[1,2] & ~b[1,2])) | ((~bmh[1,2] & (h[1,2] & ~b[1,2])) | (~bmh[1,2] & (~h[1,2] & b[1,2]))))
((d[1,3] & ~d1[1,3]) | ((~d[1,3] & d1[1,3]) | (~d[1,3] & ~d1[1,3])))
((hmb[1,1] & (~b[1,1] & ~h[1,1])) | ((~hmb[1,1] & (b[1,1] & ~h[1,1])) | (~hmb[1,1] & (~b[1,1] & h[1,1]))))
(arg1[] <-> arg1[1])
(arg1[1] <-> arg1[1,5])
(arg2[] <-> arg2[1])
(arg2[1] <-> arg2[1,6])
(arg3[] <-> arg3[0])
(arg3[] <-> arg3[1])
(arg3[0] <-> arg3[0,0])
(arg3[1] <-> arg3[1,0])
(b[1,4] <-> b[1,4,2])
(b[1,4,2] <-> b[1,4,2,0])
(b[1,4,2,0] <-> b[1,4,2,0,2])
(b[1,4,2,0,2] <-> b[1,4,2,0,2,0])
(b[1,4,2,0,2,0] <-> arg1[])
(bmh[1,4] <-> bmh[1,4,2])
(bmh[1,4,2] <-> bmh[1,4,2,0])
(d[1,4] <-> d[1,4,2])
(d[1,4,2] <-> d[1,4,2,0])
(d1[1,4] <-> d1[1,4,2])
(d1[1,4,2] <-> d1[1,4,2,0])
(d1[1,4,2,0] <-> d1[1,4,2,0,2])
(d1[1,4,2,0,2] <-> d1[1,4,2,0,2,0])
(d1[1,4,2,0,2,0] <-> arg2[])
(h[1,0] <-> t[1,0])
(t[1,4] <-> t[1,4,2])
(t[1,4,2] <-> t[1,4,2,0])
(t[1,4,2,0] <-> t[1,4,2,0,2])
(t[1,4,2,0,2] <-> t[1,4,2,0,2,0])
(t[1,4,2,0,2,0] <-> arg3[])
1
-}

nodiag = rget $ (procedure @'[ 'In, 'In, 'In ] nodiagIII) :& RNil
  where
    nodiagIII = \arg1 arg2 arg3 -> Logic.once $ do
      -- solution: b[1,5] bmh[1,2] d[1,6] d1[1,3] h[1,0] hmb[1,1] t[1,0] ~arg1[] ~arg1[1] ~arg1[1,5] ~arg2[] ~arg2[1] ~arg2[1,6] ~arg3[] ~arg3[0] ~arg3[0,0] ~arg3[1] ~arg3[1,0] ~b[1,1] ~b[1,2] ~b[1,4] ~b[1,4,2] ~b[1,4,2,0] ~b[1,4,2,0,2] ~b[1,4,2,0,2,0] ~bmh[1,4] ~bmh[1,4,2] ~bmh[1,4,2,0] ~bmh[1,4,2,0,0,0] ~d[1,3] ~d[1,4] ~d[1,4,0,0] ~d[1,4,2] ~d[1,4,2,0] ~d[1,4,2,0,0,0] ~d1[1,4] ~d1[1,4,2] ~d1[1,4,2,0] ~d1[1,4,2,0,2] ~d1[1,4,2,0,2,0] ~h[1,1] ~h[1,2] ~hmb[1,4] ~hmb[1,4,0,0] ~t[1,4] ~t[1,4,2] ~t[1,4,2,0] ~t[1,4,2,0,2] ~t[1,4,2,0,2,0]
      -- cost: 9
      () <- (do
        guard $ arg3 == []
        pure ()
       ) <|> (do
        b <- pure arg1
        d <- pure arg2
        (h:t) <- pure arg3
        (OneTuple (bmh)) <- runProcedure @'[ 'Out, 'In, 'In ] plus h b
        (OneTuple (hmb)) <- runProcedure @'[ 'Out, 'In, 'In ] plus b h
        (OneTuple (d1)) <- runProcedure @'[ 'In, 'Out ] succ d
        () <- Logic.ifte ((do
          guard $ d == hmb
          pure ()
         )) (\() -> (do
          () <- empty 
          pure ()
         )) ((do
          () <- Logic.ifte ((do
            guard $ d == bmh
            pure ()
           )) (\() -> (do
            () <- empty 
            pure ()
           )) ((do
            () <- nodiagIII b d1 t
            pure ()
           ))
          pure ()
         ))
        pure ()
       )
      pure ()
    
{- safe/1
safe arg1 :- ((arg1 = []); (arg1 = h:t, nodiag h data0 t, data0 = 1, safe t)).
constraints:
~(arg1[1,0] & h[1,0])
~(data0[1,1] & data0[1,2])
~(h[1,0] & h[1,1])
~(t[1,0] & t[1,1])
~(t[1,0] & t[1,3])
~(t[1,1] & t[1,3])
(~h[1,1] & (~data0[1,1] & ~t[1,1]))
(data0[1,1] | data0[1,2])
(h[1,0] | h[1,1])
(t[1,0] | (t[1,1] | t[1,3]))
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg1[0] <-> arg1[0,0])
(arg1[1] <-> arg1[1,0])
(h[1,0] <-> t[1,0])
(t[1,3] <-> arg1[])
1
-}

safe = rget $ (procedure @'[ 'In ] safeI) :& RNil
  where
    safeI = \arg1 -> Logic.once $ do
      -- solution: data0[1,2] h[1,0] t[1,0] ~arg1[] ~arg1[0] ~arg1[0,0] ~arg1[1] ~arg1[1,0] ~data0[1,1] ~h[1,1] ~t[1,1] ~t[1,3]
      -- cost: 2
      () <- (do
        guard $ arg1 == []
        pure ()
       ) <|> (do
        data0 <- pure 1
        (h:t) <- pure arg1
        () <- runProcedure @'[ 'In, 'In, 'In ] nodiag h data0 t
        () <- safeI t
        pure ()
       )
      pure ()
    
{- queens1/2
queens1 dat out :- ((qperm dat out, safe out)).
constraints:
~out[0,1]
~(out[0,0] & out[0,1])
((dat[0,0] & ~out[0,0]) | ((~dat[0,0] & out[0,0]) | (~dat[0,0] & ~out[0,0])))
(dat[] <-> dat[0])
(dat[0] <-> dat[0,0])
(out[] <-> out[0])
(out[0] <-> (out[0,0] | out[0,1]))
1
-}

queens1 = rget $ (procedure @'[ 'In, 'In ] queens1II) :& (procedure @'[ 'In, 'Out ] queens1IO) :& (procedure @'[ 'Out, 'In ] queens1OI) :& RNil
  where
    queens1II = \dat out -> Logic.once $ do
      -- solution: ~dat[] ~dat[0] ~dat[0,0] ~out[] ~out[0] ~out[0,0] ~out[0,1]
      -- cost: 2
      () <- (do
        () <- runProcedure @'[ 'In, 'In ] qperm dat out
        () <- runProcedure @'[ 'In ] safe out
        pure ()
       )
      pure ()
    
    queens1IO = \dat -> do
      -- solution: out[] out[0] out[0,0] ~dat[] ~dat[0] ~dat[0,0] ~out[0,1]
      -- cost: 3
      (out) <- (do
        (OneTuple (out)) <- runProcedure @'[ 'In, 'Out ] qperm dat
        () <- runProcedure @'[ 'In ] safe out
        pure (out)
       )
      pure (OneTuple (out))
    
    queens1OI = \out -> do
      -- solution: dat[] dat[0] dat[0,0] ~out[] ~out[0] ~out[0,0] ~out[0,1]
      -- cost: 3
      (dat) <- (do
        () <- runProcedure @'[ 'In ] safe out
        (OneTuple (dat)) <- runProcedure @'[ 'Out, 'In ] qperm out
        pure (dat)
       )
      pure (OneTuple (dat))
    
{- cqueens/3
cqueens arg1 arg2 arg3 :- ((arg1 = [], arg3 = []); (arg3 = q0:m, q0 = q, xs = _:_, qdelete q xs r, nodiag q data0 history, data0 = 1, cqueens r data1 m, data1 = q1:history, q1 = q, arg1 = xs, arg2 = history)).
constraints:
~arg2[]
~xs[1,2]
~(arg1[1,9] & xs[1,9])
~(arg2[1,10] & history[1,10])
~(arg3[1,0] & q0[1,0])
~(data0[1,4] & data0[1,5])
~(data1[1,6] & data1[1,7])
~(data1[1,7] & q1[1,7])
~(history[1,4] & history[1,7])
~(history[1,4] & history[1,10])
~(history[1,7] & history[1,10])
~(m[1,0] & m[1,6])
~(q[1,1] & q[1,3])
~(q[1,1] & q[1,4])
~(q[1,1] & q[1,8])
~(q[1,3] & q[1,4])
~(q[1,3] & q[1,8])
~(q[1,4] & q[1,8])
~(q0[1,0] & q0[1,1])
~(q0[1,1] & q[1,1])
~(q1[1,7] & q1[1,8])
~(q1[1,8] & q[1,8])
~(r[1,3] & r[1,6])
~(xs[1,2] & xs[1,3])
~(xs[1,2] & xs[1,9])
~(xs[1,3] & xs[1,9])
(~q[1,4] & (~data0[1,4] & ~history[1,4]))
(data0[1,4] | data0[1,5])
(data1[1,6] | data1[1,7])
(history[1,4] | (history[1,7] | history[1,10]))
(m[1,0] | m[1,6])
(q[1,1] | (q[1,3] | (q[1,4] | q[1,8])))
(q0[1,0] | q0[1,1])
(q1[1,7] | q1[1,8])
(r[1,3] | r[1,6])
(xs[1,2] | (xs[1,3] | xs[1,9]))
((q[1,3] & (~xs[1,3] & r[1,3])) | ((q[1,3] & (~xs[1,3] & ~r[1,3])) | ((~q[1,3] & (xs[1,3] & ~r[1,3])) | ((~q[1,3] & (~xs[1,3] & r[1,3])) | (~q[1,3] & (~xs[1,3] & ~r[1,3]))))))
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg1[0] <-> arg1[0,0])
(arg1[1] <-> arg1[1,9])
(arg2[] <-> arg2[1])
(arg2[1] <-> arg2[1,10])
(arg3[] <-> arg3[0])
(arg3[] <-> arg3[1])
(arg3[0] <-> arg3[0,1])
(arg3[1] <-> arg3[1,0])
(data1[1,6] <-> arg2[])
(m[1,6] <-> arg3[])
(q0[1,0] <-> m[1,0])
(q1[1,7] <-> history[1,7])
(r[1,6] <-> arg1[])
1
-}

cqueens = rget $ (procedure @'[ 'In, 'In, 'In ] cqueensIII) :& (procedure @'[ 'In, 'In, 'Out ] cqueensIIO) :& (procedure @'[ 'Out, 'In, 'In ] cqueensOII) :& RNil
  where
    cqueensIII = \arg1 arg2 arg3 -> Logic.once $ do
      -- solution: data0[1,5] data1[1,7] history[1,10] m[1,0] q[1,1] q0[1,0] q1[1,8] r[1,3] xs[1,9] ~arg1[] ~arg1[0] ~arg1[0,0] ~arg1[1] ~arg1[1,9] ~arg2[] ~arg2[1] ~arg2[1,10] ~arg3[] ~arg3[0] ~arg3[0,1] ~arg3[1] ~arg3[1,0] ~data0[1,4] ~data1[1,6] ~history[1,4] ~history[1,7] ~m[1,6] ~q[1,3] ~q[1,4] ~q[1,8] ~q0[1,1] ~q1[1,7] ~r[1,6] ~xs[1,2] ~xs[1,3]
      -- cost: 4
      () <- (do
        guard $ arg1 == []
        guard $ arg3 == []
        pure ()
       ) <|> (do
        xs <- pure arg1
        history <- pure arg2
        data0 <- pure 1
        (_:_) <- pure xs
        (q0:m) <- pure arg3
        q <- pure q0
        q1 <- pure q
        data1 <- pure (q1:history)
        () <- runProcedure @'[ 'In, 'In, 'In ] nodiag q data0 history
        (OneTuple (r)) <- runProcedure @'[ 'In, 'In, 'Out ] qdelete q xs
        () <- cqueensIII r data1 m
        pure ()
       )
      pure ()
    
    cqueensIIO = \arg1 arg2 -> do
      -- solution: arg3[] arg3[0] arg3[0,1] arg3[1] arg3[1,0] data0[1,5] data1[1,7] history[1,10] m[1,6] q[1,3] q0[1,1] q1[1,8] r[1,3] xs[1,9] ~arg1[] ~arg1[0] ~arg1[0,0] ~arg1[1] ~arg1[1,9] ~arg2[] ~arg2[1] ~arg2[1,10] ~data0[1,4] ~data1[1,6] ~history[1,4] ~history[1,7] ~m[1,0] ~q[1,1] ~q[1,4] ~q[1,8] ~q0[1,0] ~q1[1,7] ~r[1,6] ~xs[1,2] ~xs[1,3]
      -- cost: 6
      (arg3) <- (do
        guard $ arg1 == []
        arg3 <- pure []
        pure (arg3)
       ) <|> (do
        xs <- pure arg1
        history <- pure arg2
        data0 <- pure 1
        (_:_) <- pure xs
        (q,r) <- runProcedure @'[ 'Out, 'In, 'Out ] qdelete xs
        q0 <- pure q
        q1 <- pure q
        data1 <- pure (q1:history)
        () <- runProcedure @'[ 'In, 'In, 'In ] nodiag q data0 history
        (OneTuple (m)) <- cqueensIIO r data1
        arg3 <- pure (q0:m)
        pure (arg3)
       )
      pure (OneTuple (arg3))
    
    cqueensOII = \arg2 arg3 -> do
      -- solution: arg1[] arg1[0] arg1[0,0] arg1[1] arg1[1,9] data0[1,5] data1[1,7] history[1,10] m[1,0] q[1,1] q0[1,0] q1[1,8] r[1,6] xs[1,3] ~arg2[] ~arg2[1] ~arg2[1,10] ~arg3[] ~arg3[0] ~arg3[0,1] ~arg3[1] ~arg3[1,0] ~data0[1,4] ~data1[1,6] ~history[1,4] ~history[1,7] ~m[1,6] ~q[1,3] ~q[1,4] ~q[1,8] ~q0[1,1] ~q1[1,7] ~r[1,3] ~xs[1,2] ~xs[1,9]
      -- cost: 5
      (arg1) <- (do
        arg1 <- pure []
        guard $ arg3 == []
        pure (arg1)
       ) <|> (do
        history <- pure arg2
        data0 <- pure 1
        (q0:m) <- pure arg3
        q <- pure q0
        q1 <- pure q
        data1 <- pure (q1:history)
        () <- runProcedure @'[ 'In, 'In, 'In ] nodiag q data0 history
        (OneTuple (r)) <- cqueensOII data1 m
        (OneTuple (xs)) <- runProcedure @'[ 'In, 'Out, 'In ] qdelete q r
        arg1 <- pure xs
        (_:_) <- pure xs
        pure (arg1)
       )
      pure (OneTuple (arg1))
    
{- queens2/2
queens2 dat out :- ((cqueens dat data0 out, data0 = [])).
constraints:
~(data0[0,0] & data0[0,1])
(data0[0,0] | data0[0,1])
((dat[0,0] & (~data0[0,0] & ~out[0,0])) | ((~dat[0,0] & (~data0[0,0] & out[0,0])) | (~dat[0,0] & (~data0[0,0] & ~out[0,0]))))
(dat[] <-> dat[0])
(dat[0] <-> dat[0,0])
(out[] <-> out[0])
(out[0] <-> out[0,0])
1
-}

queens2 = rget $ (procedure @'[ 'In, 'In ] queens2II) :& (procedure @'[ 'In, 'Out ] queens2IO) :& (procedure @'[ 'Out, 'In ] queens2OI) :& RNil
  where
    queens2II = \dat out -> Logic.once $ do
      -- solution: data0[0,1] ~dat[] ~dat[0] ~dat[0,0] ~data0[0,0] ~out[] ~out[0] ~out[0,0]
      -- cost: 1
      () <- (do
        data0 <- pure []
        () <- runProcedure @'[ 'In, 'In, 'In ] cqueens dat data0 out
        pure ()
       )
      pure ()
    
    queens2IO = \dat -> do
      -- solution: data0[0,1] out[] out[0] out[0,0] ~dat[] ~dat[0] ~dat[0,0] ~data0[0,0]
      -- cost: 2
      (out) <- (do
        data0 <- pure []
        (OneTuple (out)) <- runProcedure @'[ 'In, 'In, 'Out ] cqueens dat data0
        pure (out)
       )
      pure (OneTuple (out))
    
    queens2OI = \out -> do
      -- solution: dat[] dat[0] dat[0,0] data0[0,1] ~data0[0,0] ~out[] ~out[0] ~out[0,0]
      -- cost: 2
      (dat) <- (do
        data0 <- pure []
        (OneTuple (dat)) <- runProcedure @'[ 'Out, 'In, 'In ] cqueens data0 out
        pure (dat)
       )
      pure (OneTuple (dat))
    