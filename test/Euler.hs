{-# LANGUAGE DataKinds, FlexibleContexts, NoImplicitPrelude, NoMonomorphismRestriction, TypeApplications #-}
module Euler where

import qualified Control.Monad.Logic as Logic
import Control.Monad.Logic.Moded.Prelude

{- nat/1
nat arg1 :- ((arg1 = 0); (nat n, succ n n', arg1 = n')).
constraints:
~(arg1[1,2] & n'[1,2])
~(n[1,0] & n[1,1])
~(n'[1,1] & n'[1,2])
(n[1,0] | n[1,1])
(n'[1,1] | n'[1,2])
((n[1,1] & ~n'[1,1]) | ((~n[1,1] & n'[1,1]) | (~n[1,1] & ~n'[1,1])))
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg1[0] <-> arg1[0,0])
(arg1[1] <-> arg1[1,2])
(n[1,0] <-> arg1[])
1
-}

nat = rget $ (procedure @'[ 'In ] natI) :& (procedure @'[ 'Out ] natO) :& RNil
  where
    natI = \arg1 -> Logic.once $ do
      -- solution: n[1,1] n'[1,2] ~arg1[] ~arg1[0] ~arg1[0,0] ~arg1[1] ~arg1[1,2] ~n[1,0] ~n'[1,1]
      -- cost: 3
      () <- (do
        guard $ arg1 == 0
        pure ()
       ) <|> (do
        n' <- pure arg1
        (OneTuple (n)) <- runProcedure @'[ 'Out, 'In ] succ n'
        () <- natI n
        pure ()
       )
      pure ()
    
    natO = do
      -- solution: arg1[] arg1[0] arg1[0,0] arg1[1] arg1[1,2] n[1,0] n'[1,1] ~n[1,1] ~n'[1,2]
      -- cost: 4
      (arg1) <- (do
        arg1 <- pure 0
        pure (arg1)
       ) <|> (do
        (OneTuple (n)) <- natO 
        (OneTuple (n')) <- runProcedure @'[ 'In, 'Out ] succ n
        arg1 <- pure n'
        pure (arg1)
       )
      pure (OneTuple (arg1 :: Integer))
    
{- oddNat/1
oddNat arg1 :- ((arg1 = 1); (oddNat n, plus n data0 n', data0 = 2, arg1 = n')).
constraints:
~(arg1[1,3] & n'[1,3])
~(data0[1,1] & data0[1,2])
~(n[1,0] & n[1,1])
~(n'[1,1] & n'[1,3])
(data0[1,1] | data0[1,2])
(n[1,0] | n[1,1])
(n'[1,1] | n'[1,3])
((n[1,1] & (~data0[1,1] & ~n'[1,1])) | ((~n[1,1] & (data0[1,1] & ~n'[1,1])) | (~n[1,1] & (~data0[1,1] & n'[1,1]))))
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg1[0] <-> arg1[0,0])
(arg1[1] <-> arg1[1,3])
(n[1,0] <-> arg1[])
1
-}

oddNat = rget $ (procedure @'[ 'In ] oddNatI) :& (procedure @'[ 'Out ] oddNatO) :& RNil
  where
    oddNatI = \arg1 -> Logic.once $ do
      -- solution: data0[1,2] n[1,1] n'[1,3] ~arg1[] ~arg1[0] ~arg1[0,0] ~arg1[1] ~arg1[1,3] ~data0[1,1] ~n[1,0] ~n'[1,1]
      -- cost: 3
      () <- (do
        guard $ arg1 == 1
        pure ()
       ) <|> (do
        n' <- pure arg1
        data0 <- pure 2
        (OneTuple (n)) <- runProcedure @'[ 'Out, 'In, 'In ] plus data0 n'
        () <- oddNatI n
        pure ()
       )
      pure ()
    
    oddNatO = do
      -- solution: arg1[] arg1[0] arg1[0,0] arg1[1] arg1[1,3] data0[1,2] n[1,0] n'[1,1] ~data0[1,1] ~n[1,1] ~n'[1,3]
      -- cost: 4
      (arg1) <- (do
        arg1 <- pure 1
        pure (arg1)
       ) <|> (do
        data0 <- pure 2
        (OneTuple (n)) <- oddNatO 
        (OneTuple (n')) <- runProcedure @'[ 'In, 'In, 'Out ] plus n data0
        arg1 <- pure n'
        pure (arg1)
       )
      pure (OneTuple (arg1))
    
{- even/1
even x :- ((mod x data0 data1, data0 = 2, data1 = 0)).
constraints:
~(data0[0,0] & data0[0,1])
~(data1[0,0] & data1[0,2])
(data0[0,0] | data0[0,1])
(data1[0,0] | data1[0,2])
((~x[0,0] & (~data0[0,0] & data1[0,0])) | (~x[0,0] & (~data0[0,0] & ~data1[0,0])))
(x[] <-> x[0])
(x[0] <-> x[0,0])
1
-}

even = rget $ (procedure @'[ 'In ] evenI) :& RNil
  where
    evenI = \x -> Logic.once $ do
      -- solution: data0[0,1] data1[0,2] ~data0[0,0] ~data1[0,0] ~x[] ~x[0] ~x[0,0]
      -- cost: 1
      () <- (do
        data1 <- pure 0
        data0 <- pure 2
        () <- runProcedure @'[ 'In, 'In, 'In ] mod x data0 data1
        pure ()
       )
      pure ()
    
{- elem/2
elem x arg2 :- ((arg2 = x:_); (arg2 = _:xs, elem x xs)).
constraints:
x[0,0]
xs[1,0]
~arg2[1,0]
~(arg2[0,0] & x[0,0])
~(xs[1,0] & xs[1,1])
(xs[1,0] | xs[1,1])
(arg2[] <-> arg2[0])
(arg2[] <-> arg2[1])
(arg2[0] <-> arg2[0,0])
(arg2[1] <-> arg2[1,0])
(x[] <-> x[0])
(x[] <-> x[1])
(x[0] <-> x[0,0])
(x[1] <-> x[1,1])
(x[1,1] <-> x[])
(xs[1,1] <-> arg2[])
1
-}

elem = rget $ (procedure @'[ 'Out, 'In ] elemOI) :& RNil
  where
    elemOI = \arg2 -> do
      -- solution: x[] x[0] x[0,0] x[1] x[1,1] xs[1,0] ~arg2[] ~arg2[0] ~arg2[0,0] ~arg2[1] ~arg2[1,0] ~xs[1,1]
      -- cost: 2
      (x) <- (do
        (x:_) <- pure arg2
        pure (x)
       ) <|> (do
        (_:xs) <- pure arg2
        (OneTuple (x)) <- elemOI xs
        pure (x)
       )
      pure (OneTuple (x))
    
{- span/4
span p arg2 arg3 arg4 :- ((arg2 = [], arg3 = [], arg4 = []); (arg2 = x0:xs1, x0 = x, xs1 = xs, if (p x) then (span p xs yt zs, ys = x2:yt, x2 = x) else (ys = [], zs = x3:xs4, x3 = x, xs4 = xs), arg3 = ys, arg4 = zs)).
constraints:
~p[]
~p[1,3,1]
~x[1,3,0,0]
~x[1,3,1,2]
~x[1,3,2]
~(arg2[1,0] & x0[1,0])
~(arg3[1,4] & ys[1,4])
~(arg4[1,5] & zs[1,5])
~(x[1,1] & x[1,3])
~(x0[1,0] & x0[1,1])
~(x0[1,1] & x[1,1])
~(x2[1,3,1,1] & x2[1,3,1,2])
~(x2[1,3,1,2] & x[1,3,1,2])
~(x3[1,3,2,1] & x3[1,3,2,2])
~(x3[1,3,2,2] & x[1,3,2,2])
~(xs[1,2] & xs[1,3])
~(xs1[1,0] & xs1[1,2])
~(xs1[1,2] & xs[1,2])
~(xs4[1,3,2,1] & xs4[1,3,2,3])
~(xs4[1,3,2,3] & xs[1,3,2,3])
~(ys[1,3] & ys[1,4])
~(ys[1,3,1,1] & x2[1,3,1,1])
~(yt[1,3,1,0] & yt[1,3,1,1])
~(zs[1,3] & zs[1,5])
~(zs[1,3,2,1] & x3[1,3,2,1])
(x[1,1] | x[1,3])
(x0[1,0] | x0[1,1])
(x2[1,3,1,1] | x2[1,3,1,2])
(x3[1,3,2,1] | x3[1,3,2,2])
(xs[1,2] | xs[1,3])
(xs1[1,0] | xs1[1,2])
(xs4[1,3,2,1] | xs4[1,3,2,3])
(ys[1,3] | ys[1,4])
(yt[1,3,1,0] | yt[1,3,1,1])
(zs[1,3] | zs[1,5])
(arg2[] <-> arg2[0])
(arg2[] <-> arg2[1])
(arg2[0] <-> arg2[0,0])
(arg2[1] <-> arg2[1,0])
(arg3[] <-> arg3[0])
(arg3[] <-> arg3[1])
(arg3[0] <-> arg3[0,1])
(arg3[1] <-> arg3[1,4])
(arg4[] <-> arg4[0])
(arg4[] <-> arg4[1])
(arg4[0] <-> arg4[0,2])
(arg4[1] <-> arg4[1,5])
(p[] <-> p[1])
(p[1] <-> p[1,3])
(p[1,3] <-> p[1,3,1])
(p[1,3,1] <-> p[1,3,1,0])
(p[1,3,1,0] <-> p[])
(x[1,3] <-> x[1,3,2])
(x[1,3,0,0] <-> p(1))
(x[1,3,2] <-> x[1,3,2,2])
(x0[1,0] <-> xs1[1,0])
(x2[1,3,1,1] <-> yt[1,3,1,1])
(x3[1,3,2,1] <-> xs4[1,3,2,1])
(xs[1,3] <-> (xs[1,3,1] | xs[1,3,2]))
(xs[1,3,1] <-> xs[1,3,1,0])
(xs[1,3,1] <-> xs[1,3,2])
(xs[1,3,1,0] <-> arg2[])
(xs[1,3,2] <-> xs[1,3,2,3])
(ys[1,3] <-> (ys[1,3,1] | ys[1,3,2]))
(ys[1,3,1] <-> ys[1,3,1,1])
(ys[1,3,1] <-> ys[1,3,2])
(ys[1,3,2] <-> ys[1,3,2,0])
(yt[1,3,1,0] <-> arg3[])
(zs[1,3] <-> (zs[1,3,1] | zs[1,3,2]))
(zs[1,3,1] <-> zs[1,3,1,0])
(zs[1,3,1] <-> zs[1,3,2])
(zs[1,3,1,0] <-> arg4[])
(zs[1,3,2] <-> zs[1,3,2,1])
1
-}

span = rget $ (procedure @'[ 'PredMode '[ 'In ], 'In, 'In, 'In ] spanP1IIII) :& (procedure @'[ 'PredMode '[ 'In ], 'In, 'In, 'Out ] spanP1IIIO) :& (procedure @'[ 'PredMode '[ 'In ], 'In, 'Out, 'In ] spanP1IIOI) :& (procedure @'[ 'PredMode '[ 'In ], 'In, 'Out, 'Out ] spanP1IIOO) :& RNil
  where
    spanP1IIII = \p arg2 arg3 arg4 -> Logic.once $ do
      -- solution: x[1,1] x0[1,0] x2[1,3,1,1] x3[1,3,2,1] xs[1,2] xs1[1,0] xs4[1,3,2,1] ys[1,4] yt[1,3,1,1] zs[1,5] ~arg2[] ~arg2[0] ~arg2[0,0] ~arg2[1] ~arg2[1,0] ~arg3[] ~arg3[0] ~arg3[0,1] ~arg3[1] ~arg3[1,4] ~arg4[] ~arg4[0] ~arg4[0,2] ~arg4[1] ~arg4[1,5] ~p[] ~p[1] ~p[1,3] ~p[1,3,1] ~p[1,3,1,0] ~x[1,3] ~x[1,3,0,0] ~x[1,3,1,2] ~x[1,3,2] ~x[1,3,2,2] ~x0[1,1] ~x2[1,3,1,2] ~x3[1,3,2,2] ~xs[1,3] ~xs[1,3,1] ~xs[1,3,1,0] ~xs[1,3,2] ~xs[1,3,2,3] ~xs1[1,2] ~xs4[1,3,2,3] ~ys[1,3] ~ys[1,3,1] ~ys[1,3,1,1] ~ys[1,3,2] ~ys[1,3,2,0] ~yt[1,3,1,0] ~zs[1,3] ~zs[1,3,1] ~zs[1,3,1,0] ~zs[1,3,2] ~zs[1,3,2,1] ~p(1)
      -- cost: 2
      () <- (do
        guard $ arg2 == []
        guard $ arg3 == []
        guard $ arg4 == []
        pure ()
       ) <|> (do
        ys <- pure arg3
        zs <- pure arg4
        (x0:xs1) <- pure arg2
        x <- pure x0
        xs <- pure xs1
        () <- Logic.ifte ((do
          () <- runProcedure p x
          pure ()
         )) (\() -> (do
          (x2:yt) <- pure ys
          guard $ x2 == x
          () <- spanP1IIII p xs yt zs
          pure ()
         )) ((do
          (x3:xs4) <- pure zs
          guard $ x3 == x
          guard $ xs4 == xs
          guard $ ys == []
          pure ()
         ))
        pure ()
       )
      pure ()
    
    spanP1IIIO = \p arg2 arg3 -> do
      -- solution: arg4[] arg4[0] arg4[0,2] arg4[1] arg4[1,5] x[1,1] x0[1,0] x2[1,3,1,1] x3[1,3,2,2] xs[1,2] xs1[1,0] xs4[1,3,2,3] ys[1,4] yt[1,3,1,1] zs[1,3] zs[1,3,1] zs[1,3,1,0] zs[1,3,2] zs[1,3,2,1] ~arg2[] ~arg2[0] ~arg2[0,0] ~arg2[1] ~arg2[1,0] ~arg3[] ~arg3[0] ~arg3[0,1] ~arg3[1] ~arg3[1,4] ~p[] ~p[1] ~p[1,3] ~p[1,3,1] ~p[1,3,1,0] ~x[1,3] ~x[1,3,0,0] ~x[1,3,1,2] ~x[1,3,2] ~x[1,3,2,2] ~x0[1,1] ~x2[1,3,1,2] ~x3[1,3,2,1] ~xs[1,3] ~xs[1,3,1] ~xs[1,3,1,0] ~xs[1,3,2] ~xs[1,3,2,3] ~xs1[1,2] ~xs4[1,3,2,1] ~ys[1,3] ~ys[1,3,1] ~ys[1,3,1,1] ~ys[1,3,2] ~ys[1,3,2,0] ~yt[1,3,1,0] ~zs[1,5] ~p(1)
      -- cost: 3
      (arg4) <- (do
        guard $ arg2 == []
        guard $ arg3 == []
        arg4 <- pure []
        pure (arg4)
       ) <|> (do
        ys <- pure arg3
        (x0:xs1) <- pure arg2
        x <- pure x0
        xs <- pure xs1
        (zs) <- Logic.ifte ((do
          () <- runProcedure p x
          pure ()
         )) (\() -> (do
          (x2:yt) <- pure ys
          guard $ x2 == x
          (OneTuple (zs)) <- spanP1IIIO p xs yt
          pure (zs)
         )) ((do
          x3 <- pure x
          xs4 <- pure xs
          zs <- pure (x3:xs4)
          guard $ ys == []
          pure (zs)
         ))
        arg4 <- pure zs
        pure (arg4)
       )
      pure (OneTuple (arg4))
    
    spanP1IIOI = \p arg2 arg4 -> do
      -- solution: arg3[] arg3[0] arg3[0,1] arg3[1] arg3[1,4] x[1,1] x0[1,0] x2[1,3,1,2] x3[1,3,2,1] xs[1,2] xs1[1,0] xs4[1,3,2,1] ys[1,3] ys[1,3,1] ys[1,3,1,1] ys[1,3,2] ys[1,3,2,0] yt[1,3,1,0] zs[1,5] ~arg2[] ~arg2[0] ~arg2[0,0] ~arg2[1] ~arg2[1,0] ~arg4[] ~arg4[0] ~arg4[0,2] ~arg4[1] ~arg4[1,5] ~p[] ~p[1] ~p[1,3] ~p[1,3,1] ~p[1,3,1,0] ~x[1,3] ~x[1,3,0,0] ~x[1,3,1,2] ~x[1,3,2] ~x[1,3,2,2] ~x0[1,1] ~x2[1,3,1,1] ~x3[1,3,2,2] ~xs[1,3] ~xs[1,3,1] ~xs[1,3,1,0] ~xs[1,3,2] ~xs[1,3,2,3] ~xs1[1,2] ~xs4[1,3,2,3] ~ys[1,4] ~yt[1,3,1,1] ~zs[1,3] ~zs[1,3,1] ~zs[1,3,1,0] ~zs[1,3,2] ~zs[1,3,2,1] ~p(1)
      -- cost: 3
      (arg3) <- (do
        guard $ arg2 == []
        arg3 <- pure []
        guard $ arg4 == []
        pure (arg3)
       ) <|> (do
        zs <- pure arg4
        (x0:xs1) <- pure arg2
        x <- pure x0
        xs <- pure xs1
        (ys) <- Logic.ifte ((do
          () <- runProcedure p x
          pure ()
         )) (\() -> (do
          x2 <- pure x
          (OneTuple (yt)) <- spanP1IIOI p xs zs
          ys <- pure (x2:yt)
          pure (ys)
         )) ((do
          (x3:xs4) <- pure zs
          guard $ x3 == x
          guard $ xs4 == xs
          ys <- pure []
          pure (ys)
         ))
        arg3 <- pure ys
        pure (arg3)
       )
      pure (OneTuple (arg3))
    
    spanP1IIOO = \p arg2 -> do
      -- solution: arg3[] arg3[0] arg3[0,1] arg3[1] arg3[1,4] arg4[] arg4[0] arg4[0,2] arg4[1] arg4[1,5] x[1,1] x0[1,0] x2[1,3,1,2] x3[1,3,2,2] xs[1,2] xs1[1,0] xs4[1,3,2,3] ys[1,3] ys[1,3,1] ys[1,3,1,1] ys[1,3,2] ys[1,3,2,0] yt[1,3,1,0] zs[1,3] zs[1,3,1] zs[1,3,1,0] zs[1,3,2] zs[1,3,2,1] ~arg2[] ~arg2[0] ~arg2[0,0] ~arg2[1] ~arg2[1,0] ~p[] ~p[1] ~p[1,3] ~p[1,3,1] ~p[1,3,1,0] ~x[1,3] ~x[1,3,0,0] ~x[1,3,1,2] ~x[1,3,2] ~x[1,3,2,2] ~x0[1,1] ~x2[1,3,1,1] ~x3[1,3,2,1] ~xs[1,3] ~xs[1,3,1] ~xs[1,3,1,0] ~xs[1,3,2] ~xs[1,3,2,3] ~xs1[1,2] ~xs4[1,3,2,1] ~ys[1,4] ~yt[1,3,1,1] ~zs[1,5] ~p(1)
      -- cost: 4
      (arg3,arg4) <- (do
        guard $ arg2 == []
        arg3 <- pure []
        arg4 <- pure []
        pure (arg3,arg4)
       ) <|> (do
        (x0:xs1) <- pure arg2
        x <- pure x0
        xs <- pure xs1
        (ys,zs) <- Logic.ifte ((do
          () <- runProcedure p x
          pure ()
         )) (\() -> (do
          x2 <- pure x
          (yt,zs) <- spanP1IIOO p xs
          ys <- pure (x2:yt)
          pure (ys,zs)
         )) ((do
          x3 <- pure x
          xs4 <- pure xs
          zs <- pure (x3:xs4)
          ys <- pure []
          pure (ys,zs)
         ))
        arg3 <- pure ys
        arg4 <- pure zs
        pure (arg3,arg4)
       )
      pure (arg3,arg4)
    
{- reverseDL/3
reverseDL arg1 arg2 arg3 :- ((arg1 = [], arg2 = xs, arg3 = xs); (arg1 = h0:t, h0 = h, reverseDL t data0 r, data0 = h1:rest, h1 = h, arg2 = rest, arg3 = r)).
constraints:
~(arg1[1,0] & h0[1,0])
~(arg2[0,1] & xs[0,1])
~(arg2[1,5] & rest[1,5])
~(arg3[0,2] & xs[0,2])
~(arg3[1,6] & r[1,6])
~(data0[1,2] & data0[1,3])
~(data0[1,3] & h1[1,3])
~(h[1,1] & h[1,4])
~(h0[1,0] & h0[1,1])
~(h0[1,1] & h[1,1])
~(h1[1,3] & h1[1,4])
~(h1[1,4] & h[1,4])
~(r[1,2] & r[1,6])
~(rest[1,3] & rest[1,5])
~(t[1,0] & t[1,2])
~(xs[0,1] & xs[0,2])
(data0[1,2] | data0[1,3])
(h[1,1] | h[1,4])
(h0[1,0] | h0[1,1])
(h1[1,3] | h1[1,4])
(r[1,2] | r[1,6])
(rest[1,3] | rest[1,5])
(t[1,0] | t[1,2])
(xs[0,1] | xs[0,2])
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg1[0] <-> arg1[0,0])
(arg1[1] <-> arg1[1,0])
(arg2[] <-> arg2[0])
(arg2[] <-> arg2[1])
(arg2[0] <-> arg2[0,1])
(arg2[1] <-> arg2[1,5])
(arg3[] <-> arg3[0])
(arg3[] <-> arg3[1])
(arg3[0] <-> arg3[0,2])
(arg3[1] <-> arg3[1,6])
(data0[1,2] <-> arg2[])
(h0[1,0] <-> t[1,0])
(h1[1,3] <-> rest[1,3])
(r[1,2] <-> arg3[])
(t[1,2] <-> arg1[])
1
-}

reverseDL = rget $ (procedure @'[ 'In, 'In, 'In ] reverseDLIII) :& (procedure @'[ 'In, 'In, 'Out ] reverseDLIIO) :& (procedure @'[ 'In, 'Out, 'In ] reverseDLIOI) :& (procedure @'[ 'Out, 'Out, 'In ] reverseDLOOI) :& RNil
  where
    reverseDLIII = \arg1 arg2 arg3 -> Logic.once $ do
      -- solution: data0[1,3] h[1,1] h0[1,0] h1[1,4] r[1,6] rest[1,5] t[1,0] xs[0,1] ~arg1[] ~arg1[0] ~arg1[0,0] ~arg1[1] ~arg1[1,0] ~arg2[] ~arg2[0] ~arg2[0,1] ~arg2[1] ~arg2[1,5] ~arg3[] ~arg3[0] ~arg3[0,2] ~arg3[1] ~arg3[1,6] ~data0[1,2] ~h[1,4] ~h0[1,1] ~h1[1,3] ~r[1,2] ~rest[1,3] ~t[1,2] ~xs[0,2]
      -- cost: 1
      () <- (do
        xs <- pure arg2
        guard $ arg3 == xs
        guard $ arg1 == []
        pure ()
       ) <|> (do
        rest <- pure arg2
        r <- pure arg3
        (h0:t) <- pure arg1
        h <- pure h0
        h1 <- pure h
        data0 <- pure (h1:rest)
        () <- reverseDLIII t data0 r
        pure ()
       )
      pure ()
    
    reverseDLIIO = \arg1 arg2 -> do
      -- solution: arg3[] arg3[0] arg3[0,2] arg3[1] arg3[1,6] data0[1,3] h[1,1] h0[1,0] h1[1,4] r[1,2] rest[1,5] t[1,0] xs[0,1] ~arg1[] ~arg1[0] ~arg1[0,0] ~arg1[1] ~arg1[1,0] ~arg2[] ~arg2[0] ~arg2[0,1] ~arg2[1] ~arg2[1,5] ~data0[1,2] ~h[1,4] ~h0[1,1] ~h1[1,3] ~r[1,6] ~rest[1,3] ~t[1,2] ~xs[0,2]
      -- cost: 2
      (arg3) <- (do
        xs <- pure arg2
        arg3 <- pure xs
        guard $ arg1 == []
        pure (arg3)
       ) <|> (do
        rest <- pure arg2
        (h0:t) <- pure arg1
        h <- pure h0
        h1 <- pure h
        data0 <- pure (h1:rest)
        (OneTuple (r)) <- reverseDLIIO t data0
        arg3 <- pure r
        pure (arg3)
       )
      pure (OneTuple (arg3))
    
    reverseDLIOI = \arg1 arg3 -> do
      -- solution: arg2[] arg2[0] arg2[0,1] arg2[1] arg2[1,5] data0[1,2] h[1,1] h0[1,0] h1[1,3] r[1,6] rest[1,3] t[1,0] xs[0,2] ~arg1[] ~arg1[0] ~arg1[0,0] ~arg1[1] ~arg1[1,0] ~arg3[] ~arg3[0] ~arg3[0,2] ~arg3[1] ~arg3[1,6] ~data0[1,3] ~h[1,4] ~h0[1,1] ~h1[1,4] ~r[1,2] ~rest[1,5] ~t[1,2] ~xs[0,1]
      -- cost: 2
      (arg2) <- (do
        xs <- pure arg3
        arg2 <- pure xs
        guard $ arg1 == []
        pure (arg2)
       ) <|> (do
        r <- pure arg3
        (h0:t) <- pure arg1
        h <- pure h0
        (OneTuple (data0)) <- reverseDLIOI t r
        (h1:rest) <- pure data0
        arg2 <- pure rest
        guard $ h1 == h
        pure (arg2)
       )
      pure (OneTuple (arg2))
    
    reverseDLOOI = \arg3 -> do
      -- solution: arg1[] arg1[0] arg1[0,0] arg1[1] arg1[1,0] arg2[] arg2[0] arg2[0,1] arg2[1] arg2[1,5] data0[1,2] h[1,4] h0[1,1] h1[1,3] r[1,6] rest[1,3] t[1,2] xs[0,2] ~arg3[] ~arg3[0] ~arg3[0,2] ~arg3[1] ~arg3[1,6] ~data0[1,3] ~h[1,1] ~h0[1,0] ~h1[1,4] ~r[1,2] ~rest[1,5] ~t[1,0] ~xs[0,1]
      -- cost: 3
      (arg1,arg2) <- (do
        xs <- pure arg3
        arg2 <- pure xs
        arg1 <- pure []
        pure (arg1,arg2)
       ) <|> (do
        r <- pure arg3
        (t,data0) <- reverseDLOOI r
        (h1:rest) <- pure data0
        arg2 <- pure rest
        h <- pure h1
        h0 <- pure h
        arg1 <- pure (h0:t)
        pure (arg1,arg2)
       )
      pure (arg1,arg2)
    
{- reverse/2
reverse s r :- ((reverseDL s data0 r, data0 = [])).
constraints:
~(data0[0,0] & data0[0,1])
(data0[0,0] | data0[0,1])
((s[0,0] & (data0[0,0] & ~r[0,0])) | ((~s[0,0] & (data0[0,0] & ~r[0,0])) | ((~s[0,0] & (~data0[0,0] & r[0,0])) | (~s[0,0] & (~data0[0,0] & ~r[0,0])))))
(r[] <-> r[0])
(r[0] <-> r[0,0])
(s[] <-> s[0])
(s[0] <-> s[0,0])
1
-}

reverse = rget $ (procedure @'[ 'In, 'In ] reverseII) :& (procedure @'[ 'In, 'Out ] reverseIO) :& (procedure @'[ 'Out, 'In ] reverseOI) :& RNil
  where
    reverseII = \s r -> Logic.once $ do
      -- solution: data0[0,1] ~data0[0,0] ~r[] ~r[0] ~r[0,0] ~s[] ~s[0] ~s[0,0]
      -- cost: 1
      () <- (do
        data0 <- pure []
        () <- runProcedure @'[ 'In, 'In, 'In ] reverseDL s data0 r
        pure ()
       )
      pure ()
    
    reverseIO = \s -> do
      -- solution: data0[0,1] r[] r[0] r[0,0] ~data0[0,0] ~s[] ~s[0] ~s[0,0]
      -- cost: 2
      (r) <- (do
        data0 <- pure []
        (OneTuple (r)) <- runProcedure @'[ 'In, 'In, 'Out ] reverseDL s data0
        pure (r)
       )
      pure (OneTuple (r))
    
    reverseOI = \r -> do
      -- solution: data0[0,0] s[] s[0] s[0,0] ~data0[0,1] ~r[] ~r[0] ~r[0,0]
      -- cost: 3
      (s) <- (do
        (s,data0) <- runProcedure @'[ 'Out, 'Out, 'In ] reverseDL r
        guard $ data0 == []
        pure (s)
       )
      pure (OneTuple (s))
    
{- all/2
all p arg2 :- ((arg2 = []); (arg2 = h:t, if (p h) then (all p t) else (empty))).
constraints:
~h[1,1]
~h[1,1,0,0]
~p[]
~p[1,1,1]
~t[1,1,1]
~(arg2[1,0] & h[1,0])
~(h[1,0] & h[1,1])
~(t[1,0] & t[1,1])
(h[1,0] | h[1,1])
(t[1,0] | t[1,1])
(arg2[] <-> arg2[0])
(arg2[] <-> arg2[1])
(arg2[0] <-> arg2[0,0])
(arg2[1] <-> arg2[1,0])
(h[1,0] <-> t[1,0])
(h[1,1,0,0] <-> p(1))
(p[] <-> p[1])
(p[1] <-> p[1,1])
(p[1,1] <-> p[1,1,1])
(p[1,1,1] <-> p[1,1,1,0])
(p[1,1,1,0] <-> p[])
(t[1,1] <-> t[1,1,1])
(t[1,1,1] <-> t[1,1,1,0])
(t[1,1,1,0] <-> arg2[])
1
-}

all = rget $ (procedure @'[ 'PredMode '[ 'In ], 'In ] allP1II) :& RNil
  where
    allP1II = \p arg2 -> Logic.once $ do
      -- solution: h[1,0] t[1,0] ~arg2[] ~arg2[0] ~arg2[0,0] ~arg2[1] ~arg2[1,0] ~h[1,1] ~h[1,1,0,0] ~p[] ~p[1] ~p[1,1] ~p[1,1,1] ~p[1,1,1,0] ~t[1,1] ~t[1,1,1] ~t[1,1,1,0] ~p(1)
      -- cost: 3
      () <- (do
        guard $ arg2 == []
        pure ()
       ) <|> (do
        (h:t) <- pure arg2
        () <- Logic.ifte ((do
          () <- runProcedure p h
          pure ()
         )) (\() -> (do
          () <- allP1II p t
          pure ()
         )) ((do
          () <- empty 
          pure ()
         ))
        pure ()
       )
      pure ()
    
{- multiple/2
multiple x y :- ((mod x y data0, data0 = 0)).
constraints:
~(data0[0,0] & data0[0,1])
(data0[0,0] | data0[0,1])
((~x[0,0] & (~y[0,0] & data0[0,0])) | (~x[0,0] & (~y[0,0] & ~data0[0,0])))
(x[] <-> x[0])
(x[0] <-> x[0,0])
(y[] <-> y[0])
(y[0] <-> y[0,0])
1
-}

multiple = rget $ (procedure @'[ 'In, 'In ] multipleII) :& RNil
  where
    multipleII = \x y -> Logic.once $ do
      -- solution: data0[0,1] ~data0[0,0] ~x[] ~x[0] ~x[0,0] ~y[] ~y[0] ~y[0,0]
      -- cost: 1
      () <- (do
        data0 <- pure 0
        () <- runProcedure @'[ 'In, 'In, 'In ] mod x y data0
        pure ()
       )
      pure ()
    
{- euler1/1
euler1 x :- ((elem x data2, data0 = 0, data1 = 999, data2 = .. data0 data1, multiple x y, ((y = 3); (y = 5)))).
constraints:
~(data0[0,1] & data0[0,3])
~(data1[0,2] & data1[0,3])
~(data2[0,0] & data2[0,3])
~(data2[0,3] & data0[0,3])
~(x[0,0] & x[0,4])
~(y[0,4] & y[0,5])
(x[0,0] & ~data2[0,0])
(~x[0,4] & ~y[0,4])
(data0[0,1] | data0[0,3])
(data1[0,2] | data1[0,3])
(data2[0,0] | data2[0,3])
(y[0,4] | y[0,5])
(data0[0,3] <-> data1[0,3])
(x[] <-> x[0])
(x[0] <-> (x[0,0] | x[0,4]))
(y[0,5] <-> y[0,5,0])
(y[0,5] <-> y[0,5,1])
(y[0,5,0] <-> y[0,5,0,0])
(y[0,5,1] <-> y[0,5,1,0])
1
-}

euler1 = rget $ (procedure @'[ 'Out ] euler1O) :& RNil
  where
    euler1O = choose . nub . Logic.observeAll $ do
      -- solution: data0[0,1] data1[0,2] data2[0,3] x[] x[0] x[0,0] y[0,5] y[0,5,0] y[0,5,0,0] y[0,5,1] y[0,5,1,0] ~data0[0,3] ~data1[0,3] ~data2[0,0] ~x[0,4] ~y[0,4]
      -- cost: 3
      (x) <- (do
        data0 <- pure 0
        data1 <- pure 999
        data2 <- pure [data0..data1]
        (y) <- (do
          y <- pure 3
          pure (y)
         ) <|> (do
          y <- pure 5
          pure (y)
         )
        (OneTuple (x)) <- runProcedure @'[ 'Out, 'In ] elem data2
        () <- runProcedure @'[ 'In, 'In ] multiple x y
        pure (x)
       )
      pure (OneTuple (x))
    
{- euler1'/1
euler1' s :- ((observeAll pred0 r, (pred0 curry1 :- (euler1 curry1)), sum r s)).
constraints:
curry1[0,1,0,0]
~curry1[0]
~pred0[0,0]
~(r[0,0] & r[0,2])
(~pred0[0,0] & (pred0(1) & r[0,0]))
(r[0,0] | r[0,2])
((~r[0,2] & s[0,2]) | (~r[0,2] & ~s[0,2]))
(curry1[0,1,0] <-> curry1[0,1,0,0])
(s[] <-> s[0])
(s[0] <-> s[0,2])
(pred0(1) <-> curry1[0,1,0])
1
-}

euler1' = rget $ (procedure @'[ 'In ] euler1'I) :& (procedure @'[ 'Out ] euler1'O) :& RNil
  where
    euler1'I = \s -> Logic.once $ do
      -- solution: curry1[0,1,0] curry1[0,1,0,0] r[0,0] pred0(1) ~curry1[0] ~pred0[0,0] ~r[0,2] ~s[] ~s[0] ~s[0,2]
      -- cost: 5
      () <- (do
        let pred0 = procedure @'[ 'Out ] $
              do
                (curry1) <- (do
                  (OneTuple (curry1)) <- runProcedure @'[ 'Out ] euler1 
                  pure (curry1)
                 )
                pure (OneTuple (curry1))
        (OneTuple (r)) <- runProcedure @'[ 'PredMode '[ 'Out ], 'Out ] observeAll pred0
        () <- runProcedure @'[ 'In, 'In ] sum r s
        pure ()
       )
      pure ()
    
    euler1'O = do
      -- solution: curry1[0,1,0] curry1[0,1,0,0] r[0,0] s[] s[0] s[0,2] pred0(1) ~curry1[0] ~pred0[0,0] ~r[0,2]
      -- cost: 6
      (s) <- (do
        let pred0 = procedure @'[ 'Out ] $
              do
                (curry1) <- (do
                  (OneTuple (curry1)) <- runProcedure @'[ 'Out ] euler1 
                  pure (curry1)
                 )
                pure (OneTuple (curry1))
        (OneTuple (r)) <- runProcedure @'[ 'PredMode '[ 'Out ], 'Out ] observeAll pred0
        (OneTuple (s)) <- runProcedure @'[ 'In, 'Out ] sum r
        pure (s)
       )
      pure (OneTuple (s))
    
{- fib/2
fib arg1 arg2 :- ((arg1 = 0, arg2 = 0); (arg1 = 1, arg2 = 1); ((>) k data0, data0 = 1, succ i j, succ j k, fib i fi, fib j fj, plus fi fj fk, arg1 = k, arg2 = fk)).
constraints:
~(arg1[2,7] & k[2,7])
~(arg2[2,8] & fk[2,8])
~(data0[2,0] & data0[2,1])
~(fi[2,4] & fi[2,6])
~(fj[2,5] & fj[2,6])
~(fk[2,6] & fk[2,8])
~(i[2,2] & i[2,4])
~(j[2,2] & j[2,3])
~(j[2,2] & j[2,5])
~(j[2,3] & j[2,5])
~(k[2,0] & k[2,3])
~(k[2,0] & k[2,7])
~(k[2,3] & k[2,7])
(~k[2,0] & ~data0[2,0])
(data0[2,0] | data0[2,1])
(fi[2,4] | fi[2,6])
(fj[2,5] | fj[2,6])
(fk[2,6] | fk[2,8])
(i[2,2] | i[2,4])
(j[2,2] | (j[2,3] | j[2,5]))
(k[2,0] | (k[2,3] | k[2,7]))
((fi[2,6] & (~fj[2,6] & ~fk[2,6])) | ((~fi[2,6] & (fj[2,6] & ~fk[2,6])) | (~fi[2,6] & (~fj[2,6] & fk[2,6]))))
((i[2,2] & ~j[2,2]) | ((~i[2,2] & j[2,2]) | (~i[2,2] & ~j[2,2])))
((j[2,3] & ~k[2,3]) | ((~j[2,3] & k[2,3]) | (~j[2,3] & ~k[2,3])))
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg1[] <-> arg1[2])
(arg1[0] <-> arg1[0,0])
(arg1[1] <-> arg1[1,0])
(arg1[2] <-> arg1[2,7])
(arg2[] <-> arg2[0])
(arg2[] <-> arg2[1])
(arg2[] <-> arg2[2])
(arg2[0] <-> arg2[0,1])
(arg2[1] <-> arg2[1,1])
(arg2[2] <-> arg2[2,8])
(fi[2,4] <-> arg2[])
(fj[2,5] <-> arg2[])
(i[2,4] <-> arg1[])
(j[2,5] <-> arg1[])
1
-}

fib = rget $ (procedure @'[ 'In, 'Out ] fibIO) :& (procedure @'[ 'Out, 'Out ] fibOO) :& RNil
  where
    fibIO = memo $ \arg1 -> choose . Logic.observeAll $ do
      -- solution: arg2[] arg2[0] arg2[0,1] arg2[1] arg2[1,1] arg2[2] arg2[2,8] data0[2,1] fi[2,4] fj[2,5] fk[2,6] i[2,2] j[2,3] k[2,7] ~arg1[] ~arg1[0] ~arg1[0,0] ~arg1[1] ~arg1[1,0] ~arg1[2] ~arg1[2,7] ~data0[2,0] ~fi[2,6] ~fj[2,6] ~fk[2,8] ~i[2,4] ~j[2,2] ~j[2,5] ~k[2,0] ~k[2,3]
      -- cost: 11
      (arg2) <- (do
        guard $ arg1 == 0
        arg2 <- pure 0
        pure (arg2)
       ) <|> (do
        guard $ arg1 == 1
        arg2 <- pure 1
        pure (arg2)
       ) <|> (do
        k <- pure arg1
        data0 <- pure 1
        guard $ (>) k data0
        (OneTuple (j)) <- runProcedure @'[ 'Out, 'In ] succ k
        (OneTuple (fj)) <- fibIO j
        (OneTuple (i)) <- runProcedure @'[ 'Out, 'In ] succ j
        (OneTuple (fi)) <- fibIO i
        (OneTuple (fk)) <- runProcedure @'[ 'In, 'In, 'Out ] plus fi fj
        arg2 <- pure fk
        pure (arg2)
       )
      pure (OneTuple (arg2))
    
    fibOO = choose . Logic.observeAll $ do
      -- solution: arg1[] arg1[0] arg1[0,0] arg1[1] arg1[1,0] arg1[2] arg1[2,7] arg2[] arg2[0] arg2[0,1] arg2[1] arg2[1,1] arg2[2] arg2[2,8] data0[2,1] fi[2,4] fj[2,5] fk[2,6] i[2,4] j[2,5] k[2,3] ~data0[2,0] ~fi[2,6] ~fj[2,6] ~fk[2,8] ~i[2,2] ~j[2,2] ~j[2,3] ~k[2,0] ~k[2,7]
      -- cost: 12
      (arg1,arg2) <- (do
        arg1 <- pure 0
        arg2 <- pure 0
        pure (arg1,arg2)
       ) <|> (do
        arg1 <- pure 1
        arg2 <- pure 1
        pure (arg1,arg2)
       ) <|> (do
        data0 <- pure 1
        (i,fi) <- fibOO 
        (j,fj) <- fibOO 
        () <- runProcedure @'[ 'In, 'In ] succ i j
        (OneTuple (fk)) <- runProcedure @'[ 'In, 'In, 'Out ] plus fi fj
        arg2 <- pure fk
        (OneTuple (k)) <- runProcedure @'[ 'In, 'Out ] succ j
        arg1 <- pure k
        guard $ (>) k data0
        pure (arg1,arg2)
       )
      pure (arg1,arg2)
    
{- fib'/1
fib' f :- ((nat i, fib i f)).
constraints:
~(i[0,0] & i[0,1])
(i[0,0] | i[0,1])
(i[0,0] | ~i[0,0])
((i[0,1] & f[0,1]) | (~i[0,1] & f[0,1]))
(f[] <-> f[0])
(f[0] <-> f[0,1])
1
-}

fib' = rget $ (procedure @'[ 'Out ] fib'O) :& RNil
  where
    fib'O = do
      -- solution: f[] f[0] f[0,1] i[0,0] ~i[0,1]
      -- cost: 4
      (f) <- (do
        (OneTuple (i)) <- runProcedure @'[ 'Out ] nat 
        (OneTuple (f)) <- runProcedure @'[ 'In, 'Out ] fib i
        pure (f)
       )
      pure (OneTuple (f))
    
{- euler2/1
euler2 s :- ((observeAll pred0 fs, (pred0 x :- (fib' x, even x)), span pred2 fs xs _, data1 = 1000000, (pred2 x :- ((<) x data1, data1 = 1000000)), sum xs s)).
constraints:
data1[0,3]
x[0,1,0,0]
~pred0[0,0]
~pred2[0,2]
~x[0]
~x[0,1,0,1]
~(data1[0,4,0,0] & data1[0,4,0,1])
~(fs[0,0] & fs[0,2])
~(x[0,1,0,0] & x[0,1,0,1])
~(xs[0,2] & xs[0,5])
(~pred0[0,0] & (pred0(1) & fs[0,0]))
(~x[0,4,0,0] & ~data1[0,4,0,0])
(fs[0,0] | fs[0,2])
(xs[0,2] | xs[0,5])
((~pred2[0,2] & (~pred2(1) & (~fs[0,2] & xs[0,2]))) | (~pred2[0,2] & (~pred2(1) & (~fs[0,2] & ~xs[0,2]))))
((~xs[0,5] & s[0,5]) | (~xs[0,5] & ~s[0,5]))
(data1[0,4,0] <-> (data1[0,4,0,0] | data1[0,4,0,1]))
(s[] <-> s[0])
(s[0] <-> s[0,5])
(x[0,1,0] <-> (x[0,1,0,0] | x[0,1,0,1]))
(x[0,4,0] <-> x[0,4,0,0])
(pred0(1) <-> x[0,1,0])
(pred2(1) <-> x[0,4,0])
1
-}

euler2 = rget $ (procedure @'[ 'In ] euler2I) :& (procedure @'[ 'Out ] euler2O) :& RNil
  where
    euler2I = \s -> Logic.once $ do
      -- solution: data1[0,3] data1[0,4,0] data1[0,4,0,1] fs[0,0] x[0,1,0] x[0,1,0,0] xs[0,2] pred0(1) ~data1[0,4,0,0] ~fs[0,2] ~pred0[0,0] ~pred2[0,2] ~s[] ~s[0] ~s[0,5] ~x[0] ~x[0,1,0,1] ~x[0,4,0] ~x[0,4,0,0] ~xs[0,5] ~pred2(1)
      -- cost: 10
      () <- (do
        data1 <- pure 1000000
        let pred0 = procedure @'[ 'Out ] $
              do
                (x) <- (do
                  (OneTuple (x)) <- runProcedure @'[ 'Out ] fib' 
                  () <- runProcedure @'[ 'In ] even x
                  pure (x)
                 )
                pure (OneTuple (x))
        let pred2 = procedure @'[ 'In ] $
              \x -> do
                (data1) <- (do
                  data1 <- pure 1000000
                  guard $ (<) x data1
                  pure (data1)
                 )
                pure ()
        (OneTuple (fs)) <- runProcedure @'[ 'PredMode '[ 'Out ], 'Out ] observeAll pred0
        (xs,_) <- runProcedure @'[ 'PredMode '[ 'In ], 'In, 'Out, 'Out ] span pred2 fs
        () <- runProcedure @'[ 'In, 'In ] sum xs s
        pure ()
       )
      pure ()
    
    euler2O = do
      -- solution: data1[0,3] data1[0,4,0] data1[0,4,0,1] fs[0,0] s[] s[0] s[0,5] x[0,1,0] x[0,1,0,0] xs[0,2] pred0(1) ~data1[0,4,0,0] ~fs[0,2] ~pred0[0,0] ~pred2[0,2] ~x[0] ~x[0,1,0,1] ~x[0,4,0] ~x[0,4,0,0] ~xs[0,5] ~pred2(1)
      -- cost: 11
      (s) <- (do
        data1 <- pure 1000000
        let pred0 = procedure @'[ 'Out ] $
              do
                (x) <- (do
                  (OneTuple (x)) <- runProcedure @'[ 'Out ] fib' 
                  () <- runProcedure @'[ 'In ] even x
                  pure (x)
                 )
                pure (OneTuple (x))
        let pred2 = procedure @'[ 'In ] $
              \x -> do
                (data1) <- (do
                  data1 <- pure 1000000
                  guard $ (<) x data1
                  pure (data1)
                 )
                pure ()
        (OneTuple (fs)) <- runProcedure @'[ 'PredMode '[ 'Out ], 'Out ] observeAll pred0
        (xs,_) <- runProcedure @'[ 'PredMode '[ 'In ], 'In, 'Out, 'Out ] span pred2 fs
        (OneTuple (s)) <- runProcedure @'[ 'In, 'Out ] sum xs
        pure (s)
       )
      pure (OneTuple (s))
    
{- nontrivialDivisor/2
nontrivialDivisor n d :- ((succ n' n, elem d data1, data0 = 2, data1 = .. data0 n', mod n d data2, data2 = 0)).
constraints:
~(d[0,1] & d[0,4])
~(data0[0,2] & data0[0,3])
~(data1[0,1] & data1[0,3])
~(data1[0,3] & data0[0,3])
~(data2[0,4] & data2[0,5])
~(n[0,0] & n[0,4])
~(n'[0,0] & n'[0,3])
(d[0,1] & ~data1[0,1])
(data0[0,2] | data0[0,3])
(data1[0,1] | data1[0,3])
(data2[0,4] | data2[0,5])
(n'[0,0] | n'[0,3])
((n'[0,0] & ~n[0,0]) | ((~n'[0,0] & n[0,0]) | (~n'[0,0] & ~n[0,0])))
((~n[0,4] & (~d[0,4] & data2[0,4])) | (~n[0,4] & (~d[0,4] & ~data2[0,4])))
(d[] <-> d[0])
(d[0] <-> (d[0,1] | d[0,4]))
(data0[0,3] <-> n'[0,3])
(n[] <-> n[0])
(n[0] <-> (n[0,0] | n[0,4]))
1
-}

nontrivialDivisor = rget $ (procedure @'[ 'In, 'Out ] nontrivialDivisorIO) :& RNil
  where
    nontrivialDivisorIO = \n -> do
      -- solution: d[] d[0] d[0,1] data0[0,2] data1[0,3] data2[0,5] n'[0,0] ~d[0,4] ~data0[0,3] ~data1[0,1] ~data2[0,4] ~n[] ~n[0] ~n[0,0] ~n[0,4] ~n'[0,3]
      -- cost: 5
      (d) <- (do
        data2 <- pure 0
        data0 <- pure 2
        (OneTuple (n')) <- runProcedure @'[ 'Out, 'In ] succ n
        data1 <- pure [data0..n']
        (OneTuple (d)) <- runProcedure @'[ 'Out, 'In ] elem data1
        () <- runProcedure @'[ 'In, 'In, 'In ] mod n d data2
        pure (d)
       )
      pure (OneTuple (d))
    
{- primeSlow/1
primeSlow n :- ((nat n, (>) n data0, data0 = 1, if (nontrivialDivisor n _) then (empty) else ())).
constraints:
_[0,3]
~n[0,3]
~n[0,3,0,0]
~(data0[0,1] & data0[0,2])
~(n[0,0] & n[0,1])
~(n[0,0] & n[0,3])
~(n[0,1] & n[0,3])
(~n[0,1] & ~data0[0,1])
(data0[0,1] | data0[0,2])
(n[0,0] | ~n[0,0])
(_[0] <-> _[0,3])
(n[] <-> n[0])
(n[0] <-> (n[0,0] | (n[0,1] | n[0,3])))
1
-}

primeSlow = rget $ (procedure @'[ 'In ] primeSlowI) :& (procedure @'[ 'Out ] primeSlowO) :& RNil
  where
    primeSlowI = \n -> Logic.once $ do
      -- solution: _[0] _[0,3] data0[0,2] ~data0[0,1] ~n[] ~n[0] ~n[0,0] ~n[0,1] ~n[0,3] ~n[0,3,0,0]
      -- cost: 5
      () <- (do
        data0 <- pure 1
        guard $ (>) n data0
        () <- runProcedure @'[ 'In ] nat n
        () <- Logic.ifte ((do
          (OneTuple (_)) <- runProcedure @'[ 'In, 'Out ] nontrivialDivisor n
          pure ()
         )) (\() -> (do
          () <- empty 
          pure ()
         )) ((do
          
          pure ()
         ))
        pure ()
       )
      pure ()
    
    primeSlowO = do
      -- solution: _[0] _[0,3] data0[0,2] n[] n[0] n[0,0] ~data0[0,1] ~n[0,1] ~n[0,3] ~n[0,3,0,0]
      -- cost: 6
      (n) <- (do
        data0 <- pure 1
        (OneTuple (n)) <- runProcedure @'[ 'Out ] nat 
        guard $ (>) n data0
        () <- Logic.ifte ((do
          (OneTuple (_)) <- runProcedure @'[ 'In, 'Out ] nontrivialDivisor n
          pure ()
         )) (\() -> (do
          () <- empty 
          pure ()
         )) ((do
          
          pure ()
         ))
        pure (n)
       )
      pure (OneTuple (n))
    
{- factor/3
factor arg1 n f :- ((arg1 = p0:ps1, p0 = p, ps1 = ps, if (timesInt p2 p3 pp, p2 = p, p3 = p, (>) pp n) then (f = n) else (if (divMod n p d data0, data0 = 0) then (((f = p); (factor data1 d f, data1 = p4:ps5, p4 = p, ps5 = ps))) else (factor ps n f)))).
constraints:
d[0,3,2,0,0]
data0[0,3,2,0]
p2[0,3]
p3[0,3]
pp[0,3]
~d[0,3,2,0,1,0]
~n[0,3,0,3]
~n[0,3,1,0]
~n[0,3,2]
~n[0,3,2,0,0,0]
~n[0,3,2,0,2]
~p[0,3,2]
~p[0,3,2,0]
~p[0,3,2,0,0,0]
~p[0,3,2,0,1,0]
~ps[0,3,2]
~ps[0,3,2,0,1,0]
~(arg1[0,0] & p0[0,0])
~(data0[0,3,2,0,0,0] & data0[0,3,2,0,0,1])
~(data1[0,3,2,0,1,0,1,0] & data1[0,3,2,0,1,0,1,1])
~(data1[0,3,2,0,1,0,1,1] & p4[0,3,2,0,1,0,1,1])
~(f[0,3,1,0] & n[0,3,1,0])
~(f[0,3,2,0,1,0,0,0] & p[0,3,2,0,1,0,0,0])
~(p[0,1] & p[0,3])
~(p[0,3,0,1] & p[0,3,0,2])
~(p0[0,0] & p0[0,1])
~(p0[0,1] & p[0,1])
~(p2[0,3,0,0] & p2[0,3,0,1])
~(p2[0,3,0,1] & p[0,3,0,1])
~(p3[0,3,0,0] & p3[0,3,0,2])
~(p3[0,3,0,2] & p[0,3,0,2])
~(p4[0,3,2,0,1,0,1,1] & p4[0,3,2,0,1,0,1,2])
~(p4[0,3,2,0,1,0,1,2] & p[0,3,2,0,1,0,1,2])
~(pp[0,3,0,0] & pp[0,3,0,3])
~(ps[0,2] & ps[0,3])
~(ps1[0,0] & ps1[0,2])
~(ps1[0,2] & ps[0,2])
~(ps5[0,3,2,0,1,0,1,1] & ps5[0,3,2,0,1,0,1,3])
~(ps5[0,3,2,0,1,0,1,3] & ps[0,3,2,0,1,0,1,3])
~(p[0,3,0,1] | p[0,3,0,2])
(~pp[0,3,0,3] & ~n[0,3,0,3])
(data0[0,3,2,0,0,0] | data0[0,3,2,0,0,1])
(data1[0,3,2,0,1,0,1,0] | data1[0,3,2,0,1,0,1,1])
(p[0,1] | p[0,3])
(p0[0,0] | p0[0,1])
(p2[0,3,0,0] | p2[0,3,0,1])
(p3[0,3,0,0] | p3[0,3,0,2])
(p4[0,3,2,0,1,0,1,1] | p4[0,3,2,0,1,0,1,2])
(pp[0,3,0,0] | pp[0,3,0,3])
(ps[0,2] | ps[0,3])
(ps1[0,0] | ps1[0,2])
(ps5[0,3,2,0,1,0,1,1] | ps5[0,3,2,0,1,0,1,3])
((p2[0,3,0,0] & (~p3[0,3,0,0] & ~pp[0,3,0,0])) | ((~p2[0,3,0,0] & (p3[0,3,0,0] & ~pp[0,3,0,0])) | (~p2[0,3,0,0] & (~p3[0,3,0,0] & pp[0,3,0,0]))))
((~n[0,3,2,0,0,0] & (~p[0,3,2,0,0,0] & (d[0,3,2,0,0,0] & data0[0,3,2,0,0,0]))) | ((~n[0,3,2,0,0,0] & (~p[0,3,2,0,0,0] & (d[0,3,2,0,0,0] & ~data0[0,3,2,0,0,0]))) | ((~n[0,3,2,0,0,0] & (~p[0,3,2,0,0,0] & (~d[0,3,2,0,0,0] & data0[0,3,2,0,0,0]))) | (~n[0,3,2,0,0,0] & (~p[0,3,2,0,0,0] & (~d[0,3,2,0,0,0] & ~data0[0,3,2,0,0,0]))))))
(arg1[] <-> arg1[0])
(arg1[0] <-> arg1[0,0])
(d[0,3,2,0,0] <-> d[0,3,2,0,0,0])
(d[0,3,2,0,1,0] <-> d[0,3,2,0,1,0,1])
(d[0,3,2,0,1,0,1] <-> d[0,3,2,0,1,0,1,0])
(d[0,3,2,0,1,0,1,0] <-> n[])
(data0[0] <-> data0[0,3])
(data0[0,3] <-> data0[0,3,2])
(data0[0,3,2] <-> data0[0,3,2,0])
(data1[0,3,2,0,1,0,1,0] <-> arg1[])
(f[] <-> f[0])
(f[0] <-> f[0,3])
(f[0,3] <-> (f[0,3,1] | f[0,3,2]))
(f[0,3,1] <-> f[0,3,1,0])
(f[0,3,1] <-> f[0,3,2])
(f[0,3,2] <-> f[0,3,2,0])
(f[0,3,2,0] <-> (f[0,3,2,0,1] | f[0,3,2,0,2]))
(f[0,3,2,0,1] <-> f[0,3,2,0,1,0])
(f[0,3,2,0,1] <-> f[0,3,2,0,2])
(f[0,3,2,0,1,0] <-> f[0,3,2,0,1,0,0])
(f[0,3,2,0,1,0] <-> f[0,3,2,0,1,0,1])
(f[0,3,2,0,1,0,0] <-> f[0,3,2,0,1,0,0,0])
(f[0,3,2,0,1,0,1] <-> f[0,3,2,0,1,0,1,0])
(f[0,3,2,0,1,0,1,0] <-> f[])
(f[0,3,2,0,2] <-> f[0,3,2,0,2,0])
(f[0,3,2,0,2,0] <-> f[])
(n[] <-> n[0])
(n[0] <-> n[0,3])
(n[0,3] <-> n[0,3,2])
(n[0,3,2] <-> n[0,3,2,0])
(n[0,3,2,0] <-> n[0,3,2,0,2])
(n[0,3,2,0,2] <-> n[0,3,2,0,2,0])
(n[0,3,2,0,2,0] <-> n[])
(p[0,3] <-> p[0,3,2])
(p[0,3,2] <-> p[0,3,2,0])
(p[0,3,2,0,1,0] <-> p[0,3,2,0,1,0,0])
(p[0,3,2,0,1,0] <-> p[0,3,2,0,1,0,1])
(p[0,3,2,0,1,0,0] <-> p[0,3,2,0,1,0,0,0])
(p[0,3,2,0,1,0,1] <-> p[0,3,2,0,1,0,1,2])
(p0[0,0] <-> ps1[0,0])
(p2[0] <-> p2[0,3])
(p3[0] <-> p3[0,3])
(p4[0,3,2,0,1,0,1,1] <-> ps5[0,3,2,0,1,0,1,1])
(pp[0] <-> pp[0,3])
(ps[0,3] <-> ps[0,3,2])
(ps[0,3,2] <-> ps[0,3,2,0])
(ps[0,3,2,0] <-> (ps[0,3,2,0,1] | ps[0,3,2,0,2]))
(ps[0,3,2,0,1] <-> ps[0,3,2,0,1,0])
(ps[0,3,2,0,1] <-> ps[0,3,2,0,2])
(ps[0,3,2,0,1,0] <-> ps[0,3,2,0,1,0,1])
(ps[0,3,2,0,1,0,1] <-> ps[0,3,2,0,1,0,1,3])
(ps[0,3,2,0,2] <-> ps[0,3,2,0,2,0])
(ps[0,3,2,0,2,0] <-> arg1[])
1
-}

factor = rget $ (procedure @'[ 'In, 'In, 'In ] factorIII) :& (procedure @'[ 'In, 'In, 'Out ] factorIIO) :& RNil
  where
    factorIII = \arg1 n f -> Logic.once $ do
      -- solution: d[0,3,2,0,0] d[0,3,2,0,0,0] data0[0] data0[0,3] data0[0,3,2] data0[0,3,2,0] data0[0,3,2,0,0,1] data1[0,3,2,0,1,0,1,1] p[0,1] p0[0,0] p2[0] p2[0,3] p2[0,3,0,1] p3[0] p3[0,3] p3[0,3,0,2] p4[0,3,2,0,1,0,1,2] pp[0] pp[0,3] pp[0,3,0,0] ps[0,2] ps1[0,0] ps5[0,3,2,0,1,0,1,3] ~arg1[] ~arg1[0] ~arg1[0,0] ~d[0,3,2,0,1,0] ~d[0,3,2,0,1,0,1] ~d[0,3,2,0,1,0,1,0] ~data0[0,3,2,0,0,0] ~data1[0,3,2,0,1,0,1,0] ~f[] ~f[0] ~f[0,3] ~f[0,3,1] ~f[0,3,1,0] ~f[0,3,2] ~f[0,3,2,0] ~f[0,3,2,0,1] ~f[0,3,2,0,1,0] ~f[0,3,2,0,1,0,0] ~f[0,3,2,0,1,0,0,0] ~f[0,3,2,0,1,0,1] ~f[0,3,2,0,1,0,1,0] ~f[0,3,2,0,2] ~f[0,3,2,0,2,0] ~n[] ~n[0] ~n[0,3] ~n[0,3,0,3] ~n[0,3,1,0] ~n[0,3,2] ~n[0,3,2,0] ~n[0,3,2,0,0,0] ~n[0,3,2,0,2] ~n[0,3,2,0,2,0] ~p[0,3] ~p[0,3,0,1] ~p[0,3,0,2] ~p[0,3,2] ~p[0,3,2,0] ~p[0,3,2,0,0,0] ~p[0,3,2,0,1,0] ~p[0,3,2,0,1,0,0] ~p[0,3,2,0,1,0,0,0] ~p[0,3,2,0,1,0,1] ~p[0,3,2,0,1,0,1,2] ~p0[0,1] ~p2[0,3,0,0] ~p3[0,3,0,0] ~p4[0,3,2,0,1,0,1,1] ~pp[0,3,0,3] ~ps[0,3] ~ps[0,3,2] ~ps[0,3,2,0] ~ps[0,3,2,0,1] ~ps[0,3,2,0,1,0] ~ps[0,3,2,0,1,0,1] ~ps[0,3,2,0,1,0,1,3] ~ps[0,3,2,0,2] ~ps[0,3,2,0,2,0] ~ps1[0,2] ~ps5[0,3,2,0,1,0,1,1]
      -- cost: 7
      () <- (do
        (p0:ps1) <- pure arg1
        p <- pure p0
        ps <- pure ps1
        () <- Logic.ifte ((do
          p2 <- pure p
          p3 <- pure p
          (OneTuple (pp)) <- runProcedure @'[ 'In, 'In, 'Out ] timesInt p2 p3
          guard $ (>) pp n
          pure ()
         )) (\() -> (do
          guard $ f == n
          pure ()
         )) ((do
          () <- Logic.ifte ((do
            data0 <- pure 0
            (OneTuple (d)) <- runProcedure @'[ 'In, 'In, 'Out, 'In ] divMod n p data0
            pure (d)
           )) (\(d) -> (do
            () <- (do
              guard $ f == p
              pure ()
             ) <|> (do
              p4 <- pure p
              ps5 <- pure ps
              data1 <- pure (p4:ps5)
              () <- factorIII data1 d f
              pure ()
             )
            pure ()
           )) ((do
            () <- factorIII ps n f
            pure ()
           ))
          pure ()
         ))
        pure ()
       )
      pure ()
    
    factorIIO = \arg1 n -> do
      -- solution: d[0,3,2,0,0] d[0,3,2,0,0,0] data0[0] data0[0,3] data0[0,3,2] data0[0,3,2,0] data0[0,3,2,0,0,1] data1[0,3,2,0,1,0,1,1] f[] f[0] f[0,3] f[0,3,1] f[0,3,1,0] f[0,3,2] f[0,3,2,0] f[0,3,2,0,1] f[0,3,2,0,1,0] f[0,3,2,0,1,0,0] f[0,3,2,0,1,0,0,0] f[0,3,2,0,1,0,1] f[0,3,2,0,1,0,1,0] f[0,3,2,0,2] f[0,3,2,0,2,0] p[0,1] p0[0,0] p2[0] p2[0,3] p2[0,3,0,1] p3[0] p3[0,3] p3[0,3,0,2] p4[0,3,2,0,1,0,1,2] pp[0] pp[0,3] pp[0,3,0,0] ps[0,2] ps1[0,0] ps5[0,3,2,0,1,0,1,3] ~arg1[] ~arg1[0] ~arg1[0,0] ~d[0,3,2,0,1,0] ~d[0,3,2,0,1,0,1] ~d[0,3,2,0,1,0,1,0] ~data0[0,3,2,0,0,0] ~data1[0,3,2,0,1,0,1,0] ~n[] ~n[0] ~n[0,3] ~n[0,3,0,3] ~n[0,3,1,0] ~n[0,3,2] ~n[0,3,2,0] ~n[0,3,2,0,0,0] ~n[0,3,2,0,2] ~n[0,3,2,0,2,0] ~p[0,3] ~p[0,3,0,1] ~p[0,3,0,2] ~p[0,3,2] ~p[0,3,2,0] ~p[0,3,2,0,0,0] ~p[0,3,2,0,1,0] ~p[0,3,2,0,1,0,0] ~p[0,3,2,0,1,0,0,0] ~p[0,3,2,0,1,0,1] ~p[0,3,2,0,1,0,1,2] ~p0[0,1] ~p2[0,3,0,0] ~p3[0,3,0,0] ~p4[0,3,2,0,1,0,1,1] ~pp[0,3,0,3] ~ps[0,3] ~ps[0,3,2] ~ps[0,3,2,0] ~ps[0,3,2,0,1] ~ps[0,3,2,0,1,0] ~ps[0,3,2,0,1,0,1] ~ps[0,3,2,0,1,0,1,3] ~ps[0,3,2,0,2] ~ps[0,3,2,0,2,0] ~ps1[0,2] ~ps5[0,3,2,0,1,0,1,1]
      -- cost: 9
      (f) <- (do
        (p0:ps1) <- pure arg1
        p <- pure p0
        ps <- pure ps1
        (f) <- Logic.ifte ((do
          p2 <- pure p
          p3 <- pure p
          (OneTuple (pp)) <- runProcedure @'[ 'In, 'In, 'Out ] timesInt p2 p3
          guard $ (>) pp n
          pure ()
         )) (\() -> (do
          f <- pure n
          pure (f)
         )) ((do
          (f) <- Logic.ifte ((do
            data0 <- pure 0
            (OneTuple (d)) <- runProcedure @'[ 'In, 'In, 'Out, 'In ] divMod n p data0
            pure (d)
           )) (\(d) -> (do
            (f) <- (do
              f <- pure p
              pure (f)
             ) <|> (do
              p4 <- pure p
              ps5 <- pure ps
              data1 <- pure (p4:ps5)
              (OneTuple (f)) <- factorIIO data1 d
              pure (f)
             )
            pure (f)
           )) ((do
            (OneTuple (f)) <- factorIIO ps n
            pure (f)
           ))
          pure (f)
         ))
        pure (f)
       )
      pure (OneTuple (f))
    
{- prime/1
prime arg1 :- ((arg1 = 2); (oddNat p, (>) p data0, data0 = 2, observeAll pred1 primes, (pred1 curry1 :- (prime curry1)), if (factor primes p d, (/=) p d) then (empty) else (), arg1 = p)).
constraints:
d[1,5]
~curry1[1]
~p[1,5]
~pred1[1,3]
~primes[1,5]
~primes[1,5,0,0]
~(arg1[1,6] & p[1,6])
~(d[1,5,0,0] & d[1,5,0,1])
~(data0[1,1] & data0[1,2])
~(p[1,0] & p[1,1])
~(p[1,0] & p[1,5])
~(p[1,0] & p[1,6])
~(p[1,1] & p[1,5])
~(p[1,1] & p[1,6])
~(p[1,5] & p[1,6])
~(p[1,5,0,0] & p[1,5,0,1])
~(primes[1,3] & primes[1,5])
~(p[1,5,0,0] | p[1,5,0,1])
(~p[1,1] & ~data0[1,1])
(~p[1,5,0,1] & ~d[1,5,0,1])
(~pred1[1,3] & (pred1(1) & primes[1,3]))
(d[1,5,0,0] | d[1,5,0,1])
(data0[1,1] | data0[1,2])
(p[1,0] | ~p[1,0])
(p[1,0] | (p[1,1] | (p[1,5] | p[1,6])))
(primes[1,3] | primes[1,5])
((~primes[1,5,0,0] & (~p[1,5,0,0] & d[1,5,0,0])) | (~primes[1,5,0,0] & (~p[1,5,0,0] & ~d[1,5,0,0])))
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg1[0] <-> arg1[0,0])
(arg1[1] <-> arg1[1,6])
(curry1[1,4,0] <-> curry1[1,4,0,0])
(curry1[1,4,0,0] <-> arg1[])
(d[1] <-> d[1,5])
(pred1(1) <-> curry1[1,4,0])
1
-}

prime = rget $ (procedure @'[ 'Out ] primeO) :& RNil
  where
    primeO = choose . Logic.observeAll $ do
      -- solution: arg1[] arg1[0] arg1[0,0] arg1[1] arg1[1,6] curry1[1,4,0] curry1[1,4,0,0] d[1] d[1,5] d[1,5,0,0] data0[1,2] p[1,0] primes[1,3] pred1(1) ~curry1[1] ~d[1,5,0,1] ~data0[1,1] ~p[1,1] ~p[1,5] ~p[1,5,0,0] ~p[1,5,0,1] ~p[1,6] ~pred1[1,3] ~primes[1,5] ~primes[1,5,0,0]
      -- cost: 11
      (arg1) <- (do
        arg1 <- pure 2
        pure (arg1)
       ) <|> (do
        data0 <- pure 2
        (OneTuple (p)) <- runProcedure @'[ 'Out ] oddNat 
        arg1 <- pure p
        guard $ (>) p data0
        let pred1 = procedure @'[ 'Out ] $
              do
                (curry1) <- (do
                  (OneTuple (curry1)) <- primeO 
                  pure (curry1)
                 )
                pure (OneTuple (curry1))
        (OneTuple (primes)) <- runProcedure @'[ 'PredMode '[ 'Out ], 'Out ] observeAll pred1
        () <- Logic.ifte ((do
          (OneTuple (d)) <- runProcedure @'[ 'In, 'In, 'Out ] factor primes p
          guard $ (/=) p d
          pure ()
         )) (\() -> (do
          () <- empty 
          pure ()
         )) ((do
          
          pure ()
         ))
        pure (arg1)
       )
      pure (OneTuple (arg1))
    
{- primeFactor/2
primeFactor n d :- ((observeAll pred0 primes, (pred0 curry1 :- (prime curry1)), factor primes n d)).
constraints:
curry1[0,1,0,0]
~curry1[0]
~pred0[0,0]
~(primes[0,0] & primes[0,2])
(~pred0[0,0] & (pred0(1) & primes[0,0]))
(primes[0,0] | primes[0,2])
((~primes[0,2] & (~n[0,2] & d[0,2])) | (~primes[0,2] & (~n[0,2] & ~d[0,2])))
(curry1[0,1,0] <-> curry1[0,1,0,0])
(d[] <-> d[0])
(d[0] <-> d[0,2])
(n[] <-> n[0])
(n[0] <-> n[0,2])
(pred0(1) <-> curry1[0,1,0])
1
-}

primeFactor = rget $ (procedure @'[ 'In, 'In ] primeFactorII) :& (procedure @'[ 'In, 'Out ] primeFactorIO) :& RNil
  where
    primeFactorII = \n d -> Logic.once $ do
      -- solution: curry1[0,1,0] curry1[0,1,0,0] primes[0,0] pred0(1) ~curry1[0] ~d[] ~d[0] ~d[0,2] ~n[] ~n[0] ~n[0,2] ~pred0[0,0] ~primes[0,2]
      -- cost: 5
      () <- (do
        let pred0 = procedure @'[ 'Out ] $
              do
                (curry1) <- (do
                  (OneTuple (curry1)) <- runProcedure @'[ 'Out ] prime 
                  pure (curry1)
                 )
                pure (OneTuple (curry1))
        (OneTuple (primes)) <- runProcedure @'[ 'PredMode '[ 'Out ], 'Out ] observeAll pred0
        () <- runProcedure @'[ 'In, 'In, 'In ] factor primes n d
        pure ()
       )
      pure ()
    
    primeFactorIO = \n -> do
      -- solution: curry1[0,1,0] curry1[0,1,0,0] d[] d[0] d[0,2] primes[0,0] pred0(1) ~curry1[0] ~n[] ~n[0] ~n[0,2] ~pred0[0,0] ~primes[0,2]
      -- cost: 6
      (d) <- (do
        let pred0 = procedure @'[ 'Out ] $
              do
                (curry1) <- (do
                  (OneTuple (curry1)) <- runProcedure @'[ 'Out ] prime 
                  pure (curry1)
                 )
                pure (OneTuple (curry1))
        (OneTuple (primes)) <- runProcedure @'[ 'PredMode '[ 'Out ], 'Out ] observeAll pred0
        (OneTuple (d)) <- runProcedure @'[ 'In, 'In, 'Out ] factor primes n
        pure (d)
       )
      pure (OneTuple (d))
    
{- euler3/2
euler3 n r :- ((observeAll pred0 fs, (pred0 curry1 :- (primeFactor n curry1)), maximum fs r)).
constraints:
~curry1[0]
~n[0]
~pred0[0,0]
~(fs[0,0] & fs[0,2])
(~pred0[0,0] & (pred0(1) & fs[0,0]))
(fs[0,0] | fs[0,2])
((~fs[0,2] & r[0,2]) | (~fs[0,2] & ~r[0,2]))
((~n[0,1,0,0] & curry1[0,1,0,0]) | (~n[0,1,0,0] & ~curry1[0,1,0,0]))
(curry1[0,1,0] <-> curry1[0,1,0,0])
(n[] <-> n[0])
(n[0,1,0] <-> n[0,1,0,0])
(r[] <-> r[0])
(r[0] <-> r[0,2])
(pred0(1) <-> curry1[0,1,0])
1
-}

euler3 = rget $ (procedure @'[ 'In, 'In ] euler3II) :& (procedure @'[ 'In, 'Out ] euler3IO) :& RNil
  where
    euler3II = \n r -> Logic.once $ do
      -- solution: curry1[0,1,0] curry1[0,1,0,0] fs[0,0] pred0(1) ~curry1[0] ~fs[0,2] ~n[] ~n[0] ~n[0,1,0] ~n[0,1,0,0] ~pred0[0,0] ~r[] ~r[0] ~r[0,2]
      -- cost: 5
      () <- (do
        let pred0 = procedure @'[ 'Out ] $
              do
                (curry1) <- (do
                  (OneTuple (curry1)) <- runProcedure @'[ 'In, 'Out ] primeFactor n
                  pure (curry1)
                 )
                pure (OneTuple (curry1))
        (OneTuple (fs)) <- runProcedure @'[ 'PredMode '[ 'Out ], 'Out ] observeAll pred0
        () <- runProcedure @'[ 'In, 'In ] maximum fs r
        pure ()
       )
      pure ()
    
    euler3IO = \n -> do
      -- solution: curry1[0,1,0] curry1[0,1,0,0] fs[0,0] r[] r[0] r[0,2] pred0(1) ~curry1[0] ~fs[0,2] ~n[] ~n[0] ~n[0,1,0] ~n[0,1,0,0] ~pred0[0,0]
      -- cost: 6
      (r) <- (do
        let pred0 = procedure @'[ 'Out ] $
              do
                (curry1) <- (do
                  (OneTuple (curry1)) <- runProcedure @'[ 'In, 'Out ] primeFactor n
                  pure (curry1)
                 )
                pure (OneTuple (curry1))
        (OneTuple (fs)) <- runProcedure @'[ 'PredMode '[ 'Out ], 'Out ] observeAll pred0
        (OneTuple (r)) <- runProcedure @'[ 'In, 'Out ] maximum fs
        pure (r)
       )
      pure (OneTuple (r))
    
{- euler4/1
euler4 n :- ((elem x data2, data0 = 10, data1 = 99, data2 = .. data0 data1, elem y data5, data3 = 10, data4 = 99, data5 = .. data3 data4, timesInt x y n, show n s, reverse s0 s1, s0 = s, s1 = s)).
constraints:
~(data0[0,1] & data0[0,3])
~(data1[0,2] & data1[0,3])
~(data2[0,0] & data2[0,3])
~(data2[0,3] & data0[0,3])
~(data3[0,5] & data3[0,7])
~(data4[0,6] & data4[0,7])
~(data5[0,4] & data5[0,7])
~(data5[0,7] & data3[0,7])
~(n[0,8] & n[0,9])
~(s[0,9] & s[0,11])
~(s[0,9] & s[0,12])
~(s[0,11] & s[0,12])
~(s0[0,10] & s0[0,11])
~(s0[0,11] & s[0,11])
~(s1[0,10] & s1[0,12])
~(s1[0,12] & s[0,12])
~(x[0,0] & x[0,8])
~(y[0,4] & y[0,8])
(x[0,0] & ~data2[0,0])
(y[0,4] & ~data5[0,4])
(data0[0,1] | data0[0,3])
(data1[0,2] | data1[0,3])
(data2[0,0] | data2[0,3])
(data3[0,5] | data3[0,7])
(data4[0,6] | data4[0,7])
(data5[0,4] | data5[0,7])
(s[0,9] | (s[0,11] | s[0,12]))
(s0[0,10] | s0[0,11])
(s1[0,10] | s1[0,12])
(x[0,0] | x[0,8])
(y[0,4] | y[0,8])
((n[0,9] & ~s[0,9]) | ((~n[0,9] & s[0,9]) | (~n[0,9] & ~s[0,9])))
((s0[0,10] & ~s1[0,10]) | ((~s0[0,10] & s1[0,10]) | (~s0[0,10] & ~s1[0,10])))
((x[0,8] & (~y[0,8] & ~n[0,8])) | ((~x[0,8] & (y[0,8] & ~n[0,8])) | (~x[0,8] & (~y[0,8] & n[0,8]))))
(data0[0,3] <-> data1[0,3])
(data3[0,7] <-> data4[0,7])
(n[] <-> n[0])
(n[0] <-> (n[0,8] | n[0,9]))
1
-}
--mode ordering failure, cyclic dependency: [10] reverse s0::O s1::I -> [11] s0::I = s::O -> [12] s1::O = s::I
--mode ordering failure, cyclic dependency: [10] reverse s0::I s1::O -> [12] s1::I = s::O -> [11] s0::O = s::I
euler4 = rget $ (procedure @'[ 'Out ] euler4O) :& RNil
  where
    euler4O = do
      -- solution: data0[0,1] data1[0,2] data2[0,3] data3[0,5] data4[0,6] data5[0,7] n[] n[0] n[0,8] s[0,9] s0[0,11] s1[0,12] x[0,0] y[0,4] ~data0[0,3] ~data1[0,3] ~data2[0,0] ~data3[0,7] ~data4[0,7] ~data5[0,4] ~n[0,9] ~s[0,11] ~s[0,12] ~s0[0,10] ~s1[0,10] ~x[0,8] ~y[0,8]
      -- cost: 9
      (n) <- (do
        data0 <- pure 10
        data3 <- pure 10
        data1 <- pure 99
        data2 <- pure [data0..data1]
        data4 <- pure 99
        data5 <- pure [data3..data4]
        (OneTuple (x)) <- runProcedure @'[ 'Out, 'In ] elem data2
        (OneTuple (y)) <- runProcedure @'[ 'Out, 'In ] elem data5
        (OneTuple (n)) <- runProcedure @'[ 'In, 'In, 'Out ] timesInt x y
        (OneTuple (s)) <- runProcedure @'[ 'In, 'Out ] show n
        s0 <- pure s
        s1 <- pure s
        () <- runProcedure @'[ 'In, 'In ] reverse s0 s1
        pure (n)
       )
      pure (OneTuple (n))
    
{- euler4'/1
euler4' n :- ((observeAll pred0 s, (pred0 curry1 :- (euler4 curry1)), maximum s n)).
constraints:
curry1[0,1,0,0]
~curry1[0]
~pred0[0,0]
~(s[0,0] & s[0,2])
(~pred0[0,0] & (pred0(1) & s[0,0]))
(s[0,0] | s[0,2])
((~s[0,2] & n[0,2]) | (~s[0,2] & ~n[0,2]))
(curry1[0,1,0] <-> curry1[0,1,0,0])
(n[] <-> n[0])
(n[0] <-> n[0,2])
(pred0(1) <-> curry1[0,1,0])
1
-}

euler4' = rget $ (procedure @'[ 'In ] euler4'I) :& (procedure @'[ 'Out ] euler4'O) :& RNil
  where
    euler4'I = \n -> Logic.once $ do
      -- solution: curry1[0,1,0] curry1[0,1,0,0] s[0,0] pred0(1) ~curry1[0] ~n[] ~n[0] ~n[0,2] ~pred0[0,0] ~s[0,2]
      -- cost: 5
      () <- (do
        let pred0 = procedure @'[ 'Out ] $
              do
                (curry1) <- (do
                  (OneTuple (curry1)) <- runProcedure @'[ 'Out ] euler4 
                  pure (curry1)
                 )
                pure (OneTuple (curry1))
        (OneTuple (s)) <- runProcedure @'[ 'PredMode '[ 'Out ], 'Out ] observeAll pred0
        () <- runProcedure @'[ 'In, 'In ] maximum s n
        pure ()
       )
      pure ()
    
    euler4'O = do
      -- solution: curry1[0,1,0] curry1[0,1,0,0] n[] n[0] n[0,2] s[0,0] pred0(1) ~curry1[0] ~pred0[0,0] ~s[0,2]
      -- cost: 6
      (n) <- (do
        let pred0 = procedure @'[ 'Out ] $
              do
                (curry1) <- (do
                  (OneTuple (curry1)) <- runProcedure @'[ 'Out ] euler4 
                  pure (curry1)
                 )
                pure (OneTuple (curry1))
        (OneTuple (s)) <- runProcedure @'[ 'PredMode '[ 'Out ], 'Out ] observeAll pred0
        (OneTuple (n)) <- runProcedure @'[ 'In, 'Out ] maximum s
        pure (n)
       )
      pure (OneTuple (n))
    
{- euler5/1
euler5 n :- ((nat n, (>) n data0, data0 = 0, all pred1 data4, data2 = 1, data3 = 5, data4 = .. data2 data3, (pred1 curry1 :- (multiple n curry1)))).
constraints:
~curry1[0]
~pred1[0,3]
~(data0[0,1] & data0[0,2])
~(data2[0,4] & data2[0,6])
~(data3[0,5] & data3[0,6])
~(data4[0,3] & data4[0,6])
~(data4[0,6] & data2[0,6])
~(n[0,0] & n[0,1])
(~n[0,1] & ~data0[0,1])
(~n[0,7,0,0] & ~curry1[0,7,0,0])
(~pred1[0,3] & (~pred1(1) & ~data4[0,3]))
(data0[0,1] | data0[0,2])
(data2[0,4] | data2[0,6])
(data3[0,5] | data3[0,6])
(data4[0,3] | data4[0,6])
(n[0,0] | ~n[0,0])
(curry1[0,7,0] <-> curry1[0,7,0,0])
(data2[0,6] <-> data3[0,6])
(n[] <-> n[0])
(n[0] <-> (n[0,0] | n[0,1]))
(n[0,7,0] <-> n[0,7,0,0])
(pred1(1) <-> curry1[0,7,0])
1
-}

euler5 = rget $ (procedure @'[ 'In ] euler5I) :& (procedure @'[ 'Out ] euler5O) :& RNil
  where
    euler5I = \n -> Logic.once $ do
      -- solution: data0[0,2] data2[0,4] data3[0,5] data4[0,6] ~curry1[0] ~curry1[0,7,0] ~curry1[0,7,0,0] ~data0[0,1] ~data2[0,6] ~data3[0,6] ~data4[0,3] ~n[] ~n[0] ~n[0,0] ~n[0,1] ~n[0,7,0] ~n[0,7,0,0] ~pred1[0,3] ~pred1(1)
      -- cost: 4
      () <- (do
        data0 <- pure 0
        data2 <- pure 1
        data3 <- pure 5
        data4 <- pure [data2..data3]
        guard $ (>) n data0
        () <- runProcedure @'[ 'In ] nat n
        let pred1 = procedure @'[ 'In ] $
              \curry1 -> do
                () <- (do
                  () <- runProcedure @'[ 'In, 'In ] multiple n curry1
                  pure ()
                 )
                pure ()
        () <- runProcedure @'[ 'PredMode '[ 'In ], 'In ] all pred1 data4
        pure ()
       )
      pure ()
    
    euler5O = do
      -- solution: data0[0,2] data2[0,4] data3[0,5] data4[0,6] n[] n[0] n[0,0] ~curry1[0] ~curry1[0,7,0] ~curry1[0,7,0,0] ~data0[0,1] ~data2[0,6] ~data3[0,6] ~data4[0,3] ~n[0,1] ~n[0,7,0] ~n[0,7,0,0] ~pred1[0,3] ~pred1(1)
      -- cost: 5
      (n) <- (do
        data0 <- pure 0
        data2 <- pure 1
        data3 <- pure 5
        data4 <- pure [data2..data3]
        (OneTuple (n)) <- runProcedure @'[ 'Out ] nat 
        guard $ (>) n data0
        let pred1 = procedure @'[ 'In ] $
              \curry1 -> do
                () <- (do
                  () <- runProcedure @'[ 'In, 'In ] multiple n curry1
                  pure ()
                 )
                pure ()
        () <- runProcedure @'[ 'PredMode '[ 'In ], 'In ] all pred1 data4
        pure (n)
       )
      pure (OneTuple (n))
    