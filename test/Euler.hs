{-# LANGUAGE DataKinds, FlexibleContexts, NoImplicitPrelude, NoMonomorphismRestriction, TypeApplications #-}
module Euler where

import qualified Control.Monad.Logic as Logic
import Control.Monad.Logic.Moded.Prelude

{- nat/1
nat arg1 :- ((arg1 = 0); (nat n, succ n n', arg1 = n')).
constraints:
~nat[1]
~succ[1]
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
      -- solution: n[1,1] n'[1,2]
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
      -- solution: arg1[] arg1[0] arg1[0,0] arg1[1] arg1[1,2] n[1,0] n'[1,1]
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
~oddNat[1]
~plus[1]
~(arg1[1,3] & n'[1,3])
~(data0[1,1] & data0[1,2])
~(n[1,0] & n[1,1])
~(n'[1,1] & n'[1,3])
(data0[1,1] | data0[1,2])
(n[1,0] | n[1,1])
(n'[1,1] | n'[1,3])
((n[1,1] & (~data0[1,1] & ~n'[1,1])) | ((~n[1,1] & (data0[1,1] & ~n'[1,1])) | ((~n[1,1] & (~data0[1,1] & n'[1,1])) | (~n[1,1] & (~data0[1,1] & ~n'[1,1])))))
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
      -- solution: data0[1,2] n[1,1] n'[1,3]
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
      -- solution: arg1[] arg1[0] arg1[0,0] arg1[1] arg1[1,3] data0[1,2] n[1,0] n'[1,1]
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
~mod[0]
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
      -- solution: data0[0,1] data1[0,2]
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
~elem[1]
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
      -- solution: x[] x[0] x[0,0] x[1] x[1,1] xs[1,0]
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
~p[1,3]
~p[1,3,1,0]
~span[1,3,1]
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
(p[1,3,1,0] <-> p[])
(span[1] <-> span[1,3])
(span[1,3] <-> span[1,3,1])
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
      -- solution: x[1,1] x0[1,0] x2[1,3,1,1] x3[1,3,2,1] xs[1,2] xs1[1,0] xs4[1,3,2,1] ys[1,4] yt[1,3,1,1] zs[1,5]
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
      -- solution: arg4[] arg4[0] arg4[0,2] arg4[1] arg4[1,5] x[1,1] x0[1,0] x2[1,3,1,1] x3[1,3,2,2] xs[1,2] xs1[1,0] xs4[1,3,2,3] ys[1,4] yt[1,3,1,1] zs[1,3] zs[1,3,1] zs[1,3,1,0] zs[1,3,2] zs[1,3,2,1]
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
      -- solution: arg3[] arg3[0] arg3[0,1] arg3[1] arg3[1,4] x[1,1] x0[1,0] x2[1,3,1,2] x3[1,3,2,1] xs[1,2] xs1[1,0] xs4[1,3,2,1] ys[1,3] ys[1,3,1] ys[1,3,1,1] ys[1,3,2] ys[1,3,2,0] yt[1,3,1,0] zs[1,5]
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
      -- solution: arg3[] arg3[0] arg3[0,1] arg3[1] arg3[1,4] arg4[] arg4[0] arg4[0,2] arg4[1] arg4[1,5] x[1,1] x0[1,0] x2[1,3,1,2] x3[1,3,2,2] xs[1,2] xs1[1,0] xs4[1,3,2,3] ys[1,3] ys[1,3,1] ys[1,3,1,1] ys[1,3,2] ys[1,3,2,0] yt[1,3,1,0] zs[1,3] zs[1,3,1] zs[1,3,1,0] zs[1,3,2] zs[1,3,2,1]
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
    
{- takeWhile/3
takeWhile p xs ys :- ((span p xs ys _)).
constraints:
~span[0]
((~p[0,0] & (~p(1) & (~xs[0,0] & ys[0,0]))) | (~p[0,0] & (~p(1) & (~xs[0,0] & ~ys[0,0]))))
(p[] <-> p[0])
(p[0] <-> p[0,0])
(xs[] <-> xs[0])
(xs[0] <-> xs[0,0])
(ys[] <-> ys[0])
(ys[0] <-> ys[0,0])
1
-}

takeWhile = rget $ (procedure @'[ 'PredMode '[ 'In ], 'In, 'In ] takeWhileP1III) :& (procedure @'[ 'PredMode '[ 'In ], 'In, 'Out ] takeWhileP1IIO) :& RNil
  where
    takeWhileP1III = \p xs ys -> Logic.once $ do
      -- solution: 
      -- cost: 2
      () <- (do
        (OneTuple (_)) <- runProcedure @'[ 'PredMode '[ 'In ], 'In, 'In, 'Out ] span p xs ys
        pure ()
       )
      pure ()
    
    takeWhileP1IIO = \p xs -> do
      -- solution: ys[] ys[0] ys[0,0]
      -- cost: 3
      (ys) <- (do
        (ys,_) <- runProcedure @'[ 'PredMode '[ 'In ], 'In, 'Out, 'Out ] span p xs
        pure (ys)
       )
      pure (OneTuple (ys))
    
{- reverseDL/3
reverseDL arg1 arg2 arg3 :- ((arg1 = [], arg2 = xs, arg3 = xs); (arg1 = h0:t, h0 = h, reverseDL t data0 r, data0 = h1:rest, h1 = h, arg2 = rest, arg3 = r)).
constraints:
~reverseDL[1]
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
      -- solution: data0[1,3] h[1,1] h0[1,0] h1[1,4] r[1,6] rest[1,5] t[1,0] xs[0,1]
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
      -- solution: arg3[] arg3[0] arg3[0,2] arg3[1] arg3[1,6] data0[1,3] h[1,1] h0[1,0] h1[1,4] r[1,2] rest[1,5] t[1,0] xs[0,1]
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
      -- solution: arg2[] arg2[0] arg2[0,1] arg2[1] arg2[1,5] data0[1,2] h[1,1] h0[1,0] h1[1,3] r[1,6] rest[1,3] t[1,0] xs[0,2]
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
      -- solution: arg1[] arg1[0] arg1[0,0] arg1[1] arg1[1,0] arg2[] arg2[0] arg2[0,1] arg2[1] arg2[1,5] data0[1,2] h[1,4] h0[1,1] h1[1,3] r[1,6] rest[1,3] t[1,2] xs[0,2]
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
~reverseDL[0]
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
      -- solution: data0[0,1]
      -- cost: 1
      () <- (do
        data0 <- pure []
        () <- runProcedure @'[ 'In, 'In, 'In ] reverseDL s data0 r
        pure ()
       )
      pure ()
    
    reverseIO = \s -> do
      -- solution: data0[0,1] r[] r[0] r[0,0]
      -- cost: 2
      (r) <- (do
        data0 <- pure []
        (OneTuple (r)) <- runProcedure @'[ 'In, 'In, 'Out ] reverseDL s data0
        pure (r)
       )
      pure (OneTuple (r))
    
    reverseOI = \r -> do
      -- solution: data0[0,0] s[] s[0] s[0,0]
      -- cost: 3
      (s) <- (do
        (s,data0) <- runProcedure @'[ 'Out, 'Out, 'In ] reverseDL r
        guard $ data0 == []
        pure (s)
       )
      pure (OneTuple (s))
    
{- all/2
all p arg2 :- ((arg2 = []); (arg2 = h:t, p h, all p t)).
constraints:
~all[1]
~p[]
~(arg2[1,0] & h[1,0])
~(h[1,0] & h[1,1])
~(t[1,0] & t[1,2])
(h[1,0] | h[1,1])
(t[1,0] | t[1,2])
(arg2[] <-> arg2[0])
(arg2[] <-> arg2[1])
(arg2[0] <-> arg2[0,0])
(arg2[1] <-> arg2[1,0])
(h[1,0] <-> t[1,0])
(h[1,1] <-> p(1))
(p[] <-> p[1])
(p[1] <-> p[1,2])
(p[1,2] <-> p[])
(t[1,2] <-> arg2[])
1
-}

all = rget $ (procedure @'[ 'PredMode '[ 'In ], 'In ] allP1II) :& (procedure @'[ 'PredMode '[ 'Out ], 'Out ] allP1OO) :& RNil
  where
    allP1II = \p arg2 -> Logic.once $ do
      -- solution: h[1,0] t[1,0]
      -- cost: 2
      () <- (do
        guard $ arg2 == []
        pure ()
       ) <|> (do
        (h:t) <- pure arg2
        () <- allP1II p t
        () <- runProcedure p h
        pure ()
       )
      pure ()
    
    allP1OO = \p -> do
      -- solution: arg2[] arg2[0] arg2[0,0] arg2[1] arg2[1,0] h[1,1] t[1,2] p(1)
      -- cost: 4
      (arg2) <- (do
        arg2 <- pure []
        pure (arg2)
       ) <|> (do
        (OneTuple (t)) <- allP1OO p
        (OneTuple (h)) <- runProcedure p 
        arg2 <- pure (h:t)
        pure (arg2)
       )
      pure (OneTuple (arg2))
    
{- multiple/2
multiple x y :- ((mod x y data0, data0 = 0)).
constraints:
~mod[0]
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
      -- solution: data0[0,1]
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
~elem[0]
~multiple[0]
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
      -- solution: data0[0,1] data1[0,2] data2[0,3] x[] x[0] x[0,0] y[0,5] y[0,5,0] y[0,5,0,0] y[0,5,1] y[0,5,1,0]
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
euler1' carg3 :- ((observeAll pred1_1 x_0, (pred1_1 x_0 :- (euler1 x_0)), sum x_0 carg3)).
constraints:
x_0[0,1,0,0]
~euler1[0,1,0]
~observeAll[0]
~pred1_1[0,0]
~sum[0]
~(x_0[0,0] & x_0[0,2])
(~pred1_1[0,0] & (pred1_1(1) & x_0[0,0]))
(x_0[0,0] | x_0[0,2])
((~x_0[0,2] & carg3[0,2]) | (~x_0[0,2] & ~carg3[0,2]))
(carg3[] <-> carg3[0])
(carg3[0] <-> carg3[0,2])
(euler1[0] <-> euler1[0,1])
(x_0[0,1,0] <-> x_0[0,1,0,0])
(pred1_1(1) <-> x_0[0,1,0])
1
-}

euler1' = rget $ (procedure @'[ 'In ] euler1'I) :& (procedure @'[ 'Out ] euler1'O) :& RNil
  where
    euler1'I = \carg3 -> Logic.once $ do
      -- solution: euler1[0] euler1[0,1] x_0[0,0] x_0[0,1,0] x_0[0,1,0,0] pred1_1(1)
      -- cost: 5
      () <- (do
        let pred1_1 = procedure @'[ 'Out ] $
              do
                (x_0) <- (do
                  (OneTuple (x_0)) <- runProcedure @'[ 'Out ] euler1 
                  pure (x_0)
                 )
                pure (OneTuple (x_0))
        (OneTuple (x_0)) <- runProcedure @'[ 'PredMode '[ 'Out ], 'Out ] observeAll pred1_1
        () <- runProcedure @'[ 'In, 'In ] sum x_0 carg3
        pure ()
       )
      pure ()
    
    euler1'O = do
      -- solution: carg3[] carg3[0] carg3[0,2] euler1[0] euler1[0,1] x_0[0,0] x_0[0,1,0] x_0[0,1,0,0] pred1_1(1)
      -- cost: 6
      (carg3) <- (do
        let pred1_1 = procedure @'[ 'Out ] $
              do
                (x_0) <- (do
                  (OneTuple (x_0)) <- runProcedure @'[ 'Out ] euler1 
                  pure (x_0)
                 )
                pure (OneTuple (x_0))
        (OneTuple (x_0)) <- runProcedure @'[ 'PredMode '[ 'Out ], 'Out ] observeAll pred1_1
        (OneTuple (carg3)) <- runProcedure @'[ 'In, 'Out ] sum x_0
        pure (carg3)
       )
      pure (OneTuple (carg3))
    
{- fib/2
fib arg1 arg2 :- ((arg1 = 0, arg2 = 0); (arg1 = 1, arg2 = 1); ((>) k data0, data0 = 1, succ i j, succ j k, fib i fi, fib j fj, plus fi fj fk, arg1 = k, arg2 = fk)).
constraints:
~(>)[2]
~fib[2]
~plus[2]
~succ[2]
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
((fi[2,6] & (~fj[2,6] & ~fk[2,6])) | ((~fi[2,6] & (fj[2,6] & ~fk[2,6])) | ((~fi[2,6] & (~fj[2,6] & fk[2,6])) | (~fi[2,6] & (~fj[2,6] & ~fk[2,6])))))
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
      -- solution: arg2[] arg2[0] arg2[0,1] arg2[1] arg2[1,1] arg2[2] arg2[2,8] data0[2,1] fi[2,4] fj[2,5] fk[2,6] i[2,2] j[2,3] k[2,7]
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
      -- solution: arg1[] arg1[0] arg1[0,0] arg1[1] arg1[1,0] arg1[2] arg1[2,7] arg2[] arg2[0] arg2[0,1] arg2[1] arg2[1,1] arg2[2] arg2[2,8] data0[2,1] fi[2,4] fj[2,5] fk[2,6] i[2,4] j[2,5] k[2,3]
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
fib' carg3 :- ((nat x_0, fib x_0 carg3)).
constraints:
~fib[0]
~nat[0]
~(x_0[0,0] & x_0[0,1])
(x_0[0,0] | x_0[0,1])
(x_0[0,0] | ~x_0[0,0])
((x_0[0,1] & carg3[0,1]) | (~x_0[0,1] & carg3[0,1]))
(carg3[] <-> carg3[0])
(carg3[0] <-> carg3[0,1])
1
-}

fib' = rget $ (procedure @'[ 'Out ] fib'O) :& RNil
  where
    fib'O = do
      -- solution: carg3[] carg3[0] carg3[0,1] x_0[0,0]
      -- cost: 4
      (carg3) <- (do
        (OneTuple (x_0)) <- runProcedure @'[ 'Out ] nat 
        (OneTuple (carg3)) <- runProcedure @'[ 'In, 'Out ] fib x_0
        pure (carg3)
       )
      pure (OneTuple (carg3))
    
{- euler2/1
euler2 carg3 :- ((observeAll pred4_1_4 x_3, (pred4_1_4 x_1 :- (fib' x_1, even x_1)), takeWhile pred2_1_5 x_3 x_0, (pred2_1_5 x_1 :- ((<) x_1 data1_1_5, data1_1_5 = 1000000)), sum x_0 carg3)).
constraints:
x_1[0,1,0,0]
~(<)[0,3,0]
~even[0,1,0]
~fib'[0,1,0]
~observeAll[0]
~pred2_1_5[0,2]
~pred4_1_4[0,0]
~sum[0]
~takeWhile[0]
~x_1[0]
~x_1[0,1,0,1]
~(data1_1_5[0,3,0,0] & data1_1_5[0,3,0,1])
~(x_0[0,2] & x_0[0,4])
~(x_1[0,1,0,0] & x_1[0,1,0,1])
~(x_3[0,0] & x_3[0,2])
(~pred4_1_4[0,0] & (pred4_1_4(1) & x_3[0,0]))
(~x_1[0,3,0,0] & ~data1_1_5[0,3,0,0])
(data1_1_5[0,3,0,0] | data1_1_5[0,3,0,1])
(x_0[0,2] | x_0[0,4])
(x_3[0,0] | x_3[0,2])
((~pred2_1_5[0,2] & (~pred2_1_5(1) & (~x_3[0,2] & x_0[0,2]))) | (~pred2_1_5[0,2] & (~pred2_1_5(1) & (~x_3[0,2] & ~x_0[0,2]))))
((~x_0[0,4] & carg3[0,4]) | (~x_0[0,4] & ~carg3[0,4]))
((<)[0] <-> (<)[0,3])
(carg3[] <-> carg3[0])
(carg3[0] <-> carg3[0,4])
(data1_1_5[0] <-> data1_1_5[0,3])
(even[0] <-> even[0,1])
(fib'[0] <-> fib'[0,1])
(x_1[0,1,0] <-> (x_1[0,1,0,0] | x_1[0,1,0,1]))
(x_1[0,3,0] <-> x_1[0,3,0,0])
(pred2_1_5(1) <-> x_1[0,3,0])
(pred4_1_4(1) <-> x_1[0,1,0])
1
-}

euler2 = rget $ (procedure @'[ 'In ] euler2I) :& (procedure @'[ 'Out ] euler2O) :& RNil
  where
    euler2I = \carg3 -> Logic.once $ do
      -- solution: (<)[0] (<)[0,3] data1_1_5[0] data1_1_5[0,3] data1_1_5[0,3,0,1] even[0] even[0,1] fib'[0] fib'[0,1] x_0[0,2] x_1[0,1,0] x_1[0,1,0,0] x_3[0,0] pred4_1_4(1)
      -- cost: 9
      () <- (do
        let pred4_1_4 = procedure @'[ 'Out ] $
              do
                (x_1) <- (do
                  (OneTuple (x_1)) <- runProcedure @'[ 'Out ] fib' 
                  () <- runProcedure @'[ 'In ] even x_1
                  pure (x_1)
                 )
                pure (OneTuple (x_1))
        let pred2_1_5 = procedure @'[ 'In ] $
              \x_1 -> do
                () <- (do
                  data1_1_5 <- pure 1000000
                  guard $ (<) x_1 data1_1_5
                  pure ()
                 )
                pure ()
        (OneTuple (x_3)) <- runProcedure @'[ 'PredMode '[ 'Out ], 'Out ] observeAll pred4_1_4
        (OneTuple (x_0)) <- runProcedure @'[ 'PredMode '[ 'In ], 'In, 'Out ] takeWhile pred2_1_5 x_3
        () <- runProcedure @'[ 'In, 'In ] sum x_0 carg3
        pure ()
       )
      pure ()
    
    euler2O = do
      -- solution: (<)[0] (<)[0,3] carg3[] carg3[0] carg3[0,4] data1_1_5[0] data1_1_5[0,3] data1_1_5[0,3,0,1] even[0] even[0,1] fib'[0] fib'[0,1] x_0[0,2] x_1[0,1,0] x_1[0,1,0,0] x_3[0,0] pred4_1_4(1)
      -- cost: 10
      (carg3) <- (do
        let pred4_1_4 = procedure @'[ 'Out ] $
              do
                (x_1) <- (do
                  (OneTuple (x_1)) <- runProcedure @'[ 'Out ] fib' 
                  () <- runProcedure @'[ 'In ] even x_1
                  pure (x_1)
                 )
                pure (OneTuple (x_1))
        let pred2_1_5 = procedure @'[ 'In ] $
              \x_1 -> do
                () <- (do
                  data1_1_5 <- pure 1000000
                  guard $ (<) x_1 data1_1_5
                  pure ()
                 )
                pure ()
        (OneTuple (x_3)) <- runProcedure @'[ 'PredMode '[ 'Out ], 'Out ] observeAll pred4_1_4
        (OneTuple (x_0)) <- runProcedure @'[ 'PredMode '[ 'In ], 'In, 'Out ] takeWhile pred2_1_5 x_3
        (OneTuple (carg3)) <- runProcedure @'[ 'In, 'Out ] sum x_0
        pure (carg3)
       )
      pure (OneTuple (carg3))
    
{- nontrivialDivisor/2
nontrivialDivisor n d :- ((succ n' n, elem d data1, data0 = 2, data1 = .. data0 n', multiple n d)).
constraints:
~elem[0]
~multiple[0]
~succ[0]
~(d[0,1] & d[0,4])
~(data0[0,2] & data0[0,3])
~(data1[0,1] & data1[0,3])
~(data1[0,3] & data0[0,3])
~(n[0,0] & n[0,4])
~(n'[0,0] & n'[0,3])
(d[0,1] & ~data1[0,1])
(~n[0,4] & ~d[0,4])
(data0[0,2] | data0[0,3])
(data1[0,1] | data1[0,3])
(n'[0,0] | n'[0,3])
((n'[0,0] & ~n[0,0]) | ((~n'[0,0] & n[0,0]) | (~n'[0,0] & ~n[0,0])))
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
      -- solution: d[] d[0] d[0,1] data0[0,2] data1[0,3] n'[0,0]
      -- cost: 5
      (d) <- (do
        data0 <- pure 2
        (OneTuple (n')) <- runProcedure @'[ 'Out, 'In ] succ n
        data1 <- pure [data0..n']
        (OneTuple (d)) <- runProcedure @'[ 'Out, 'In ] elem data1
        () <- runProcedure @'[ 'In, 'In ] multiple n d
        pure (d)
       )
      pure (OneTuple (d))
    
{- primeSlow/1
primeSlow n :- ((nat n, (>) n data0, data0 = 1, if (nontrivialDivisor n _) then (empty) else ())).
constraints:
_[0,3]
~(>)[0]
~empty[0,3,1]
~n[0,3]
~n[0,3,0,0]
~nat[0]
~nontrivialDivisor[0,3,0]
~(data0[0,1] & data0[0,2])
~(n[0,0] & n[0,1])
~(n[0,0] & n[0,3])
~(n[0,1] & n[0,3])
(~n[0,1] & ~data0[0,1])
(data0[0,1] | data0[0,2])
(n[0,0] | ~n[0,0])
(_[0] <-> _[0,3])
(empty[0] <-> empty[0,3])
(empty[0,3] <-> empty[0,3,1])
(n[] <-> n[0])
(n[0] <-> (n[0,0] | (n[0,1] | n[0,3])))
(nontrivialDivisor[0] <-> nontrivialDivisor[0,3])
(nontrivialDivisor[0,3] <-> nontrivialDivisor[0,3,0])
1
-}

primeSlow = rget $ (procedure @'[ 'In ] primeSlowI) :& (procedure @'[ 'Out ] primeSlowO) :& RNil
  where
    primeSlowI = \n -> Logic.once $ do
      -- solution: _[0] _[0,3] data0[0,2]
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
      -- solution: _[0] _[0,3] data0[0,2] n[] n[0] n[0,0]
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
factor n arg2 f :- ((arg2 = p0:ps1, p0 = p, ps1 = ps, if (timesInt p2 p3 pp, p2 = p, p3 = p, (>) pp n) then (f = n) else (if (divMod n p d data0, data0 = 0) then (((f = p); (factor d data1 f, data1 = p4:ps5, p4 = p, ps5 = ps))) else (factor n ps f)))).
constraints:
d[0,3,2,0,0]
data0[0,3,2,0]
p2[0,3]
p3[0,3]
pp[0,3]
~(>)[0,3,0]
~d[0,3,2,0,1,0]
~divMod[0,3,2,0,0]
~factor[0,3,2,0,1,0,1]
~factor[0,3,2,0,2]
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
~timesInt[0,3,0]
~(arg2[0,0] & p0[0,0])
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
((p2[0,3,0,0] & (~p3[0,3,0,0] & ~pp[0,3,0,0])) | ((~p2[0,3,0,0] & (p3[0,3,0,0] & ~pp[0,3,0,0])) | ((~p2[0,3,0,0] & (~p3[0,3,0,0] & pp[0,3,0,0])) | (~p2[0,3,0,0] & (~p3[0,3,0,0] & ~pp[0,3,0,0])))))
((~n[0,3,2,0,0,0] & (~p[0,3,2,0,0,0] & (d[0,3,2,0,0,0] & data0[0,3,2,0,0,0]))) | ((~n[0,3,2,0,0,0] & (~p[0,3,2,0,0,0] & (d[0,3,2,0,0,0] & ~data0[0,3,2,0,0,0]))) | ((~n[0,3,2,0,0,0] & (~p[0,3,2,0,0,0] & (~d[0,3,2,0,0,0] & data0[0,3,2,0,0,0]))) | (~n[0,3,2,0,0,0] & (~p[0,3,2,0,0,0] & (~d[0,3,2,0,0,0] & ~data0[0,3,2,0,0,0]))))))
((>)[0] <-> (>)[0,3])
((>)[0,3] <-> (>)[0,3,0])
(arg2[] <-> arg2[0])
(arg2[0] <-> arg2[0,0])
(d[0,3,2,0,0] <-> d[0,3,2,0,0,0])
(d[0,3,2,0,1,0] <-> d[0,3,2,0,1,0,1])
(d[0,3,2,0,1,0,1] <-> d[0,3,2,0,1,0,1,0])
(d[0,3,2,0,1,0,1,0] <-> n[])
(data0[0] <-> data0[0,3])
(data0[0,3] <-> data0[0,3,2])
(data0[0,3,2] <-> data0[0,3,2,0])
(data1[0,3,2,0,1,0,1,0] <-> arg2[])
(divMod[0] <-> divMod[0,3])
(divMod[0,3] <-> divMod[0,3,2])
(divMod[0,3,2] <-> divMod[0,3,2,0])
(divMod[0,3,2,0] <-> divMod[0,3,2,0,0])
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
(factor[0] <-> factor[0,3])
(factor[0,3] <-> factor[0,3,2])
(factor[0,3,2] <-> factor[0,3,2,0])
(factor[0,3,2,0] <-> (factor[0,3,2,0,1] | factor[0,3,2,0,2]))
(factor[0,3,2,0,1] <-> factor[0,3,2,0,1,0])
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
(ps[0,3,2,0,2,0] <-> arg2[])
(timesInt[0] <-> timesInt[0,3])
(timesInt[0,3] <-> timesInt[0,3,0])
1
-}

factor = rget $ (procedure @'[ 'In, 'In, 'In ] factorIII) :& (procedure @'[ 'In, 'In, 'Out ] factorIIO) :& RNil
  where
    factorIII = \n arg2 f -> Logic.once $ do
      -- solution: d[0,3,2,0,0] d[0,3,2,0,0,0] data0[0] data0[0,3] data0[0,3,2] data0[0,3,2,0] data0[0,3,2,0,0,1] data1[0,3,2,0,1,0,1,1] factor[0] factor[0,3] factor[0,3,2] factor[0,3,2,0] factor[0,3,2,0,1] factor[0,3,2,0,1,0] p[0,1] p0[0,0] p2[0] p2[0,3] p2[0,3,0,1] p3[0] p3[0,3] p3[0,3,0,2] p4[0,3,2,0,1,0,1,2] pp[0] pp[0,3] pp[0,3,0,0] ps[0,2] ps1[0,0] ps5[0,3,2,0,1,0,1,3]
      -- cost: 7
      () <- (do
        (p0:ps1) <- pure arg2
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
              () <- factorIII d data1 f
              pure ()
             )
            pure ()
           )) ((do
            () <- factorIII n ps f
            pure ()
           ))
          pure ()
         ))
        pure ()
       )
      pure ()
    
    factorIIO = \n arg2 -> do
      -- solution: d[0,3,2,0,0] d[0,3,2,0,0,0] data0[0] data0[0,3] data0[0,3,2] data0[0,3,2,0] data0[0,3,2,0,0,1] data1[0,3,2,0,1,0,1,1] f[] f[0] f[0,3] f[0,3,1] f[0,3,1,0] f[0,3,2] f[0,3,2,0] f[0,3,2,0,1] f[0,3,2,0,1,0] f[0,3,2,0,1,0,0] f[0,3,2,0,1,0,0,0] f[0,3,2,0,1,0,1] f[0,3,2,0,1,0,1,0] f[0,3,2,0,2] f[0,3,2,0,2,0] factor[0] factor[0,3] factor[0,3,2] factor[0,3,2,0] factor[0,3,2,0,1] factor[0,3,2,0,1,0] p[0,1] p0[0,0] p2[0] p2[0,3] p2[0,3,0,1] p3[0] p3[0,3] p3[0,3,0,2] p4[0,3,2,0,1,0,1,2] pp[0] pp[0,3] pp[0,3,0,0] ps[0,2] ps1[0,0] ps5[0,3,2,0,1,0,1,3]
      -- cost: 9
      (f) <- (do
        (p0:ps1) <- pure arg2
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
              (OneTuple (f)) <- factorIIO d data1
              pure (f)
             )
            pure (f)
           )) ((do
            (OneTuple (f)) <- factorIIO n ps
            pure (f)
           ))
          pure (f)
         ))
        pure (f)
       )
      pure (OneTuple (f))
    
{- prime/1
prime arg1 :- ((arg1 = 2); (oddNat p, (>) p data0, data0 = 2, observeAll pred1 primes, (pred1 curry1 :- (prime curry1)), if (factor p primes d, (/=) p d) then (empty) else (), arg1 = p)).
constraints:
d[1,5]
~(/=)[1,5,0]
~(>)[1]
~curry1[1]
~empty[1,5,1]
~factor[1,5,0]
~observeAll[1]
~oddNat[1]
~p[1,5]
~pred1[1,3]
~prime[1,4,0]
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
((~p[1,5,0,0] & (~primes[1,5,0,0] & d[1,5,0,0])) | (~p[1,5,0,0] & (~primes[1,5,0,0] & ~d[1,5,0,0])))
((/=)[1] <-> (/=)[1,5])
((/=)[1,5] <-> (/=)[1,5,0])
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg1[0] <-> arg1[0,0])
(arg1[1] <-> arg1[1,6])
(curry1[1,4,0] <-> curry1[1,4,0,0])
(curry1[1,4,0,0] <-> arg1[])
(d[1] <-> d[1,5])
(empty[1] <-> empty[1,5])
(empty[1,5] <-> empty[1,5,1])
(factor[1] <-> factor[1,5])
(factor[1,5] <-> factor[1,5,0])
(prime[1] <-> prime[1,4])
(pred1(1) <-> curry1[1,4,0])
1
-}

prime = rget $ (procedure @'[ 'Out ] primeO) :& RNil
  where
    primeO = choose . Logic.observeAll $ do
      -- solution: arg1[] arg1[0] arg1[0,0] arg1[1] arg1[1,6] curry1[1,4,0] curry1[1,4,0,0] d[1] d[1,5] d[1,5,0,0] data0[1,2] p[1,0] prime[1] prime[1,4] primes[1,3] pred1(1)
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
          (OneTuple (d)) <- runProcedure @'[ 'In, 'In, 'Out ] factor p primes
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
primeFactor n carg3 :- ((observeAll pred1_1 x_0, (pred1_1 x_0 :- (prime x_0)), factor n x_0 carg3)).
constraints:
x_0[0,1,0,0]
~factor[0]
~observeAll[0]
~pred1_1[0,0]
~prime[0,1,0]
~(x_0[0,0] & x_0[0,2])
(~pred1_1[0,0] & (pred1_1(1) & x_0[0,0]))
(x_0[0,0] | x_0[0,2])
((~n[0,2] & (~x_0[0,2] & carg3[0,2])) | (~n[0,2] & (~x_0[0,2] & ~carg3[0,2])))
(carg3[] <-> carg3[0])
(carg3[0] <-> carg3[0,2])
(n[] <-> n[0])
(n[0] <-> n[0,2])
(prime[0] <-> prime[0,1])
(x_0[0,1,0] <-> x_0[0,1,0,0])
(pred1_1(1) <-> x_0[0,1,0])
1
-}

primeFactor = rget $ (procedure @'[ 'In, 'In ] primeFactorII) :& (procedure @'[ 'In, 'Out ] primeFactorIO) :& RNil
  where
    primeFactorII = \n carg3 -> Logic.once $ do
      -- solution: prime[0] prime[0,1] x_0[0,0] x_0[0,1,0] x_0[0,1,0,0] pred1_1(1)
      -- cost: 5
      () <- (do
        let pred1_1 = procedure @'[ 'Out ] $
              do
                (x_0) <- (do
                  (OneTuple (x_0)) <- runProcedure @'[ 'Out ] prime 
                  pure (x_0)
                 )
                pure (OneTuple (x_0))
        (OneTuple (x_0)) <- runProcedure @'[ 'PredMode '[ 'Out ], 'Out ] observeAll pred1_1
        () <- runProcedure @'[ 'In, 'In, 'In ] factor n x_0 carg3
        pure ()
       )
      pure ()
    
    primeFactorIO = \n -> do
      -- solution: carg3[] carg3[0] carg3[0,2] prime[0] prime[0,1] x_0[0,0] x_0[0,1,0] x_0[0,1,0,0] pred1_1(1)
      -- cost: 6
      (carg3) <- (do
        let pred1_1 = procedure @'[ 'Out ] $
              do
                (x_0) <- (do
                  (OneTuple (x_0)) <- runProcedure @'[ 'Out ] prime 
                  pure (x_0)
                 )
                pure (OneTuple (x_0))
        (OneTuple (x_0)) <- runProcedure @'[ 'PredMode '[ 'Out ], 'Out ] observeAll pred1_1
        (OneTuple (carg3)) <- runProcedure @'[ 'In, 'In, 'Out ] factor n x_0
        pure (carg3)
       )
      pure (OneTuple (carg3))
    
{- euler3/2
euler3 n carg3 :- ((observeAll pred1_1 x_0, (pred1_1 x_0 :- (primeFactor n x_0)), maximum x_0 carg3)).
constraints:
~maximum[0]
~n[0]
~observeAll[0]
~pred1_1[0,0]
~primeFactor[0,1,0]
~(x_0[0,0] & x_0[0,2])
(~pred1_1[0,0] & (pred1_1(1) & x_0[0,0]))
(x_0[0,0] | x_0[0,2])
((~n[0,1,0,0] & x_0[0,1,0,0]) | (~n[0,1,0,0] & ~x_0[0,1,0,0]))
((~x_0[0,2] & carg3[0,2]) | (~x_0[0,2] & ~carg3[0,2]))
(carg3[] <-> carg3[0])
(carg3[0] <-> carg3[0,2])
(n[] <-> n[0])
(n[0,1,0] <-> n[0,1,0,0])
(primeFactor[0] <-> primeFactor[0,1])
(x_0[0,1,0] <-> x_0[0,1,0,0])
(pred1_1(1) <-> x_0[0,1,0])
1
-}

euler3 = rget $ (procedure @'[ 'In, 'In ] euler3II) :& (procedure @'[ 'In, 'Out ] euler3IO) :& RNil
  where
    euler3II = \n carg3 -> Logic.once $ do
      -- solution: primeFactor[0] primeFactor[0,1] x_0[0,0] x_0[0,1,0] x_0[0,1,0,0] pred1_1(1)
      -- cost: 5
      () <- (do
        let pred1_1 = procedure @'[ 'Out ] $
              do
                (x_0) <- (do
                  (OneTuple (x_0)) <- runProcedure @'[ 'In, 'Out ] primeFactor n
                  pure (x_0)
                 )
                pure (OneTuple (x_0))
        (OneTuple (x_0)) <- runProcedure @'[ 'PredMode '[ 'Out ], 'Out ] observeAll pred1_1
        () <- runProcedure @'[ 'In, 'In ] maximum x_0 carg3
        pure ()
       )
      pure ()
    
    euler3IO = \n -> do
      -- solution: carg3[] carg3[0] carg3[0,2] primeFactor[0] primeFactor[0,1] x_0[0,0] x_0[0,1,0] x_0[0,1,0,0] pred1_1(1)
      -- cost: 6
      (carg3) <- (do
        let pred1_1 = procedure @'[ 'Out ] $
              do
                (x_0) <- (do
                  (OneTuple (x_0)) <- runProcedure @'[ 'In, 'Out ] primeFactor n
                  pure (x_0)
                 )
                pure (OneTuple (x_0))
        (OneTuple (x_0)) <- runProcedure @'[ 'PredMode '[ 'Out ], 'Out ] observeAll pred1_1
        (OneTuple (carg3)) <- runProcedure @'[ 'In, 'Out ] maximum x_0
        pure (carg3)
       )
      pure (OneTuple (carg3))
    
{- euler4/1
euler4 n :- ((elem x data2, data0 = 10, data1 = 99, data2 = .. data0 data1, elem y data5, data3 = 10, data4 = 99, data5 = .. data3 data4, timesInt x y n, show n s, reverse s0 s1, s0 = s, s1 = s)).
constraints:
~elem[0]
~reverse[0]
~show[0]
~timesInt[0]
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
((x[0,8] & (~y[0,8] & ~n[0,8])) | ((~x[0,8] & (y[0,8] & ~n[0,8])) | ((~x[0,8] & (~y[0,8] & n[0,8])) | (~x[0,8] & (~y[0,8] & ~n[0,8])))))
(data0[0,3] <-> data1[0,3])
(data3[0,7] <-> data4[0,7])
(n[] <-> n[0])
(n[0] <-> (n[0,8] | n[0,9]))
1
-}
--mode ordering failure, cyclic dependency: [10] reverse::I s0::O s1::I -> [11] s0::I = s::O -> [12] s1::O = s::I
--mode ordering failure, cyclic dependency: [10] reverse::I s0::I s1::O -> [12] s1::I = s::O -> [11] s0::O = s::I
--mode ordering failure, cyclic dependency: [10] reverse::I s0::O s1::I -> [11] s0::I = s::O -> [12] s1::O = s::I
--mode ordering failure, cyclic dependency: [10] reverse::I s0::I s1::O -> [12] s1::I = s::O -> [11] s0::O = s::I
--mode ordering failure, cyclic dependency: [10] reverse::I s0::O s1::I -> [11] s0::I = s::O -> [12] s1::O = s::I
--mode ordering failure, cyclic dependency: [10] reverse::I s0::I s1::O -> [12] s1::I = s::O -> [11] s0::O = s::I
euler4 = rget $ (procedure @'[ 'In ] euler4I) :& (procedure @'[ 'Out ] euler4O) :& RNil
  where
    euler4I = \n -> Logic.once $ do
      -- solution: data0[0,1] data1[0,2] data2[0,3] data3[0,5] data4[0,6] data5[0,7] s[0,9] s0[0,11] s1[0,12] x[0,0] y[0,4]
      -- cost: 8
      () <- (do
        data0 <- pure 10
        data3 <- pure 10
        data1 <- pure 99
        data2 <- pure [data0..data1]
        data4 <- pure 99
        data5 <- pure [data3..data4]
        (OneTuple (x)) <- runProcedure @'[ 'Out, 'In ] elem data2
        (OneTuple (y)) <- runProcedure @'[ 'Out, 'In ] elem data5
        () <- runProcedure @'[ 'In, 'In, 'In ] timesInt x y n
        (OneTuple (s)) <- runProcedure @'[ 'In, 'Out ] show n
        s0 <- pure s
        s1 <- pure s
        () <- runProcedure @'[ 'In, 'In ] reverse s0 s1
        pure ()
       )
      pure ()
    
    euler4O = do
      -- solution: data0[0,1] data1[0,2] data2[0,3] data3[0,5] data4[0,6] data5[0,7] n[] n[0] n[0,8] s[0,9] s0[0,11] s1[0,12] x[0,0] y[0,4]
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
euler4' carg3 :- ((observeAll pred1_1 x_0, (pred1_1 x_0 :- (euler4 x_0)), maximum x_0 carg3)).
constraints:
~euler4[0,1,0]
~maximum[0]
~observeAll[0]
~pred1_1[0,0]
~(x_0[0,0] & x_0[0,2])
(~pred1_1[0,0] & (pred1_1(1) & x_0[0,0]))
(x_0[0,0] | x_0[0,2])
(x_0[0,1,0,0] | ~x_0[0,1,0,0])
((~x_0[0,2] & carg3[0,2]) | (~x_0[0,2] & ~carg3[0,2]))
(carg3[] <-> carg3[0])
(carg3[0] <-> carg3[0,2])
(euler4[0] <-> euler4[0,1])
(x_0[0,1,0] <-> x_0[0,1,0,0])
(pred1_1(1) <-> x_0[0,1,0])
1
-}

euler4' = rget $ (procedure @'[ 'In ] euler4'I) :& (procedure @'[ 'Out ] euler4'O) :& RNil
  where
    euler4'I = \carg3 -> Logic.once $ do
      -- solution: euler4[0] euler4[0,1] x_0[0,0] x_0[0,1,0] x_0[0,1,0,0] pred1_1(1)
      -- cost: 5
      () <- (do
        let pred1_1 = procedure @'[ 'Out ] $
              do
                (x_0) <- (do
                  (OneTuple (x_0)) <- runProcedure @'[ 'Out ] euler4 
                  pure (x_0)
                 )
                pure (OneTuple (x_0))
        (OneTuple (x_0)) <- runProcedure @'[ 'PredMode '[ 'Out ], 'Out ] observeAll pred1_1
        () <- runProcedure @'[ 'In, 'In ] maximum x_0 carg3
        pure ()
       )
      pure ()
    
    euler4'O = do
      -- solution: carg3[] carg3[0] carg3[0,2] euler4[0] euler4[0,1] x_0[0,0] x_0[0,1,0] x_0[0,1,0,0] pred1_1(1)
      -- cost: 6
      (carg3) <- (do
        let pred1_1 = procedure @'[ 'Out ] $
              do
                (x_0) <- (do
                  (OneTuple (x_0)) <- runProcedure @'[ 'Out ] euler4 
                  pure (x_0)
                 )
                pure (OneTuple (x_0))
        (OneTuple (x_0)) <- runProcedure @'[ 'PredMode '[ 'Out ], 'Out ] observeAll pred1_1
        (OneTuple (carg3)) <- runProcedure @'[ 'In, 'Out ] maximum x_0
        pure (carg3)
       )
      pure (OneTuple (carg3))
    
{- euler5/1
euler5 n :- ((nat n, (>) n data0, data0 = 0, all pred1 data4, data2 = 1, data3 = 5, data4 = .. data2 data3, (pred1 curry1 :- (multiple n curry1)))).
constraints:
~(>)[0]
~all[0]
~curry1[0]
~multiple[0,7,0]
~nat[0]
~pred1[0,3]
~(data0[0,1] & data0[0,2])
~(data2[0,4] & data2[0,6])
~(data3[0,5] & data3[0,6])
~(data4[0,3] & data4[0,6])
~(data4[0,6] & data2[0,6])
~(n[0,0] & n[0,1])
(~n[0,1] & ~data0[0,1])
(~n[0,7,0,0] & ~curry1[0,7,0,0])
(data0[0,1] | data0[0,2])
(data2[0,4] | data2[0,6])
(data3[0,5] | data3[0,6])
(data4[0,3] | data4[0,6])
(n[0,0] | ~n[0,0])
((~pred1[0,3] & (pred1(1) & data4[0,3])) | (~pred1[0,3] & (~pred1(1) & ~data4[0,3])))
(curry1[0,7,0] <-> curry1[0,7,0,0])
(data2[0,6] <-> data3[0,6])
(multiple[0] <-> multiple[0,7])
(n[] <-> n[0])
(n[0] <-> (n[0,0] | n[0,1]))
(n[0,7,0] <-> n[0,7,0,0])
(pred1(1) <-> curry1[0,7,0])
1
-}

euler5 = rget $ (procedure @'[ 'In ] euler5I) :& (procedure @'[ 'Out ] euler5O) :& RNil
  where
    euler5I = \n -> Logic.once $ do
      -- solution: data0[0,2] data2[0,4] data3[0,5] data4[0,6] multiple[0] multiple[0,7]
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
      -- solution: data0[0,2] data2[0,4] data3[0,5] data4[0,6] multiple[0] multiple[0,7] n[] n[0] n[0,0]
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
    