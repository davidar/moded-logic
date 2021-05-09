{-# LANGUAGE DataKinds, FlexibleContexts, NoImplicitPrelude, NoMonomorphismRestriction, TypeApplications #-}
module Euler where

import qualified Control.Monad.Logic as Logic
import Control.Monad.Logic.Moded.Prelude

{- nat/1
nat arg1 :- ((arg1 = 0); (arg1 = n', nat n, succ n n')).
constraints:
~nat[1]
~succ[1]
~(arg1[1,0] & n'[1,0])
~(n[1,1] & n[1,2])
~(n'[1,0] & n'[1,2])
(n[1,1] | n[1,2])
(n'[1,0] | n'[1,2])
((n[1,2] & ~n'[1,2]) | ((~n[1,2] & n'[1,2]) | (~n[1,2] & ~n'[1,2])))
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg1[0] <-> arg1[0,0])
(arg1[1] <-> arg1[1,0])
(n[1,1] <-> arg1[])
1
-}

nat = rget $ (procedure @'[ 'In ] natI) :& (procedure @'[ 'Out ] natO) :& RNil
  where
    natI = \arg1 -> Logic.once $ do
      -- solution: n[1,2] n'[1,0]
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
      -- solution: arg1[] arg1[0] arg1[0,0] arg1[1] arg1[1,0] n[1,1] n'[1,2]
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
oddNat arg1 :- ((arg1 = 1); (arg1 = n', oddNat n, plus n data0 n', data0 = 2)).
constraints:
~oddNat[1]
~plus[1]
~(arg1[1,0] & n'[1,0])
~(data0[1,2] & data0[1,3])
~(n[1,1] & n[1,2])
~(n'[1,0] & n'[1,2])
(data0[1,2] | data0[1,3])
(n[1,1] | n[1,2])
(n'[1,0] | n'[1,2])
((n[1,2] & (~data0[1,2] & ~n'[1,2])) | ((~n[1,2] & (data0[1,2] & ~n'[1,2])) | ((~n[1,2] & (~data0[1,2] & n'[1,2])) | (~n[1,2] & (~data0[1,2] & ~n'[1,2])))))
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg1[0] <-> arg1[0,0])
(arg1[1] <-> arg1[1,0])
(n[1,1] <-> arg1[])
1
-}

oddNat = rget $ (procedure @'[ 'In ] oddNatI) :& (procedure @'[ 'Out ] oddNatO) :& RNil
  where
    oddNatI = \arg1 -> Logic.once $ do
      -- solution: data0[1,3] n[1,2] n'[1,0]
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
      -- solution: arg1[] arg1[0] arg1[0,0] arg1[1] arg1[1,0] data0[1,3] n[1,1] n'[1,2]
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
        data0 <- pure 2
        data1 <- pure 0
        () <- runProcedure @'[ 'In, 'In, 'In ] mod x data0 data1
        pure ()
       )
      pure ()
    
{- elem/2
elem arg1 arg2 :- ((arg1 = x0, x0 = x, arg2 = x1:_, x1 = x); (arg1 = x, arg2 = _:xs, elem x xs)).
constraints:
x1[0,2]
xs[1,1]
~arg2[1,1]
~elem[1]
~(arg1[0,0] & x0[0,0])
~(arg1[1,0] & x[1,0])
~(arg2[0,2] & x1[0,2])
~(x[0,1] & x[0,3])
~(x[1,0] & x[1,2])
~(x0[0,0] & x0[0,1])
~(x0[0,1] & x[0,1])
~(x1[0,2] & x1[0,3])
~(x1[0,3] & x[0,3])
~(xs[1,1] & xs[1,2])
(x[0,1] | x[0,3])
(x[1,0] | x[1,2])
(x0[0,0] | x0[0,1])
(x1[0,2] | x1[0,3])
(xs[1,1] | xs[1,2])
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg1[0] <-> arg1[0,0])
(arg1[1] <-> arg1[1,0])
(arg2[] <-> arg2[0])
(arg2[] <-> arg2[1])
(arg2[0] <-> arg2[0,2])
(arg2[1] <-> arg2[1,1])
(x[1,2] <-> arg1[])
(xs[1,2] <-> arg2[])
1
-}

elem = rget $ (procedure @'[ 'In, 'In ] elemII) :& (procedure @'[ 'Out, 'In ] elemOI) :& RNil
  where
    elemII = \arg1 arg2 -> Logic.once $ do
      -- solution: x[0,1] x[1,0] x0[0,0] x1[0,2] xs[1,1]
      -- cost: 1
      () <- (do
        x0 <- pure arg1
        (x1:_) <- pure arg2
        x <- pure x0
        guard $ x1 == x
        pure ()
       ) <|> (do
        x <- pure arg1
        (_:xs) <- pure arg2
        () <- elemII x xs
        pure ()
       )
      pure ()
    
    elemOI = \arg2 -> do
      -- solution: arg1[] arg1[0] arg1[0,0] arg1[1] arg1[1,0] x[0,3] x[1,2] x0[0,1] x1[0,2] xs[1,1]
      -- cost: 2
      (arg1) <- (do
        (x1:_) <- pure arg2
        x <- pure x1
        x0 <- pure x
        arg1 <- pure x0
        pure (arg1)
       ) <|> (do
        (_:xs) <- pure arg2
        (OneTuple (x)) <- elemOI xs
        arg1 <- pure x
        pure (arg1)
       )
      pure (OneTuple (arg1))
    
{- span/4
span arg1 arg2 arg3 arg4 :- ((arg2 = [], arg3 = [], arg4 = []); (arg1 = p, arg2 = x0:xs1, x0 = x, xs1 = xs, arg3 = ys, arg4 = zs, if (p x) then (span p xs yt zs, ys = x2:yt, x2 = x) else (ys = [], zs = x3:xs4, x3 = x, xs4 = xs))).
constraints:
~arg1[]
~p[1,6]
~p[1,6,1,0]
~span[1,6,1]
~x[1,6,0,0]
~x[1,6,1,2]
~x[1,6,2]
~(arg1[1,0] & p[1,0])
~(arg2[1,1] & x0[1,1])
~(arg3[1,4] & ys[1,4])
~(arg4[1,5] & zs[1,5])
~(p[1,0] & p[1,6])
~(x[1,2] & x[1,6])
~(x0[1,1] & x0[1,2])
~(x0[1,2] & x[1,2])
~(x2[1,6,1,1] & x2[1,6,1,2])
~(x2[1,6,1,2] & x[1,6,1,2])
~(x3[1,6,2,1] & x3[1,6,2,2])
~(x3[1,6,2,2] & x[1,6,2,2])
~(xs[1,3] & xs[1,6])
~(xs1[1,1] & xs1[1,3])
~(xs1[1,3] & xs[1,3])
~(xs4[1,6,2,1] & xs4[1,6,2,3])
~(xs4[1,6,2,3] & xs[1,6,2,3])
~(ys[1,4] & ys[1,6])
~(ys[1,6,1,1] & x2[1,6,1,1])
~(yt[1,6,1,0] & yt[1,6,1,1])
~(zs[1,5] & zs[1,6])
~(zs[1,6,2,1] & x3[1,6,2,1])
(p[1,0] | p[1,6])
(x[1,2] | x[1,6])
(x0[1,1] | x0[1,2])
(x2[1,6,1,1] | x2[1,6,1,2])
(x3[1,6,2,1] | x3[1,6,2,2])
(xs[1,3] | xs[1,6])
(xs1[1,1] | xs1[1,3])
(xs4[1,6,2,1] | xs4[1,6,2,3])
(ys[1,4] | ys[1,6])
(yt[1,6,1,0] | yt[1,6,1,1])
(zs[1,5] | zs[1,6])
(arg1[] <-> arg1[1])
(arg1[1] <-> arg1[1,0])
(arg2[] <-> arg2[0])
(arg2[] <-> arg2[1])
(arg2[0] <-> arg2[0,0])
(arg2[1] <-> arg2[1,1])
(arg3[] <-> arg3[0])
(arg3[] <-> arg3[1])
(arg3[0] <-> arg3[0,1])
(arg3[1] <-> arg3[1,4])
(arg4[] <-> arg4[0])
(arg4[] <-> arg4[1])
(arg4[0] <-> arg4[0,2])
(arg4[1] <-> arg4[1,5])
(p[1,6,1,0] <-> arg1[])
(span[1] <-> span[1,6])
(span[1,6] <-> span[1,6,1])
(x[1,6] <-> x[1,6,2])
(x[1,6,0,0] <-> arg1(1))
(x[1,6,0,0] <-> p(1))
(x[1,6,2] <-> x[1,6,2,2])
(x0[1,1] <-> xs1[1,1])
(x2[1,6,1,1] <-> yt[1,6,1,1])
(x3[1,6,2,1] <-> xs4[1,6,2,1])
(xs[1,6] <-> (xs[1,6,1] | xs[1,6,2]))
(xs[1,6,1] <-> xs[1,6,1,0])
(xs[1,6,1] <-> xs[1,6,2])
(xs[1,6,1,0] <-> arg2[])
(xs[1,6,2] <-> xs[1,6,2,3])
(ys[1,6] <-> (ys[1,6,1] | ys[1,6,2]))
(ys[1,6,1] <-> ys[1,6,1,1])
(ys[1,6,1] <-> ys[1,6,2])
(ys[1,6,2] <-> ys[1,6,2,0])
(yt[1,6,1,0] <-> arg3[])
(zs[1,6] <-> (zs[1,6,1] | zs[1,6,2]))
(zs[1,6,1] <-> zs[1,6,1,0])
(zs[1,6,1] <-> zs[1,6,2])
(zs[1,6,1,0] <-> arg4[])
(zs[1,6,2] <-> zs[1,6,2,1])
1
-}

span = rget $ (procedure @'[ 'PredMode '[ 'In ], 'In, 'In, 'In ] spanP1IIII) :& (procedure @'[ 'PredMode '[ 'In ], 'In, 'In, 'Out ] spanP1IIIO) :& (procedure @'[ 'PredMode '[ 'In ], 'In, 'Out, 'In ] spanP1IIOI) :& (procedure @'[ 'PredMode '[ 'In ], 'In, 'Out, 'Out ] spanP1IIOO) :& RNil
  where
    spanP1IIII = \arg1 arg2 arg3 arg4 -> Logic.once $ do
      -- solution: p[1,0] x[1,2] x0[1,1] x2[1,6,1,1] x3[1,6,2,1] xs[1,3] xs1[1,1] xs4[1,6,2,1] ys[1,4] yt[1,6,1,1] zs[1,5]
      -- cost: 2
      () <- (do
        guard $ arg2 == []
        guard $ arg3 == []
        guard $ arg4 == []
        pure ()
       ) <|> (do
        p <- pure arg1
        (x0:xs1) <- pure arg2
        ys <- pure arg3
        zs <- pure arg4
        x <- pure x0
        xs <- pure xs1
        () <- Logic.ifte ((do
          () <- runProcedure @'[ 'In ] p x
          pure ()
         )) (\() -> (do
          (x2:yt) <- pure ys
          guard $ x2 == x
          () <- spanP1IIII p xs yt zs
          pure ()
         )) ((do
          guard $ ys == []
          (x3:xs4) <- pure zs
          guard $ x3 == x
          guard $ xs4 == xs
          pure ()
         ))
        pure ()
       )
      pure ()
    
    spanP1IIIO = \arg1 arg2 arg3 -> do
      -- solution: arg4[] arg4[0] arg4[0,2] arg4[1] arg4[1,5] p[1,0] x[1,2] x0[1,1] x2[1,6,1,1] x3[1,6,2,2] xs[1,3] xs1[1,1] xs4[1,6,2,3] ys[1,4] yt[1,6,1,1] zs[1,6] zs[1,6,1] zs[1,6,1,0] zs[1,6,2] zs[1,6,2,1]
      -- cost: 3
      (arg4) <- (do
        guard $ arg2 == []
        guard $ arg3 == []
        arg4 <- pure []
        pure (arg4)
       ) <|> (do
        p <- pure arg1
        (x0:xs1) <- pure arg2
        ys <- pure arg3
        x <- pure x0
        xs <- pure xs1
        (zs) <- Logic.ifte ((do
          () <- runProcedure @'[ 'In ] p x
          pure ()
         )) (\() -> (do
          (x2:yt) <- pure ys
          guard $ x2 == x
          (OneTuple (zs)) <- spanP1IIIO p xs yt
          pure (zs)
         )) ((do
          x3 <- pure x
          xs4 <- pure xs
          guard $ ys == []
          zs <- pure (x3:xs4)
          pure (zs)
         ))
        arg4 <- pure zs
        pure (arg4)
       )
      pure (OneTuple (arg4))
    
    spanP1IIOI = \arg1 arg2 arg4 -> do
      -- solution: arg3[] arg3[0] arg3[0,1] arg3[1] arg3[1,4] p[1,0] x[1,2] x0[1,1] x2[1,6,1,2] x3[1,6,2,2] xs[1,3] xs1[1,1] xs4[1,6,2,3] ys[1,6] ys[1,6,1] ys[1,6,1,1] ys[1,6,2] ys[1,6,2,0] yt[1,6,1,0] zs[1,5]
      -- cost: 3
      (arg3) <- (do
        guard $ arg2 == []
        arg3 <- pure []
        guard $ arg4 == []
        pure (arg3)
       ) <|> (do
        p <- pure arg1
        (x0:xs1) <- pure arg2
        zs <- pure arg4
        x <- pure x0
        xs <- pure xs1
        (ys) <- Logic.ifte ((do
          () <- runProcedure @'[ 'In ] p x
          pure ()
         )) (\() -> (do
          x2 <- pure x
          (OneTuple (yt)) <- spanP1IIOI p xs zs
          ys <- pure (x2:yt)
          pure (ys)
         )) ((do
          x3 <- pure x
          xs4 <- pure xs
          ys <- pure []
          guard $ zs == (x3:xs4)
          pure (ys)
         ))
        arg3 <- pure ys
        pure (arg3)
       )
      pure (OneTuple (arg3))
    
    spanP1IIOO = \arg1 arg2 -> do
      -- solution: arg3[] arg3[0] arg3[0,1] arg3[1] arg3[1,4] arg4[] arg4[0] arg4[0,2] arg4[1] arg4[1,5] p[1,0] x[1,2] x0[1,1] x2[1,6,1,2] x3[1,6,2,2] xs[1,3] xs1[1,1] xs4[1,6,2,3] ys[1,6] ys[1,6,1] ys[1,6,1,1] ys[1,6,2] ys[1,6,2,0] yt[1,6,1,0] zs[1,6] zs[1,6,1] zs[1,6,1,0] zs[1,6,2] zs[1,6,2,1]
      -- cost: 4
      (arg3,arg4) <- (do
        guard $ arg2 == []
        arg3 <- pure []
        arg4 <- pure []
        pure (arg3,arg4)
       ) <|> (do
        p <- pure arg1
        (x0:xs1) <- pure arg2
        x <- pure x0
        xs <- pure xs1
        (ys,zs) <- Logic.ifte ((do
          () <- runProcedure @'[ 'In ] p x
          pure ()
         )) (\() -> (do
          x2 <- pure x
          (yt,zs) <- spanP1IIOO p xs
          ys <- pure (x2:yt)
          pure (ys,zs)
         )) ((do
          x3 <- pure x
          xs4 <- pure xs
          ys <- pure []
          zs <- pure (x3:xs4)
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
reverseDL arg1 arg2 arg3 :- ((arg1 = [], arg2 = xs0, xs0 = xs, arg3 = xs1, xs1 = xs); (arg1 = h2:t, h2 = h, arg2 = rest3, rest3 = rest, arg3 = r, reverseDL t data0 r, data0 = h4:rest5, h4 = h, rest5 = rest)).
constraints:
~reverseDL[1]
~(arg1[1,0] & h2[1,0])
~(arg2[0,1] & xs0[0,1])
~(arg2[1,2] & rest3[1,2])
~(arg3[0,3] & xs1[0,3])
~(arg3[1,4] & r[1,4])
~(data0[1,5] & data0[1,6])
~(data0[1,6] & h4[1,6])
~(h[1,1] & h[1,7])
~(h2[1,0] & h2[1,1])
~(h2[1,1] & h[1,1])
~(h4[1,6] & h4[1,7])
~(h4[1,7] & h[1,7])
~(r[1,4] & r[1,5])
~(rest[1,3] & rest[1,8])
~(rest3[1,2] & rest3[1,3])
~(rest3[1,3] & rest[1,3])
~(rest5[1,6] & rest5[1,8])
~(rest5[1,8] & rest[1,8])
~(t[1,0] & t[1,5])
~(xs[0,2] & xs[0,4])
~(xs0[0,1] & xs0[0,2])
~(xs0[0,2] & xs[0,2])
~(xs1[0,3] & xs1[0,4])
~(xs1[0,4] & xs[0,4])
(data0[1,5] | data0[1,6])
(h[1,1] | h[1,7])
(h2[1,0] | h2[1,1])
(h4[1,6] | h4[1,7])
(r[1,4] | r[1,5])
(rest[1,3] | rest[1,8])
(rest3[1,2] | rest3[1,3])
(rest5[1,6] | rest5[1,8])
(t[1,0] | t[1,5])
(xs[0,2] | xs[0,4])
(xs0[0,1] | xs0[0,2])
(xs1[0,3] | xs1[0,4])
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg1[0] <-> arg1[0,0])
(arg1[1] <-> arg1[1,0])
(arg2[] <-> arg2[0])
(arg2[] <-> arg2[1])
(arg2[0] <-> arg2[0,1])
(arg2[1] <-> arg2[1,2])
(arg3[] <-> arg3[0])
(arg3[] <-> arg3[1])
(arg3[0] <-> arg3[0,3])
(arg3[1] <-> arg3[1,4])
(data0[1,5] <-> arg2[])
(h2[1,0] <-> t[1,0])
(h4[1,6] <-> rest5[1,6])
(r[1,5] <-> arg3[])
(t[1,5] <-> arg1[])
1
-}

reverseDL = rget $ (procedure @'[ 'In, 'In, 'In ] reverseDLIII) :& (procedure @'[ 'In, 'In, 'Out ] reverseDLIIO) :& (procedure @'[ 'In, 'Out, 'In ] reverseDLIOI) :& (procedure @'[ 'Out, 'Out, 'In ] reverseDLOOI) :& RNil
  where
    reverseDLIII = \arg1 arg2 arg3 -> Logic.once $ do
      -- solution: data0[1,6] h[1,1] h2[1,0] h4[1,7] r[1,4] rest[1,3] rest3[1,2] rest5[1,8] t[1,0] xs[0,2] xs0[0,1] xs1[0,3]
      -- cost: 1
      () <- (do
        guard $ arg1 == []
        xs0 <- pure arg2
        xs1 <- pure arg3
        xs <- pure xs0
        guard $ xs1 == xs
        pure ()
       ) <|> (do
        (h2:t) <- pure arg1
        rest3 <- pure arg2
        r <- pure arg3
        h <- pure h2
        h4 <- pure h
        rest <- pure rest3
        rest5 <- pure rest
        data0 <- pure (h4:rest5)
        () <- reverseDLIII t data0 r
        pure ()
       )
      pure ()
    
    reverseDLIIO = \arg1 arg2 -> do
      -- solution: arg3[] arg3[0] arg3[0,3] arg3[1] arg3[1,4] data0[1,6] h[1,1] h2[1,0] h4[1,7] r[1,5] rest[1,3] rest3[1,2] rest5[1,8] t[1,0] xs[0,2] xs0[0,1] xs1[0,4]
      -- cost: 2
      (arg3) <- (do
        guard $ arg1 == []
        xs0 <- pure arg2
        xs <- pure xs0
        xs1 <- pure xs
        arg3 <- pure xs1
        pure (arg3)
       ) <|> (do
        (h2:t) <- pure arg1
        rest3 <- pure arg2
        h <- pure h2
        h4 <- pure h
        rest <- pure rest3
        rest5 <- pure rest
        data0 <- pure (h4:rest5)
        (OneTuple (r)) <- reverseDLIIO t data0
        arg3 <- pure r
        pure (arg3)
       )
      pure (OneTuple (arg3))
    
    reverseDLIOI = \arg1 arg3 -> do
      -- solution: arg2[] arg2[0] arg2[0,1] arg2[1] arg2[1,2] data0[1,5] h[1,1] h2[1,0] h4[1,6] r[1,4] rest[1,8] rest3[1,3] rest5[1,6] t[1,0] xs[0,4] xs0[0,2] xs1[0,3]
      -- cost: 2
      (arg2) <- (do
        guard $ arg1 == []
        xs1 <- pure arg3
        xs <- pure xs1
        xs0 <- pure xs
        arg2 <- pure xs0
        pure (arg2)
       ) <|> (do
        (h2:t) <- pure arg1
        r <- pure arg3
        h <- pure h2
        (OneTuple (data0)) <- reverseDLIOI t r
        (h4:rest5) <- pure data0
        guard $ h4 == h
        rest <- pure rest5
        rest3 <- pure rest
        arg2 <- pure rest3
        pure (arg2)
       )
      pure (OneTuple (arg2))
    
    reverseDLOOI = \arg3 -> do
      -- solution: arg1[] arg1[0] arg1[0,0] arg1[1] arg1[1,0] arg2[] arg2[0] arg2[0,1] arg2[1] arg2[1,2] data0[1,5] h[1,7] h2[1,1] h4[1,6] r[1,4] rest[1,8] rest3[1,3] rest5[1,6] t[1,5] xs[0,4] xs0[0,2] xs1[0,3]
      -- cost: 3
      (arg1,arg2) <- (do
        arg1 <- pure []
        xs1 <- pure arg3
        xs <- pure xs1
        xs0 <- pure xs
        arg2 <- pure xs0
        pure (arg1,arg2)
       ) <|> (do
        r <- pure arg3
        (t,data0) <- reverseDLOOI r
        (h4:rest5) <- pure data0
        h <- pure h4
        h2 <- pure h
        arg1 <- pure (h2:t)
        rest <- pure rest5
        rest3 <- pure rest
        arg2 <- pure rest3
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
all arg1 arg2 :- ((arg2 = []); (arg1 = p, arg2 = h:t, p h, all p t)).
constraints:
~all[1]
~arg1[]
~(arg1[1,0] & p[1,0])
~(arg2[1,1] & h[1,1])
~(h[1,1] & h[1,2])
~(p[1,0] & p[1,3])
~(t[1,1] & t[1,3])
(h[1,1] | h[1,2])
(p[1,0] | p[1,3])
(t[1,1] | t[1,3])
(arg1[] <-> arg1[1])
(arg1[1] <-> arg1[1,0])
(arg2[] <-> arg2[0])
(arg2[] <-> arg2[1])
(arg2[0] <-> arg2[0,0])
(arg2[1] <-> arg2[1,1])
(h[1,1] <-> t[1,1])
(h[1,2] <-> arg1(1))
(h[1,2] <-> p(1))
(p[1,3] <-> arg1[])
(t[1,3] <-> arg2[])
1
-}

all = rget $ (procedure @'[ 'PredMode '[ 'In ], 'In ] allP1II) :& (procedure @'[ 'PredMode '[ 'Out ], 'Out ] allP1OO) :& RNil
  where
    allP1II = \arg1 arg2 -> Logic.once $ do
      -- solution: h[1,1] p[1,0] t[1,1]
      -- cost: 2
      () <- (do
        guard $ arg2 == []
        pure ()
       ) <|> (do
        p <- pure arg1
        (h:t) <- pure arg2
        () <- allP1II p t
        () <- runProcedure @'[ 'In ] p h
        pure ()
       )
      pure ()
    
    allP1OO = \arg1 -> do
      -- solution: arg2[] arg2[0] arg2[0,0] arg2[1] arg2[1,1] h[1,2] p[1,0] t[1,3] arg1(1) p(1)
      -- cost: 4
      (arg2) <- (do
        arg2 <- pure []
        pure (arg2)
       ) <|> (do
        p <- pure arg1
        (OneTuple (t)) <- allP1OO p
        (OneTuple (h)) <- runProcedure @'[ 'Out ] p 
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
(~x[0,4] & ~y[0,4])
(data0[0,1] | data0[0,3])
(data1[0,2] | data1[0,3])
(data2[0,0] | data2[0,3])
(y[0,4] | y[0,5])
((x[0,0] & ~data2[0,0]) | (~x[0,0] & ~data2[0,0]))
(data0[0,3] <-> data1[0,3])
(x[] <-> x[0])
(x[0] <-> (x[0,0] | x[0,4]))
(y[0,5] <-> y[0,5,0])
(y[0,5] <-> y[0,5,1])
(y[0,5,0] <-> y[0,5,0,0])
(y[0,5,1] <-> y[0,5,1,0])
1
-}

euler1 = rget $ (procedure @'[ 'In ] euler1I) :& (procedure @'[ 'Out ] euler1O) :& RNil
  where
    euler1I = \x -> choose . nub . Logic.observeAll $ do
      -- solution: data0[0,1] data1[0,2] data2[0,3] y[0,5] y[0,5,0] y[0,5,0,0] y[0,5,1] y[0,5,1,0]
      -- cost: 2
      () <- (do
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
        () <- runProcedure @'[ 'In, 'In ] elem x data2
        () <- runProcedure @'[ 'In, 'In ] multiple x y
        pure ()
       )
      pure ()
    
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
~euler1[0,1,0]
~observeAll[0]
~pred1_1[0,0]
~sum[0]
~(x_0[0,0] & x_0[0,2])
(~pred1_1[0,0] & (pred1_1(1) & x_0[0,0]))
(x_0[0,0] | x_0[0,2])
(x_0[0,1,0,0] | ~x_0[0,1,0,0])
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
      -- solution: x_0[0,0] x_0[0,1,0] x_0[0,1,0,0] pred1_1(1)
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
fib arg1 arg2 :- ((arg1 = 0, arg2 = 0); (arg1 = 1, arg2 = 1); (arg1 = k, arg2 = fk, (>) k data0, data0 = 1, succ i j, succ j k, fib i fi, fib j fj, plus fi fj fk)).
constraints:
~(>)[2]
~fib[2]
~plus[2]
~succ[2]
~(arg1[2,0] & k[2,0])
~(arg2[2,1] & fk[2,1])
~(data0[2,2] & data0[2,3])
~(fi[2,6] & fi[2,8])
~(fj[2,7] & fj[2,8])
~(fk[2,1] & fk[2,8])
~(i[2,4] & i[2,6])
~(j[2,4] & j[2,5])
~(j[2,4] & j[2,7])
~(j[2,5] & j[2,7])
~(k[2,0] & k[2,2])
~(k[2,0] & k[2,5])
~(k[2,2] & k[2,5])
(~k[2,2] & ~data0[2,2])
(data0[2,2] | data0[2,3])
(fi[2,6] | fi[2,8])
(fj[2,7] | fj[2,8])
(fk[2,1] | fk[2,8])
(i[2,4] | i[2,6])
(j[2,4] | (j[2,5] | j[2,7]))
(k[2,0] | (k[2,2] | k[2,5]))
((fi[2,8] & (~fj[2,8] & ~fk[2,8])) | ((~fi[2,8] & (fj[2,8] & ~fk[2,8])) | ((~fi[2,8] & (~fj[2,8] & fk[2,8])) | (~fi[2,8] & (~fj[2,8] & ~fk[2,8])))))
((i[2,4] & ~j[2,4]) | ((~i[2,4] & j[2,4]) | (~i[2,4] & ~j[2,4])))
((j[2,5] & ~k[2,5]) | ((~j[2,5] & k[2,5]) | (~j[2,5] & ~k[2,5])))
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg1[] <-> arg1[2])
(arg1[0] <-> arg1[0,0])
(arg1[1] <-> arg1[1,0])
(arg1[2] <-> arg1[2,0])
(arg2[] <-> arg2[0])
(arg2[] <-> arg2[1])
(arg2[] <-> arg2[2])
(arg2[0] <-> arg2[0,1])
(arg2[1] <-> arg2[1,1])
(arg2[2] <-> arg2[2,1])
(fi[2,6] <-> arg2[])
(fj[2,7] <-> arg2[])
(i[2,6] <-> arg1[])
(j[2,7] <-> arg1[])
1
-}

fib = rget $ (procedure @'[ 'In, 'Out ] fibIO) :& (procedure @'[ 'Out, 'Out ] fibOO) :& RNil
  where
    fibIO = memo $ \arg1 -> choose . Logic.observeAll $ do
      -- solution: arg2[] arg2[0] arg2[0,1] arg2[1] arg2[1,1] arg2[2] arg2[2,1] data0[2,3] fi[2,6] fj[2,7] fk[2,8] i[2,4] j[2,5] k[2,0]
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
      -- solution: arg1[] arg1[0] arg1[0,0] arg1[1] arg1[1,0] arg1[2] arg1[2,0] arg2[] arg2[0] arg2[0,1] arg2[1] arg2[1,1] arg2[2] arg2[2,1] data0[2,3] fi[2,6] fj[2,7] fk[2,8] i[2,6] j[2,7] k[2,5]
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
      -- solution: carg3[] carg3[0] carg3[0,1] x_0[0,1]
      -- cost: 4
      (carg3) <- (do
        (x_0,carg3) <- runProcedure @'[ 'Out, 'Out ] fib 
        () <- runProcedure @'[ 'In ] nat x_0
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
      -- solution: data1_1_5[0,3,0,1] x_0[0,2] x_1[0,1,0] x_1[0,1,0,0] x_3[0,0] pred4_1_4(1)
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
      -- solution: carg3[] carg3[0] carg3[0,4] data1_1_5[0] data1_1_5[0,3] data1_1_5[0,3,0,1] x_0[0,2] x_1[0,1,0] x_1[0,1,0,0] x_3[0,0] pred4_1_4(1)
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
(~n[0,4] & ~d[0,4])
(data0[0,2] | data0[0,3])
(data1[0,1] | data1[0,3])
(n'[0,0] | n'[0,3])
((d[0,1] & ~data1[0,1]) | (~d[0,1] & ~data1[0,1]))
((n'[0,0] & ~n[0,0]) | ((~n'[0,0] & n[0,0]) | (~n'[0,0] & ~n[0,0])))
(d[] <-> d[0])
(d[0] <-> (d[0,1] | d[0,4]))
(data0[0,3] <-> n'[0,3])
(n[] <-> n[0])
(n[0] <-> (n[0,0] | n[0,4]))
1
-}

nontrivialDivisor = rget $ (procedure @'[ 'In, 'In ] nontrivialDivisorII) :& (procedure @'[ 'In, 'Out ] nontrivialDivisorIO) :& RNil
  where
    nontrivialDivisorII = \n d -> Logic.once $ do
      -- solution: data0[0,2] data1[0,3] n'[0,0]
      -- cost: 4
      () <- (do
        data0 <- pure 2
        () <- runProcedure @'[ 'In, 'In ] multiple n d
        (OneTuple (n')) <- runProcedure @'[ 'Out, 'In ] succ n
        data1 <- pure [data0..n']
        () <- runProcedure @'[ 'In, 'In ] elem d data1
        pure ()
       )
      pure ()
    
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
factor arg1 arg2 arg3 :- ((arg1 = n0, n0 = n, arg2 = p1:ps2, p1 = p, ps2 = ps, arg3 = f, if (timesInt p3 p4 pp, p3 = p, p4 = p, (>) pp n) then (f = n5, n5 = n) else (if (divMod n p d data0, data0 = 0) then (((f = p6, p6 = p); (factor d data1 f, data1 = p7:ps8, p7 = p, ps8 = ps))) else (factor n ps f)))).
constraints:
d[0,6,2,0,0]
data0[0,6,2,0]
p3[0,6]
p4[0,6]
pp[0,6]
~(>)[0,6,0]
~d[0,6,2,0,1,0]
~divMod[0,6,2,0,0]
~factor[0,6,2,0,1,0,1]
~factor[0,6,2,0,2]
~n[0,6,0,3]
~n[0,6,1,1]
~n[0,6,2]
~n[0,6,2,0,0,0]
~n[0,6,2,0,2]
~p[0,6,2]
~p[0,6,2,0]
~p[0,6,2,0,0,0]
~p[0,6,2,0,1,0]
~ps[0,6,2]
~ps[0,6,2,0,1,0]
~timesInt[0,6,0]
~(arg1[0,0] & n0[0,0])
~(arg2[0,2] & p1[0,2])
~(arg3[0,5] & f[0,5])
~(data0[0,6,2,0,0,0] & data0[0,6,2,0,0,1])
~(data1[0,6,2,0,1,0,1,0] & data1[0,6,2,0,1,0,1,1])
~(data1[0,6,2,0,1,0,1,1] & p7[0,6,2,0,1,0,1,1])
~(f[0,5] & f[0,6])
~(f[0,6,1,0] & n5[0,6,1,0])
~(f[0,6,2,0,1,0,0,0] & p6[0,6,2,0,1,0,0,0])
~(n[0,1] & n[0,6])
~(n0[0,0] & n0[0,1])
~(n0[0,1] & n[0,1])
~(n5[0,6,1,0] & n5[0,6,1,1])
~(n5[0,6,1,1] & n[0,6,1,1])
~(p[0,3] & p[0,6])
~(p[0,6,0,1] & p[0,6,0,2])
~(p1[0,2] & p1[0,3])
~(p1[0,3] & p[0,3])
~(p3[0,6,0,0] & p3[0,6,0,1])
~(p3[0,6,0,1] & p[0,6,0,1])
~(p4[0,6,0,0] & p4[0,6,0,2])
~(p4[0,6,0,2] & p[0,6,0,2])
~(p6[0,6,2,0,1,0,0,0] & p6[0,6,2,0,1,0,0,1])
~(p6[0,6,2,0,1,0,0,1] & p[0,6,2,0,1,0,0,1])
~(p7[0,6,2,0,1,0,1,1] & p7[0,6,2,0,1,0,1,2])
~(p7[0,6,2,0,1,0,1,2] & p[0,6,2,0,1,0,1,2])
~(pp[0,6,0,0] & pp[0,6,0,3])
~(ps[0,4] & ps[0,6])
~(ps2[0,2] & ps2[0,4])
~(ps2[0,4] & ps[0,4])
~(ps8[0,6,2,0,1,0,1,1] & ps8[0,6,2,0,1,0,1,3])
~(ps8[0,6,2,0,1,0,1,3] & ps[0,6,2,0,1,0,1,3])
~(p[0,6,0,1] | p[0,6,0,2])
(~pp[0,6,0,3] & ~n[0,6,0,3])
(data0[0,6,2,0,0,0] | data0[0,6,2,0,0,1])
(data1[0,6,2,0,1,0,1,0] | data1[0,6,2,0,1,0,1,1])
(f[0,5] | f[0,6])
(n[0,1] | n[0,6])
(n0[0,0] | n0[0,1])
(n5[0,6,1,0] | n5[0,6,1,1])
(p[0,3] | p[0,6])
(p1[0,2] | p1[0,3])
(p3[0,6,0,0] | p3[0,6,0,1])
(p4[0,6,0,0] | p4[0,6,0,2])
(p6[0,6,2,0,1,0,0,0] | p6[0,6,2,0,1,0,0,1])
(p7[0,6,2,0,1,0,1,1] | p7[0,6,2,0,1,0,1,2])
(pp[0,6,0,0] | pp[0,6,0,3])
(ps[0,4] | ps[0,6])
(ps2[0,2] | ps2[0,4])
(ps8[0,6,2,0,1,0,1,1] | ps8[0,6,2,0,1,0,1,3])
((p3[0,6,0,0] & (~p4[0,6,0,0] & ~pp[0,6,0,0])) | ((~p3[0,6,0,0] & (p4[0,6,0,0] & ~pp[0,6,0,0])) | ((~p3[0,6,0,0] & (~p4[0,6,0,0] & pp[0,6,0,0])) | (~p3[0,6,0,0] & (~p4[0,6,0,0] & ~pp[0,6,0,0])))))
((~n[0,6,2,0,0,0] & (~p[0,6,2,0,0,0] & (d[0,6,2,0,0,0] & data0[0,6,2,0,0,0]))) | ((~n[0,6,2,0,0,0] & (~p[0,6,2,0,0,0] & (d[0,6,2,0,0,0] & ~data0[0,6,2,0,0,0]))) | ((~n[0,6,2,0,0,0] & (~p[0,6,2,0,0,0] & (~d[0,6,2,0,0,0] & data0[0,6,2,0,0,0]))) | (~n[0,6,2,0,0,0] & (~p[0,6,2,0,0,0] & (~d[0,6,2,0,0,0] & ~data0[0,6,2,0,0,0]))))))
((>)[0] <-> (>)[0,6])
((>)[0,6] <-> (>)[0,6,0])
(arg1[] <-> arg1[0])
(arg1[0] <-> arg1[0,0])
(arg2[] <-> arg2[0])
(arg2[0] <-> arg2[0,2])
(arg3[] <-> arg3[0])
(arg3[0] <-> arg3[0,5])
(d[0,6,2,0,0] <-> d[0,6,2,0,0,0])
(d[0,6,2,0,1,0] <-> d[0,6,2,0,1,0,1])
(d[0,6,2,0,1,0,1] <-> d[0,6,2,0,1,0,1,0])
(d[0,6,2,0,1,0,1,0] <-> arg1[])
(data0[0] <-> data0[0,6])
(data0[0,6] <-> data0[0,6,2])
(data0[0,6,2] <-> data0[0,6,2,0])
(data1[0,6,2,0,1,0,1,0] <-> arg2[])
(divMod[0] <-> divMod[0,6])
(divMod[0,6] <-> divMod[0,6,2])
(divMod[0,6,2] <-> divMod[0,6,2,0])
(divMod[0,6,2,0] <-> divMod[0,6,2,0,0])
(f[0,6] <-> (f[0,6,1] | f[0,6,2]))
(f[0,6,1] <-> f[0,6,1,0])
(f[0,6,1] <-> f[0,6,2])
(f[0,6,2] <-> f[0,6,2,0])
(f[0,6,2,0] <-> (f[0,6,2,0,1] | f[0,6,2,0,2]))
(f[0,6,2,0,1] <-> f[0,6,2,0,1,0])
(f[0,6,2,0,1] <-> f[0,6,2,0,2])
(f[0,6,2,0,1,0] <-> f[0,6,2,0,1,0,0])
(f[0,6,2,0,1,0] <-> f[0,6,2,0,1,0,1])
(f[0,6,2,0,1,0,0] <-> f[0,6,2,0,1,0,0,0])
(f[0,6,2,0,1,0,1] <-> f[0,6,2,0,1,0,1,0])
(f[0,6,2,0,1,0,1,0] <-> arg3[])
(f[0,6,2,0,2] <-> f[0,6,2,0,2,0])
(f[0,6,2,0,2,0] <-> arg3[])
(factor[0] <-> factor[0,6])
(factor[0,6] <-> factor[0,6,2])
(factor[0,6,2] <-> factor[0,6,2,0])
(factor[0,6,2,0] <-> (factor[0,6,2,0,1] | factor[0,6,2,0,2]))
(factor[0,6,2,0,1] <-> factor[0,6,2,0,1,0])
(n[0,6] <-> n[0,6,2])
(n[0,6,2] <-> n[0,6,2,0])
(n[0,6,2,0] <-> n[0,6,2,0,2])
(n[0,6,2,0,2] <-> n[0,6,2,0,2,0])
(n[0,6,2,0,2,0] <-> arg1[])
(p[0,6] <-> p[0,6,2])
(p[0,6,2] <-> p[0,6,2,0])
(p[0,6,2,0,1,0] <-> p[0,6,2,0,1,0,0])
(p[0,6,2,0,1,0] <-> p[0,6,2,0,1,0,1])
(p[0,6,2,0,1,0,0] <-> p[0,6,2,0,1,0,0,1])
(p[0,6,2,0,1,0,1] <-> p[0,6,2,0,1,0,1,2])
(p1[0,2] <-> ps2[0,2])
(p3[0] <-> p3[0,6])
(p4[0] <-> p4[0,6])
(p7[0,6,2,0,1,0,1,1] <-> ps8[0,6,2,0,1,0,1,1])
(pp[0] <-> pp[0,6])
(ps[0,6] <-> ps[0,6,2])
(ps[0,6,2] <-> ps[0,6,2,0])
(ps[0,6,2,0] <-> (ps[0,6,2,0,1] | ps[0,6,2,0,2]))
(ps[0,6,2,0,1] <-> ps[0,6,2,0,1,0])
(ps[0,6,2,0,1] <-> ps[0,6,2,0,2])
(ps[0,6,2,0,1,0] <-> ps[0,6,2,0,1,0,1])
(ps[0,6,2,0,1,0,1] <-> ps[0,6,2,0,1,0,1,3])
(ps[0,6,2,0,2] <-> ps[0,6,2,0,2,0])
(ps[0,6,2,0,2,0] <-> arg2[])
(timesInt[0] <-> timesInt[0,6])
(timesInt[0,6] <-> timesInt[0,6,0])
1
-}

factor = rget $ (procedure @'[ 'In, 'In, 'In ] factorIII) :& (procedure @'[ 'In, 'In, 'Out ] factorIIO) :& RNil
  where
    factorIII = \arg1 arg2 arg3 -> Logic.once $ do
      -- solution: d[0,6,2,0,0] d[0,6,2,0,0,0] data0[0] data0[0,6] data0[0,6,2] data0[0,6,2,0] data0[0,6,2,0,0,1] data1[0,6,2,0,1,0,1,1] f[0,5] n[0,1] n0[0,0] n5[0,6,1,0] p[0,3] p1[0,2] p3[0] p3[0,6] p3[0,6,0,1] p4[0] p4[0,6] p4[0,6,0,2] p6[0,6,2,0,1,0,0,0] p7[0,6,2,0,1,0,1,2] pp[0] pp[0,6] pp[0,6,0,0] ps[0,4] ps2[0,2] ps8[0,6,2,0,1,0,1,3]
      -- cost: 7
      () <- (do
        n0 <- pure arg1
        (p1:ps2) <- pure arg2
        f <- pure arg3
        n <- pure n0
        p <- pure p1
        ps <- pure ps2
        () <- Logic.ifte ((do
          p3 <- pure p
          p4 <- pure p
          (OneTuple (pp)) <- runProcedure @'[ 'In, 'In, 'Out ] timesInt p3 p4
          guard $ (>) pp n
          pure ()
         )) (\() -> (do
          n5 <- pure f
          guard $ n5 == n
          pure ()
         )) ((do
          () <- Logic.ifte ((do
            data0 <- pure 0
            (OneTuple (d)) <- runProcedure @'[ 'In, 'In, 'Out, 'In ] divMod n p data0
            pure (d)
           )) (\(d) -> (do
            () <- (do
              p6 <- pure f
              guard $ p6 == p
              pure ()
             ) <|> (do
              p7 <- pure p
              ps8 <- pure ps
              data1 <- pure (p7:ps8)
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
    
    factorIIO = \arg1 arg2 -> do
      -- solution: arg3[] arg3[0] arg3[0,5] d[0,6,2,0,0] d[0,6,2,0,0,0] data0[0] data0[0,6] data0[0,6,2] data0[0,6,2,0] data0[0,6,2,0,0,1] data1[0,6,2,0,1,0,1,1] f[0,6] f[0,6,1] f[0,6,1,0] f[0,6,2] f[0,6,2,0] f[0,6,2,0,1] f[0,6,2,0,1,0] f[0,6,2,0,1,0,0] f[0,6,2,0,1,0,0,0] f[0,6,2,0,1,0,1] f[0,6,2,0,1,0,1,0] f[0,6,2,0,2] f[0,6,2,0,2,0] n[0,1] n0[0,0] n5[0,6,1,1] p[0,3] p1[0,2] p3[0] p3[0,6] p3[0,6,0,1] p4[0] p4[0,6] p4[0,6,0,2] p6[0,6,2,0,1,0,0,1] p7[0,6,2,0,1,0,1,2] pp[0] pp[0,6] pp[0,6,0,0] ps[0,4] ps2[0,2] ps8[0,6,2,0,1,0,1,3]
      -- cost: 9
      (arg3) <- (do
        n0 <- pure arg1
        (p1:ps2) <- pure arg2
        n <- pure n0
        p <- pure p1
        ps <- pure ps2
        (f) <- Logic.ifte ((do
          p3 <- pure p
          p4 <- pure p
          (OneTuple (pp)) <- runProcedure @'[ 'In, 'In, 'Out ] timesInt p3 p4
          guard $ (>) pp n
          pure ()
         )) (\() -> (do
          n5 <- pure n
          f <- pure n5
          pure (f)
         )) ((do
          (f) <- Logic.ifte ((do
            data0 <- pure 0
            (OneTuple (d)) <- runProcedure @'[ 'In, 'In, 'Out, 'In ] divMod n p data0
            pure (d)
           )) (\(d) -> (do
            (f) <- (do
              p6 <- pure p
              f <- pure p6
              pure (f)
             ) <|> (do
              p7 <- pure p
              ps8 <- pure ps
              data1 <- pure (p7:ps8)
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
        arg3 <- pure f
        pure (arg3)
       )
      pure (OneTuple (arg3))
    
{- prime/1
prime arg1 :- ((arg1 = 2); (arg1 = p, oddNat p, (>) p data0, data0 = 2, observeAll pred1 primes, (pred1 curry1 :- (prime curry1)), if (factor p primes d, (/=) p d) then (empty) else ())).
constraints:
d[1,6]
~(/=)[1,6,0]
~(>)[1]
~curry1[1]
~empty[1,6,1]
~factor[1,6,0]
~observeAll[1]
~oddNat[1]
~p[1,6]
~pred1[1,4]
~prime[1,5,0]
~primes[1,6]
~primes[1,6,0,0]
~(arg1[1,0] & p[1,0])
~(d[1,6,0,0] & d[1,6,0,1])
~(data0[1,2] & data0[1,3])
~(p[1,0] & p[1,1])
~(p[1,0] & p[1,2])
~(p[1,0] & p[1,6])
~(p[1,1] & p[1,2])
~(p[1,1] & p[1,6])
~(p[1,2] & p[1,6])
~(p[1,6,0,0] & p[1,6,0,1])
~(primes[1,4] & primes[1,6])
~(p[1,6,0,0] | p[1,6,0,1])
(~p[1,2] & ~data0[1,2])
(~p[1,6,0,1] & ~d[1,6,0,1])
(~pred1[1,4] & (pred1(1) & primes[1,4]))
(d[1,6,0,0] | d[1,6,0,1])
(data0[1,2] | data0[1,3])
(p[1,0] | (p[1,1] | (p[1,2] | p[1,6])))
(p[1,1] | ~p[1,1])
(primes[1,4] | primes[1,6])
((~p[1,6,0,0] & (~primes[1,6,0,0] & d[1,6,0,0])) | (~p[1,6,0,0] & (~primes[1,6,0,0] & ~d[1,6,0,0])))
((/=)[1] <-> (/=)[1,6])
((/=)[1,6] <-> (/=)[1,6,0])
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg1[0] <-> arg1[0,0])
(arg1[1] <-> arg1[1,0])
(curry1[1,5,0] <-> curry1[1,5,0,0])
(curry1[1,5,0,0] <-> arg1[])
(d[1] <-> d[1,6])
(empty[1] <-> empty[1,6])
(empty[1,6] <-> empty[1,6,1])
(factor[1] <-> factor[1,6])
(factor[1,6] <-> factor[1,6,0])
(prime[1] <-> prime[1,5])
(pred1(1) <-> curry1[1,5,0])
1
-}

prime = rget $ (procedure @'[ 'Out ] primeO) :& RNil
  where
    primeO = choose . Logic.observeAll $ do
      -- solution: arg1[] arg1[0] arg1[0,0] arg1[1] arg1[1,0] curry1[1,5,0] curry1[1,5,0,0] d[1] d[1,6] d[1,6,0,0] data0[1,3] p[1,1] primes[1,4] pred1(1)
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
      -- solution: x_0[0,0] x_0[0,1,0] x_0[0,1,0,0] pred1_1(1)
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
      -- solution: x_0[0,0] x_0[0,1,0] x_0[0,1,0,0] pred1_1(1)
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
((x[0,0] & ~data2[0,0]) | (~x[0,0] & ~data2[0,0]))
((x[0,8] & (~y[0,8] & ~n[0,8])) | ((~x[0,8] & (y[0,8] & ~n[0,8])) | ((~x[0,8] & (~y[0,8] & n[0,8])) | (~x[0,8] & (~y[0,8] & ~n[0,8])))))
((y[0,4] & ~data5[0,4]) | (~y[0,4] & ~data5[0,4]))
(data0[0,3] <-> data1[0,3])
(data3[0,7] <-> data4[0,7])
(n[] <-> n[0])
(n[0] <-> (n[0,8] | n[0,9]))
1
-}
--mode ordering failure, cyclic dependency: [10] reverse::I s0::O s1::I -> [11] s0::I = s::O -> [12] s1::O = s::I
--mode ordering failure, cyclic dependency: [10] reverse::I s0::O s1::I -> [11] s0::I = s::O -> [12] s1::O = s::I
--mode ordering failure, cyclic dependency: [10] reverse::I s0::O s1::I -> [11] s0::I = s::O -> [12] s1::O = s::I
--mode ordering failure, cyclic dependency: [10] reverse::I s0::O s1::I -> [11] s0::I = s::O -> [12] s1::O = s::I
--mode ordering failure, cyclic dependency: [10] reverse::I s0::I s1::O -> [12] s1::I = s::O -> [11] s0::O = s::I
--mode ordering failure, cyclic dependency: [10] reverse::I s0::I s1::O -> [12] s1::I = s::O -> [11] s0::O = s::I
--mode ordering failure, cyclic dependency: [10] reverse::I s0::I s1::O -> [12] s1::I = s::O -> [11] s0::O = s::I
--mode ordering failure, cyclic dependency: [10] reverse::I s0::I s1::O -> [12] s1::I = s::O -> [11] s0::O = s::I
--mode ordering failure, cyclic dependency: [10] reverse::I s0::O s1::I -> [11] s0::I = s::O -> [12] s1::O = s::I
--mode ordering failure, cyclic dependency: [10] reverse::I s0::O s1::I -> [11] s0::I = s::O -> [12] s1::O = s::I
--mode ordering failure, cyclic dependency: [10] reverse::I s0::O s1::I -> [11] s0::I = s::O -> [12] s1::O = s::I
--mode ordering failure, cyclic dependency: [10] reverse::I s0::I s1::O -> [12] s1::I = s::O -> [11] s0::O = s::I
--mode ordering failure, cyclic dependency: [10] reverse::I s0::I s1::O -> [12] s1::I = s::O -> [11] s0::O = s::I
--mode ordering failure, cyclic dependency: [10] reverse::I s0::I s1::O -> [12] s1::I = s::O -> [11] s0::O = s::I
euler4 = rget $ (procedure @'[ 'In ] euler4I) :& (procedure @'[ 'Out ] euler4O) :& RNil
  where
    euler4I = \n -> Logic.once $ do
      -- solution: data0[0,1] data1[0,2] data2[0,3] data3[0,5] data4[0,6] data5[0,7] s[0,9] s0[0,11] s1[0,12] x[0,8] y[0,4]
      -- cost: 8
      () <- (do
        data0 <- pure 10
        data1 <- pure 99
        data2 <- pure [data0..data1]
        data3 <- pure 10
        data4 <- pure 99
        data5 <- pure [data3..data4]
        (OneTuple (y)) <- runProcedure @'[ 'Out, 'In ] elem data5
        (OneTuple (s)) <- runProcedure @'[ 'In, 'Out ] show n
        s0 <- pure s
        s1 <- pure s
        () <- runProcedure @'[ 'In, 'In ] reverse s0 s1
        (OneTuple (x)) <- runProcedure @'[ 'Out, 'In, 'In ] timesInt y n
        () <- runProcedure @'[ 'In, 'In ] elem x data2
        pure ()
       )
      pure ()
    
    euler4O = do
      -- solution: data0[0,1] data1[0,2] data2[0,3] data3[0,5] data4[0,6] data5[0,7] n[] n[0] n[0,8] s[0,9] s0[0,11] s1[0,12] x[0,0] y[0,4]
      -- cost: 9
      (n) <- (do
        data0 <- pure 10
        data1 <- pure 99
        data2 <- pure [data0..data1]
        data3 <- pure 10
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
      -- solution: x_0[0,0] x_0[0,1,0] x_0[0,1,0,0] pred1_1(1)
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
      -- solution: data0[0,2] data2[0,4] data3[0,5] data4[0,6]
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
    