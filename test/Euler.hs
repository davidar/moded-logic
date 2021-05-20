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
        data0 <- pure 2
        data1 <- pure 0
        () <- runProcedure @'[ 'In, 'In, 'In ] mod x data0 data1
        pure ()
       )
      pure ()
    
{- elem/2
elem arg1 arg2 :- ((arg2 = x:_, arg1 = x); (arg2 = _:xs, elem x xs, arg1 = x)).
constraints:
x[0,0]
xs[1,0]
~arg2[1,0]
~elem[1]
~(arg1[0,1] & x[0,1])
~(arg1[1,2] & x[1,2])
~(arg2[0,0] & x[0,0])
~(x[0,0] & x[0,1])
~(x[1,1] & x[1,2])
~(xs[1,0] & xs[1,1])
(x[0,0] | x[0,1])
(x[1,1] | x[1,2])
(xs[1,0] | xs[1,1])
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg1[0] <-> arg1[0,1])
(arg1[1] <-> arg1[1,2])
(arg2[] <-> arg2[0])
(arg2[] <-> arg2[1])
(arg2[0] <-> arg2[0,0])
(arg2[1] <-> arg2[1,0])
(x[1,1] <-> arg1[])
(xs[1,1] <-> arg2[])
1
-}

elem = rget $ (procedure @'[ 'In, 'In ] elemII) :& (procedure @'[ 'Out, 'In ] elemOI) :& RNil
  where
    elemII = \arg1 arg2 -> Logic.once $ do
      -- solution: x[0,0] x[1,2] xs[1,0]
      -- cost: 1
      () <- (do
        (x:_) <- pure arg2
        guard $ arg1 == x
        pure ()
       ) <|> (do
        x <- pure arg1
        (_:xs) <- pure arg2
        () <- elemII x xs
        pure ()
       )
      pure ()
    
    elemOI = \arg2 -> do
      -- solution: arg1[] arg1[0] arg1[0,1] arg1[1] arg1[1,2] x[0,0] x[1,1] xs[1,0]
      -- cost: 2
      (arg1) <- (do
        (x:_) <- pure arg2
        arg1 <- pure x
        pure (arg1)
       ) <|> (do
        (_:xs) <- pure arg2
        (OneTuple (x)) <- elemOI xs
        arg1 <- pure x
        pure (arg1)
       )
      pure (OneTuple (arg1))
    
{- elem'/2
elem' xs x :- ((elem x xs)).
constraints:
~elem[0]
((x[0,0] & ~xs[0,0]) | (~x[0,0] & ~xs[0,0]))
(x[] <-> x[0])
(x[0] <-> x[0,0])
(xs[] <-> xs[0])
(xs[0] <-> xs[0,0])
1
-}

elem' = rget $ (procedure @'[ 'In, 'In ] elem'II) :& (procedure @'[ 'In, 'Out ] elem'IO) :& RNil
  where
    elem'II = \xs x -> Logic.once $ do
      -- solution: 
      -- cost: 1
      () <- (do
        () <- runProcedure @'[ 'In, 'In ] elem x xs
        pure ()
       )
      pure ()
    
    elem'IO = \xs -> do
      -- solution: x[] x[0] x[0,0]
      -- cost: 2
      (x) <- (do
        (OneTuple (x)) <- runProcedure @'[ 'Out, 'In ] elem xs
        pure (x)
       )
      pure (OneTuple (x))
    
{- span/4
span arg1 arg2 arg3 arg4 :- ((arg2 = [], arg3 = [], arg4 = []); (arg2 = x:xs, if (p x) then (span p xs yt zs, ys = x0:yt, x0 = x) else (ys = [], zs = x1:xs0, x1 = x, xs0 = xs), arg1 = p, arg3 = ys, arg4 = zs)).
constraints:
~arg1[]
~p[1,1]
~p[1,1,1,0]
~span[1,1,1]
~x[1,1,0,0]
~x[1,1,1,2]
~x[1,1,2]
~(arg1[1,2] & p[1,2])
~(arg2[1,0] & x[1,0])
~(arg3[1,3] & ys[1,3])
~(arg4[1,4] & zs[1,4])
~(p[1,1] & p[1,2])
~(x[1,0] & x[1,1])
~(x0[1,1,1,1] & x0[1,1,1,2])
~(x0[1,1,1,2] & x[1,1,1,2])
~(x1[1,1,2,1] & x1[1,1,2,2])
~(x1[1,1,2,2] & x[1,1,2,2])
~(xs[1,0] & xs[1,1])
~(xs0[1,1,2,1] & xs0[1,1,2,3])
~(xs0[1,1,2,3] & xs[1,1,2,3])
~(ys[1,1] & ys[1,3])
~(ys[1,1,1,1] & x0[1,1,1,1])
~(yt[1,1,1,0] & yt[1,1,1,1])
~(zs[1,1] & zs[1,4])
~(zs[1,1,2,1] & x1[1,1,2,1])
(p[1,1] | p[1,2])
(x[1,0] | x[1,1])
(x0[1,1,1,1] | x0[1,1,1,2])
(x1[1,1,2,1] | x1[1,1,2,2])
(xs[1,0] | xs[1,1])
(xs0[1,1,2,1] | xs0[1,1,2,3])
(ys[1,1] | ys[1,3])
(yt[1,1,1,0] | yt[1,1,1,1])
(zs[1,1] | zs[1,4])
(arg1[] <-> arg1[1])
(arg1[1] <-> arg1[1,2])
(arg2[] <-> arg2[0])
(arg2[] <-> arg2[1])
(arg2[0] <-> arg2[0,0])
(arg2[1] <-> arg2[1,0])
(arg3[] <-> arg3[0])
(arg3[] <-> arg3[1])
(arg3[0] <-> arg3[0,1])
(arg3[1] <-> arg3[1,3])
(arg4[] <-> arg4[0])
(arg4[] <-> arg4[1])
(arg4[0] <-> arg4[0,2])
(arg4[1] <-> arg4[1,4])
(p[1,1,1,0] <-> arg1[])
(span[1] <-> span[1,1])
(span[1,1] <-> span[1,1,1])
(x[1,0] <-> xs[1,0])
(x[1,1] <-> x[1,1,2])
(x[1,1,0,0] <-> arg1(1))
(x[1,1,0,0] <-> p(1))
(x[1,1,2] <-> x[1,1,2,2])
(x0[1,1,1,1] <-> yt[1,1,1,1])
(x1[1,1,2,1] <-> xs0[1,1,2,1])
(xs[1,1] <-> (xs[1,1,1] | xs[1,1,2]))
(xs[1,1,1] <-> xs[1,1,1,0])
(xs[1,1,1] <-> xs[1,1,2])
(xs[1,1,1,0] <-> arg2[])
(xs[1,1,2] <-> xs[1,1,2,3])
(ys[1,1] <-> (ys[1,1,1] | ys[1,1,2]))
(ys[1,1,1] <-> ys[1,1,1,1])
(ys[1,1,1] <-> ys[1,1,2])
(ys[1,1,2] <-> ys[1,1,2,0])
(yt[1,1,1,0] <-> arg3[])
(zs[1,1] <-> (zs[1,1,1] | zs[1,1,2]))
(zs[1,1,1] <-> zs[1,1,1,0])
(zs[1,1,1] <-> zs[1,1,2])
(zs[1,1,1,0] <-> arg4[])
(zs[1,1,2] <-> zs[1,1,2,1])
1
-}

span = rget $ (procedure @'[ 'PredMode '[ 'In ], 'In, 'In, 'In ] spanP1IIII) :& (procedure @'[ 'PredMode '[ 'In ], 'In, 'In, 'Out ] spanP1IIIO) :& (procedure @'[ 'PredMode '[ 'In ], 'In, 'Out, 'In ] spanP1IIOI) :& (procedure @'[ 'PredMode '[ 'In ], 'In, 'Out, 'Out ] spanP1IIOO) :& RNil
  where
    spanP1IIII = \arg1 arg2 arg3 arg4 -> Logic.once $ do
      -- solution: p[1,2] x[1,0] x0[1,1,1,1] x1[1,1,2,1] xs[1,0] xs0[1,1,2,1] ys[1,3] yt[1,1,1,1] zs[1,4]
      -- cost: 2
      () <- (do
        guard $ arg2 == []
        guard $ arg3 == []
        guard $ arg4 == []
        pure ()
       ) <|> (do
        p <- pure arg1
        (x:xs) <- pure arg2
        ys <- pure arg3
        zs <- pure arg4
        () <- Logic.ifte ((do
          () <- runProcedure @'[ 'In ] p x
          pure ()
         )) (\() -> (do
          (x0:yt) <- pure ys
          guard $ x0 == x
          () <- spanP1IIII p xs yt zs
          pure ()
         )) ((do
          guard $ ys == []
          (x1:xs0) <- pure zs
          guard $ x1 == x
          guard $ xs0 == xs
          pure ()
         ))
        pure ()
       )
      pure ()
    
    spanP1IIIO = \arg1 arg2 arg3 -> do
      -- solution: arg4[] arg4[0] arg4[0,2] arg4[1] arg4[1,4] p[1,2] x[1,0] x0[1,1,1,1] x1[1,1,2,2] xs[1,0] xs0[1,1,2,3] ys[1,3] yt[1,1,1,1] zs[1,1] zs[1,1,1] zs[1,1,1,0] zs[1,1,2] zs[1,1,2,1]
      -- cost: 3
      (arg4) <- (do
        guard $ arg2 == []
        guard $ arg3 == []
        arg4 <- pure []
        pure (arg4)
       ) <|> (do
        p <- pure arg1
        (x:xs) <- pure arg2
        ys <- pure arg3
        (zs) <- Logic.ifte ((do
          () <- runProcedure @'[ 'In ] p x
          pure ()
         )) (\() -> (do
          (x0:yt) <- pure ys
          guard $ x0 == x
          (OneTuple (zs)) <- spanP1IIIO p xs yt
          pure (zs)
         )) ((do
          x1 <- pure x
          xs0 <- pure xs
          guard $ ys == []
          zs <- pure (x1:xs0)
          pure (zs)
         ))
        arg4 <- pure zs
        pure (arg4)
       )
      pure (OneTuple (arg4))
    
    spanP1IIOI = \arg1 arg2 arg4 -> do
      -- solution: arg3[] arg3[0] arg3[0,1] arg3[1] arg3[1,3] p[1,2] x[1,0] x0[1,1,1,2] x1[1,1,2,1] xs[1,0] xs0[1,1,2,1] ys[1,1] ys[1,1,1] ys[1,1,1,1] ys[1,1,2] ys[1,1,2,0] yt[1,1,1,0] zs[1,4]
      -- cost: 3
      (arg3) <- (do
        guard $ arg2 == []
        arg3 <- pure []
        guard $ arg4 == []
        pure (arg3)
       ) <|> (do
        p <- pure arg1
        (x:xs) <- pure arg2
        zs <- pure arg4
        (ys) <- Logic.ifte ((do
          () <- runProcedure @'[ 'In ] p x
          pure ()
         )) (\() -> (do
          x0 <- pure x
          (OneTuple (yt)) <- spanP1IIOI p xs zs
          ys <- pure (x0:yt)
          pure (ys)
         )) ((do
          ys <- pure []
          (x1:xs0) <- pure zs
          guard $ x1 == x
          guard $ xs0 == xs
          pure (ys)
         ))
        arg3 <- pure ys
        pure (arg3)
       )
      pure (OneTuple (arg3))
    
    spanP1IIOO = \arg1 arg2 -> do
      -- solution: arg3[] arg3[0] arg3[0,1] arg3[1] arg3[1,3] arg4[] arg4[0] arg4[0,2] arg4[1] arg4[1,4] p[1,2] x[1,0] x0[1,1,1,2] x1[1,1,2,2] xs[1,0] xs0[1,1,2,3] ys[1,1] ys[1,1,1] ys[1,1,1,1] ys[1,1,2] ys[1,1,2,0] yt[1,1,1,0] zs[1,1] zs[1,1,1] zs[1,1,1,0] zs[1,1,2] zs[1,1,2,1]
      -- cost: 4
      (arg3,arg4) <- (do
        guard $ arg2 == []
        arg3 <- pure []
        arg4 <- pure []
        pure (arg3,arg4)
       ) <|> (do
        p <- pure arg1
        (x:xs) <- pure arg2
        (ys,zs) <- Logic.ifte ((do
          () <- runProcedure @'[ 'In ] p x
          pure ()
         )) (\() -> (do
          x0 <- pure x
          (yt,zs) <- spanP1IIOO p xs
          ys <- pure (x0:yt)
          pure (ys,zs)
         )) ((do
          x1 <- pure x
          xs0 <- pure xs
          ys <- pure []
          zs <- pure (x1:xs0)
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
reverseDL arg1 arg2 arg3 :- ((arg1 = [], arg2 = xs, arg3 = xs); (arg1 = h:t, reverseDL t data0 r, data0 = h0:rest, h0 = h, arg2 = rest, arg3 = r)).
constraints:
~reverseDL[1]
~(arg1[1,0] & h[1,0])
~(arg2[0,1] & xs[0,1])
~(arg2[1,4] & rest[1,4])
~(arg3[0,2] & xs[0,2])
~(arg3[1,5] & r[1,5])
~(data0[1,1] & data0[1,2])
~(data0[1,2] & h0[1,2])
~(h[1,0] & h[1,3])
~(h0[1,2] & h0[1,3])
~(h0[1,3] & h[1,3])
~(r[1,1] & r[1,5])
~(rest[1,2] & rest[1,4])
~(t[1,0] & t[1,1])
~(xs[0,1] & xs[0,2])
(data0[1,1] | data0[1,2])
(h[1,0] | h[1,3])
(h0[1,2] | h0[1,3])
(r[1,1] | r[1,5])
(rest[1,2] | rest[1,4])
(t[1,0] | t[1,1])
(xs[0,1] | xs[0,2])
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg1[0] <-> arg1[0,0])
(arg1[1] <-> arg1[1,0])
(arg2[] <-> arg2[0])
(arg2[] <-> arg2[1])
(arg2[0] <-> arg2[0,1])
(arg2[1] <-> arg2[1,4])
(arg3[] <-> arg3[0])
(arg3[] <-> arg3[1])
(arg3[0] <-> arg3[0,2])
(arg3[1] <-> arg3[1,5])
(data0[1,1] <-> arg2[])
(h[1,0] <-> t[1,0])
(h0[1,2] <-> rest[1,2])
(r[1,1] <-> arg3[])
(t[1,1] <-> arg1[])
1
-}

reverseDL = rget $ (procedure @'[ 'In, 'In, 'In ] reverseDLIII) :& (procedure @'[ 'In, 'In, 'Out ] reverseDLIIO) :& (procedure @'[ 'In, 'Out, 'In ] reverseDLIOI) :& (procedure @'[ 'Out, 'Out, 'In ] reverseDLOOI) :& RNil
  where
    reverseDLIII = \arg1 arg2 arg3 -> Logic.once $ do
      -- solution: data0[1,2] h[1,0] h0[1,3] r[1,5] rest[1,4] t[1,0] xs[0,1]
      -- cost: 1
      () <- (do
        guard $ arg1 == []
        xs <- pure arg2
        guard $ arg3 == xs
        pure ()
       ) <|> (do
        (h:t) <- pure arg1
        rest <- pure arg2
        r <- pure arg3
        h0 <- pure h
        data0 <- pure (h0:rest)
        () <- reverseDLIII t data0 r
        pure ()
       )
      pure ()
    
    reverseDLIIO = \arg1 arg2 -> do
      -- solution: arg3[] arg3[0] arg3[0,2] arg3[1] arg3[1,5] data0[1,2] h[1,0] h0[1,3] r[1,1] rest[1,4] t[1,0] xs[0,1]
      -- cost: 2
      (arg3) <- (do
        guard $ arg1 == []
        xs <- pure arg2
        arg3 <- pure xs
        pure (arg3)
       ) <|> (do
        (h:t) <- pure arg1
        rest <- pure arg2
        h0 <- pure h
        data0 <- pure (h0:rest)
        (OneTuple (r)) <- reverseDLIIO t data0
        arg3 <- pure r
        pure (arg3)
       )
      pure (OneTuple (arg3))
    
    reverseDLIOI = \arg1 arg3 -> do
      -- solution: arg2[] arg2[0] arg2[0,1] arg2[1] arg2[1,4] data0[1,1] h[1,0] h0[1,2] r[1,5] rest[1,2] t[1,0] xs[0,2]
      -- cost: 2
      (arg2) <- (do
        guard $ arg1 == []
        xs <- pure arg3
        arg2 <- pure xs
        pure (arg2)
       ) <|> (do
        (h:t) <- pure arg1
        r <- pure arg3
        (OneTuple (data0)) <- reverseDLIOI t r
        (h0:rest) <- pure data0
        arg2 <- pure rest
        guard $ h0 == h
        pure (arg2)
       )
      pure (OneTuple (arg2))
    
    reverseDLOOI = \arg3 -> do
      -- solution: arg1[] arg1[0] arg1[0,0] arg1[1] arg1[1,0] arg2[] arg2[0] arg2[0,1] arg2[1] arg2[1,4] data0[1,1] h[1,3] h0[1,2] r[1,5] rest[1,2] t[1,1] xs[0,2]
      -- cost: 3
      (arg1,arg2) <- (do
        arg1 <- pure []
        xs <- pure arg3
        arg2 <- pure xs
        pure (arg1,arg2)
       ) <|> (do
        r <- pure arg3
        (t,data0) <- reverseDLOOI r
        (h0:rest) <- pure data0
        arg2 <- pure rest
        h <- pure h0
        arg1 <- pure (h:t)
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
all arg1 arg2 :- ((arg2 = []); (arg2 = h:t, p h, all p t, arg1 = p)).
constraints:
~all[1]
~arg1[]
~(arg1[1,3] & p[1,3])
~(arg2[1,0] & h[1,0])
~(h[1,0] & h[1,1])
~(p[1,2] & p[1,3])
~(t[1,0] & t[1,2])
(h[1,0] | h[1,1])
(p[1,2] | p[1,3])
(t[1,0] | t[1,2])
(arg1[] <-> arg1[1])
(arg1[1] <-> arg1[1,3])
(arg2[] <-> arg2[0])
(arg2[] <-> arg2[1])
(arg2[0] <-> arg2[0,0])
(arg2[1] <-> arg2[1,0])
(h[1,0] <-> t[1,0])
(h[1,1] <-> arg1(1))
(h[1,1] <-> p(1))
(p[1,2] <-> arg1[])
(t[1,2] <-> arg2[])
1
-}

all = rget $ (procedure @'[ 'PredMode '[ 'In ], 'In ] allP1II) :& (procedure @'[ 'PredMode '[ 'Out ], 'Out ] allP1OO) :& RNil
  where
    allP1II = \arg1 arg2 -> Logic.once $ do
      -- solution: h[1,0] p[1,3] t[1,0]
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
      -- solution: arg2[] arg2[0] arg2[0,0] arg2[1] arg2[1,0] h[1,1] p[1,3] t[1,2]
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
    
{- all'/3
all' arg1 arg2 arg3 :- ((arg2 = []); (arg2 = h:t, p h r, all' p t r, arg1 = p, arg3 = r)).
constraints:
~all'[1]
~arg1[]
~arg3[]
~(arg1[1,3] & p[1,3])
~(arg2[1,0] & h[1,0])
~(arg3[1,4] & r[1,4])
~(h[1,0] & h[1,1])
~(p[1,2] & p[1,3])
~(r[1,1] & r[1,2])
~(r[1,1] & r[1,4])
~(r[1,2] & r[1,4])
~(t[1,0] & t[1,2])
(h[1,0] | h[1,1])
(p[1,2] | p[1,3])
(r[1,1] | (r[1,2] | r[1,4]))
(t[1,0] | t[1,2])
(arg1[] <-> arg1[1])
(arg1[1] <-> arg1[1,3])
(arg2[] <-> arg2[0])
(arg2[] <-> arg2[1])
(arg2[0] <-> arg2[0,0])
(arg2[1] <-> arg2[1,0])
(arg3[] <-> arg3[1])
(arg3[1] <-> arg3[1,4])
(h[1,0] <-> t[1,0])
(h[1,1] <-> arg1(1))
(h[1,1] <-> p(1))
(p[1,2] <-> arg1[])
(r[1,1] <-> arg1(2))
(r[1,1] <-> p(2))
(r[1,2] <-> arg3[])
(t[1,2] <-> arg2[])
1
-}

all' = rget $ (procedure @'[ 'PredMode '[ 'In, 'In ], 'In, 'In ] all'P2IIII) :& (procedure @'[ 'PredMode '[ 'In, 'Out ], 'In, 'In ] all'P2IOII) :& (procedure @'[ 'PredMode '[ 'Out, 'In ], 'Out, 'In ] all'P2OIOI) :& (procedure @'[ 'PredMode '[ 'Out, 'Out ], 'Out, 'In ] all'P2OOOI) :& RNil
  where
    all'P2IIII = \arg1 arg2 arg3 -> Logic.once $ do
      -- solution: h[1,0] p[1,3] r[1,4] t[1,0]
      -- cost: 2
      () <- (do
        guard $ arg2 == []
        pure ()
       ) <|> (do
        p <- pure arg1
        (h:t) <- pure arg2
        r <- pure arg3
        () <- all'P2IIII p t r
        () <- runProcedure @'[ 'In, 'In ] p h r
        pure ()
       )
      pure ()
    
    all'P2IOII = \arg1 arg2 arg3 -> Logic.once $ do
      -- solution: h[1,0] p[1,3] r[1,1] t[1,0]
      -- cost: 3
      () <- (do
        guard $ arg2 == []
        pure ()
       ) <|> (do
        p <- pure arg1
        (h:t) <- pure arg2
        (OneTuple (r)) <- runProcedure @'[ 'In, 'Out ] p h
        guard $ arg3 == r
        () <- all'P2IOII p t r
        pure ()
       )
      pure ()
    
    all'P2OIOI = \arg1 arg3 -> do
      -- solution: arg2[] arg2[0] arg2[0,0] arg2[1] arg2[1,0] h[1,1] p[1,3] r[1,4] t[1,2]
      -- cost: 4
      (arg2) <- (do
        arg2 <- pure []
        pure (arg2)
       ) <|> (do
        p <- pure arg1
        r <- pure arg3
        (OneTuple (t)) <- all'P2OIOI p r
        (OneTuple (h)) <- runProcedure @'[ 'Out, 'In ] p r
        arg2 <- pure (h:t)
        pure (arg2)
       )
      pure (OneTuple (arg2))
    
    all'P2OOOI = \arg1 arg3 -> do
      -- solution: arg2[] arg2[0] arg2[0,0] arg2[1] arg2[1,0] h[1,1] p[1,3] r[1,1] t[1,2]
      -- cost: 5
      (arg2) <- (do
        arg2 <- pure []
        pure (arg2)
       ) <|> (do
        p <- pure arg1
        (h,r) <- runProcedure @'[ 'Out, 'Out ] p 
        guard $ arg3 == r
        (OneTuple (t)) <- all'P2OOOI p r
        arg2 <- pure (h:t)
        pure (arg2)
       )
      pure (OneTuple (arg2))
    
{- multiple/2
multiple y x :- ((mod x y data0, data0 = 0)).
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
    multipleII = \y x -> Logic.once $ do
      -- solution: data0[0,1]
      -- cost: 1
      () <- (do
        data0 <- pure 0
        () <- runProcedure @'[ 'In, 'In, 'In ] mod x y data0
        pure ()
       )
      pure ()
    
{- divisor/2
divisor x y :- ((mod x y data0, data0 = 0)).
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

divisor = rget $ (procedure @'[ 'In, 'In ] divisorII) :& RNil
  where
    divisorII = \x y -> Logic.once $ do
      -- solution: data0[0,1]
      -- cost: 1
      () <- (do
        data0 <- pure 0
        () <- runProcedure @'[ 'In, 'In, 'In ] mod x y data0
        pure ()
       )
      pure ()
    
{- read/2
read s x :- ((show x s)).
constraints:
~show[0]
((x[0,0] & ~s[0,0]) | ((~x[0,0] & s[0,0]) | (~x[0,0] & ~s[0,0])))
(s[] <-> s[0])
(s[0] <-> s[0,0])
(x[] <-> x[0])
(x[0] <-> x[0,0])
1
-}

read = rget $ (procedure @'[ 'In, 'In ] readII) :& (procedure @'[ 'In, 'Out ] readIO) :& (procedure @'[ 'Out, 'In ] readOI) :& RNil
  where
    readII = \s x -> Logic.once $ do
      -- solution: 
      -- cost: 1
      () <- (do
        () <- runProcedure @'[ 'In, 'In ] show x s
        pure ()
       )
      pure ()
    
    readIO = \s -> do
      -- solution: x[] x[0] x[0,0]
      -- cost: 2
      (x) <- (do
        (OneTuple (x)) <- runProcedure @'[ 'Out, 'In ] show s
        pure (x)
       )
      pure (OneTuple (x))
    
    readOI = \x -> do
      -- solution: s[] s[0] s[0,0]
      -- cost: 2
      (s) <- (do
        (OneTuple (s)) <- runProcedure @'[ 'In, 'Out ] show x
        pure (s)
       )
      pure (OneTuple (s))
    
{- id/2
id arg1 arg2 :- ((arg1 = x, arg2 = x)).
constraints:
~(arg1[0,0] & x[0,0])
~(arg2[0,1] & x[0,1])
~(x[0,0] & x[0,1])
(x[0,0] | x[0,1])
(arg1[] <-> arg1[0])
(arg1[0] <-> arg1[0,0])
(arg2[] <-> arg2[0])
(arg2[0] <-> arg2[0,1])
1
-}

id = rget $ (procedure @'[ 'In, 'In ] idII) :& (procedure @'[ 'In, 'Out ] idIO) :& (procedure @'[ 'Out, 'In ] idOI) :& RNil
  where
    idII = \arg1 arg2 -> Logic.once $ do
      -- solution: x[0,0]
      -- cost: 0
      () <- (do
        x <- pure arg1
        guard $ arg2 == x
        pure ()
       )
      pure ()
    
    idIO = \arg1 -> do
      -- solution: arg2[] arg2[0] arg2[0,1] x[0,0]
      -- cost: 0
      (arg2) <- (do
        x <- pure arg1
        arg2 <- pure x
        pure (arg2)
       )
      pure (OneTuple (arg2))
    
    idOI = \arg2 -> do
      -- solution: arg1[] arg1[0] arg1[0,0] x[0,1]
      -- cost: 0
      (arg1) <- (do
        x <- pure arg2
        arg1 <- pure x
        pure (arg1)
       )
      pure (OneTuple (arg1))
    
{- euler1/1
euler1 fresh1 :- ((multiple x_0 fresh1, ((x_0 = 3); (x_0 = 5)), elem' data2 fresh1, data0 = 0, data1 = 999, data2 = .. data0 data1)).
constraints:
~elem'[0]
~multiple[0]
~(data0[0,3] & data0[0,5])
~(data1[0,4] & data1[0,5])
~(data2[0,2] & data2[0,5])
~(data2[0,5] & data0[0,5])
~(fresh1[0,0] & fresh1[0,2])
~(x_0[0,0] & x_0[0,1])
(~x_0[0,0] & ~fresh1[0,0])
(data0[0,3] | data0[0,5])
(data1[0,4] | data1[0,5])
(data2[0,2] | data2[0,5])
(x_0[0,0] | x_0[0,1])
((~data2[0,2] & fresh1[0,2]) | (~data2[0,2] & ~fresh1[0,2]))
(data0[0,5] <-> data1[0,5])
(fresh1[] <-> fresh1[0])
(fresh1[0] <-> (fresh1[0,0] | fresh1[0,2]))
(x_0[0,1] <-> x_0[0,1,0])
(x_0[0,1] <-> x_0[0,1,1])
(x_0[0,1,0] <-> x_0[0,1,0,0])
(x_0[0,1,1] <-> x_0[0,1,1,0])
1
-}

euler1 = rget $ (procedure @'[ 'In ] euler1I) :& (procedure @'[ 'Out ] euler1O) :& RNil
  where
    euler1I = \fresh1 -> choose . nub . Logic.observeAll $ do
      -- solution: data0[0,3] data1[0,4] data2[0,5] x_0[0,1] x_0[0,1,0] x_0[0,1,0,0] x_0[0,1,1] x_0[0,1,1,0]
      -- cost: 2
      () <- (do
        data0 <- pure 0
        data1 <- pure 999
        data2 <- pure [data0..data1]
        (x_0) <- (do
          x_0 <- pure 3
          pure (x_0)
         ) <|> (do
          x_0 <- pure 5
          pure (x_0)
         )
        () <- runProcedure @'[ 'In, 'In ] elem' data2 fresh1
        () <- runProcedure @'[ 'In, 'In ] multiple x_0 fresh1
        pure ()
       )
      pure ()
    
    euler1O = choose . nub . Logic.observeAll $ do
      -- solution: data0[0,3] data1[0,4] data2[0,5] fresh1[] fresh1[0] fresh1[0,2] x_0[0,1] x_0[0,1,0] x_0[0,1,0,0] x_0[0,1,1] x_0[0,1,1,0]
      -- cost: 3
      (fresh1) <- (do
        data0 <- pure 0
        data1 <- pure 999
        data2 <- pure [data0..data1]
        (x_0) <- (do
          x_0 <- pure 3
          pure (x_0)
         ) <|> (do
          x_0 <- pure 5
          pure (x_0)
         )
        (OneTuple (fresh1)) <- runProcedure @'[ 'In, 'Out ] elem' data2
        () <- runProcedure @'[ 'In, 'In ] multiple x_0 fresh1
        pure (fresh1)
       )
      pure (OneTuple (fresh1))
    
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
      -- solution: x_0[0,0] x_0[0,1,0] x_0[0,1,0,0]
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
      -- solution: carg3[] carg3[0] carg3[0,2] x_0[0,0] x_0[0,1,0] x_0[0,1,0,0]
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

fib = rget $ (procedure @'[ 'In, 'Out ] fibIO) :& RNil
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
    
{- fib'/1
fib' fresh1 :- ((nat x_0, fib x_0 fresh1)).
constraints:
~fib[0]
~nat[0]
~(x_0[0,0] & x_0[0,1])
(~x_0[0,1] & fresh1[0,1])
(x_0[0,0] | x_0[0,1])
(x_0[0,0] | ~x_0[0,0])
(fresh1[] <-> fresh1[0])
(fresh1[0] <-> fresh1[0,1])
1
-}

fib' = rget $ (procedure @'[ 'Out ] fib'O) :& RNil
  where
    fib'O = do
      -- solution: fresh1[] fresh1[0] fresh1[0,1] x_0[0,0]
      -- cost: 4
      (fresh1) <- (do
        (OneTuple (x_0)) <- runProcedure @'[ 'Out ] nat 
        (OneTuple (fresh1)) <- runProcedure @'[ 'In, 'Out ] fib x_0
        pure (fresh1)
       )
      pure (OneTuple (fresh1))
    
{- euler2/1
euler2 carg3 :- ((observeAll pred4_1_4 x_3, (pred4_1_4 fresh2_1_4 :- ((fib' fresh2_1_4, even fresh2_1_4))), takeWhile pred2_1_5 x_3 x_0, (pred2_1_5 fresh1_1_5 :- ((<) fresh1_1_5 data1_1_5, data1_1_5 = 1000000)), sum x_0 carg3)).
constraints:
fresh2_1_4[0,1,0,0,0]
~(<)[0,3,0]
~even[0,1,0,0]
~fib'[0,1,0,0]
~fresh1_1_5[0]
~fresh2_1_4[0]
~fresh2_1_4[0,1,0,0,1]
~observeAll[0]
~pred2_1_5[0,2]
~pred4_1_4[0,0]
~sum[0]
~takeWhile[0]
~(data1_1_5[0,3,0,0] & data1_1_5[0,3,0,1])
~(fresh2_1_4[0,1,0,0,0] & fresh2_1_4[0,1,0,0,1])
~(x_0[0,2] & x_0[0,4])
~(x_3[0,0] & x_3[0,2])
(~fresh1_1_5[0,3,0,0] & ~data1_1_5[0,3,0,0])
(~pred4_1_4[0,0] & (pred4_1_4(1) & x_3[0,0]))
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
(fresh1_1_5[0,3,0] <-> fresh1_1_5[0,3,0,0])
(fresh2_1_4[0,1,0] <-> fresh2_1_4[0,1,0,0])
(fresh2_1_4[0,1,0,0] <-> (fresh2_1_4[0,1,0,0,0] | fresh2_1_4[0,1,0,0,1]))
(pred2_1_5(1) <-> fresh1_1_5[0,3,0])
(pred4_1_4(1) <-> fresh2_1_4[0,1,0])
1
-}

euler2 = rget $ (procedure @'[ 'In ] euler2I) :& (procedure @'[ 'Out ] euler2O) :& RNil
  where
    euler2I = \carg3 -> Logic.once $ do
      -- solution: data1_1_5[0,3,0,1] fresh2_1_4[0,1,0] fresh2_1_4[0,1,0,0] fresh2_1_4[0,1,0,0,0] x_0[0,2] x_3[0,0]
      -- cost: 9
      () <- (do
        let pred2_1_5 = procedure @'[ 'In ] $
              \fresh1_1_5 -> do
                () <- (do
                  data1_1_5 <- pure 1000000
                  guard $ (<) fresh1_1_5 data1_1_5
                  pure ()
                 )
                pure ()
        let pred4_1_4 = procedure @'[ 'Out ] $
              do
                (fresh2_1_4) <- (do
                  (OneTuple (fresh2_1_4)) <- runProcedure @'[ 'Out ] fib' 
                  () <- runProcedure @'[ 'In ] even fresh2_1_4
                  pure (fresh2_1_4)
                 )
                pure (OneTuple (fresh2_1_4))
        (OneTuple (x_3)) <- runProcedure @'[ 'PredMode '[ 'Out ], 'Out ] observeAll pred4_1_4
        (OneTuple (x_0)) <- runProcedure @'[ 'PredMode '[ 'In ], 'In, 'Out ] takeWhile pred2_1_5 x_3
        () <- runProcedure @'[ 'In, 'In ] sum x_0 carg3
        pure ()
       )
      pure ()
    
    euler2O = do
      -- solution: carg3[] carg3[0] carg3[0,4] data1_1_5[0,3,0,1] fresh2_1_4[0,1,0] fresh2_1_4[0,1,0,0] fresh2_1_4[0,1,0,0,0] x_0[0,2] x_3[0,0]
      -- cost: 10
      (carg3) <- (do
        let pred2_1_5 = procedure @'[ 'In ] $
              \fresh1_1_5 -> do
                () <- (do
                  data1_1_5 <- pure 1000000
                  guard $ (<) fresh1_1_5 data1_1_5
                  pure ()
                 )
                pure ()
        let pred4_1_4 = procedure @'[ 'Out ] $
              do
                (fresh2_1_4) <- (do
                  (OneTuple (fresh2_1_4)) <- runProcedure @'[ 'Out ] fib' 
                  () <- runProcedure @'[ 'In ] even fresh2_1_4
                  pure (fresh2_1_4)
                 )
                pure (OneTuple (fresh2_1_4))
        (OneTuple (x_3)) <- runProcedure @'[ 'PredMode '[ 'Out ], 'Out ] observeAll pred4_1_4
        (OneTuple (x_0)) <- runProcedure @'[ 'PredMode '[ 'In ], 'In, 'Out ] takeWhile pred2_1_5 x_3
        (OneTuple (carg3)) <- runProcedure @'[ 'In, 'Out ] sum x_0
        pure (carg3)
       )
      pure (OneTuple (carg3))
    
{- nontrivialDivisor/2
nontrivialDivisor n d :- ((succ n' n, elem d data1, data0 = 2, data1 = .. data0 n', divisor n d)).
constraints:
~divisor[0]
~elem[0]
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
        () <- runProcedure @'[ 'In, 'In ] divisor n d
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
        () <- runProcedure @'[ 'In, 'In ] divisor n d
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
factor arg1 arg2 arg3 :- ((arg2 = p:ps, if (timesInt p0 p1 pp, p0 = p, p1 = p, (>) pp n) then (id n f) else (if (divMod n p d data0, data0 = 0) then (fresh1 = f, ((id p fresh1); (factor d data1 fresh1, data1 = p2:ps0, p2 = p, ps0 = ps))) else (factor n ps f)), arg1 = n, arg3 = f)).
constraints:
d[0,1,2,0,0]
data0[0,1,2,0]
p0[0,1]
p1[0,1]
pp[0,1]
~(>)[0,1,0]
~d[0,1,2,0,1,1]
~divMod[0,1,2,0,0]
~factor[0,1,2,0,1,1,1]
~factor[0,1,2,0,2]
~id[0,1,1]
~id[0,1,2,0,1,1,0]
~n[0,1,0,3]
~n[0,1,1,0]
~n[0,1,2]
~n[0,1,2,0,0,0]
~n[0,1,2,0,2]
~p[0,1,2]
~p[0,1,2,0]
~p[0,1,2,0,0,0]
~p[0,1,2,0,1,1]
~ps[0,1,2]
~ps[0,1,2,0,1,1]
~timesInt[0,1,0]
~(arg1[0,2] & n[0,2])
~(arg2[0,0] & p[0,0])
~(arg3[0,3] & f[0,3])
~(data0[0,1,2,0,0,0] & data0[0,1,2,0,0,1])
~(data1[0,1,2,0,1,1,1,0] & data1[0,1,2,0,1,1,1,1])
~(data1[0,1,2,0,1,1,1,1] & p2[0,1,2,0,1,1,1,1])
~(f[0,1] & f[0,3])
~(fresh1[0,1,2,0,1,0] & f[0,1,2,0,1,0])
~(fresh1[0,1,2,0,1,0] & fresh1[0,1,2,0,1,1])
~(n[0,1] & n[0,2])
~(p[0,0] & p[0,1])
~(p[0,1,0,1] & p[0,1,0,2])
~(p0[0,1,0,0] & p0[0,1,0,1])
~(p0[0,1,0,1] & p[0,1,0,1])
~(p1[0,1,0,0] & p1[0,1,0,2])
~(p1[0,1,0,2] & p[0,1,0,2])
~(p2[0,1,2,0,1,1,1,1] & p2[0,1,2,0,1,1,1,2])
~(p2[0,1,2,0,1,1,1,2] & p[0,1,2,0,1,1,1,2])
~(pp[0,1,0,0] & pp[0,1,0,3])
~(ps[0,0] & ps[0,1])
~(ps0[0,1,2,0,1,1,1,1] & ps0[0,1,2,0,1,1,1,3])
~(ps0[0,1,2,0,1,1,1,3] & ps[0,1,2,0,1,1,1,3])
~(p[0,1,0,1] | p[0,1,0,2])
(~pp[0,1,0,3] & ~n[0,1,0,3])
(data0[0,1,2,0,0,0] | data0[0,1,2,0,0,1])
(data1[0,1,2,0,1,1,1,0] | data1[0,1,2,0,1,1,1,1])
(f[0,1] | f[0,3])
(fresh1[0,1,2,0,1,0] | fresh1[0,1,2,0,1,1])
(n[0,1] | n[0,2])
(p[0,0] | p[0,1])
(p0[0,1,0,0] | p0[0,1,0,1])
(p1[0,1,0,0] | p1[0,1,0,2])
(p2[0,1,2,0,1,1,1,1] | p2[0,1,2,0,1,1,1,2])
(pp[0,1,0,0] | pp[0,1,0,3])
(ps[0,0] | ps[0,1])
(ps0[0,1,2,0,1,1,1,1] | ps0[0,1,2,0,1,1,1,3])
((n[0,1,1,0] & ~f[0,1,1,0]) | ((~n[0,1,1,0] & f[0,1,1,0]) | (~n[0,1,1,0] & ~f[0,1,1,0])))
((p[0,1,2,0,1,1,0,0] & ~fresh1[0,1,2,0,1,1,0,0]) | ((~p[0,1,2,0,1,1,0,0] & fresh1[0,1,2,0,1,1,0,0]) | (~p[0,1,2,0,1,1,0,0] & ~fresh1[0,1,2,0,1,1,0,0])))
((p0[0,1,0,0] & (~p1[0,1,0,0] & ~pp[0,1,0,0])) | ((~p0[0,1,0,0] & (p1[0,1,0,0] & ~pp[0,1,0,0])) | ((~p0[0,1,0,0] & (~p1[0,1,0,0] & pp[0,1,0,0])) | (~p0[0,1,0,0] & (~p1[0,1,0,0] & ~pp[0,1,0,0])))))
((~n[0,1,2,0,0,0] & (~p[0,1,2,0,0,0] & (d[0,1,2,0,0,0] & data0[0,1,2,0,0,0]))) | ((~n[0,1,2,0,0,0] & (~p[0,1,2,0,0,0] & (d[0,1,2,0,0,0] & ~data0[0,1,2,0,0,0]))) | ((~n[0,1,2,0,0,0] & (~p[0,1,2,0,0,0] & (~d[0,1,2,0,0,0] & data0[0,1,2,0,0,0]))) | (~n[0,1,2,0,0,0] & (~p[0,1,2,0,0,0] & (~d[0,1,2,0,0,0] & ~data0[0,1,2,0,0,0]))))))
((>)[0] <-> (>)[0,1])
((>)[0,1] <-> (>)[0,1,0])
(arg1[] <-> arg1[0])
(arg1[0] <-> arg1[0,2])
(arg2[] <-> arg2[0])
(arg2[0] <-> arg2[0,0])
(arg3[] <-> arg3[0])
(arg3[0] <-> arg3[0,3])
(d[0,1,2,0,0] <-> d[0,1,2,0,0,0])
(d[0,1,2,0,1,1] <-> d[0,1,2,0,1,1,1])
(d[0,1,2,0,1,1,1] <-> d[0,1,2,0,1,1,1,0])
(d[0,1,2,0,1,1,1,0] <-> arg1[])
(data0[0] <-> data0[0,1])
(data0[0,1] <-> data0[0,1,2])
(data0[0,1,2] <-> data0[0,1,2,0])
(data1[0,1,2,0,1,1,1,0] <-> arg2[])
(divMod[0] <-> divMod[0,1])
(divMod[0,1] <-> divMod[0,1,2])
(divMod[0,1,2] <-> divMod[0,1,2,0])
(divMod[0,1,2,0] <-> divMod[0,1,2,0,0])
(f[0,1] <-> (f[0,1,1] | f[0,1,2]))
(f[0,1,1] <-> f[0,1,1,0])
(f[0,1,1] <-> f[0,1,2])
(f[0,1,2] <-> f[0,1,2,0])
(f[0,1,2,0] <-> (f[0,1,2,0,1] | f[0,1,2,0,2]))
(f[0,1,2,0,1] <-> f[0,1,2,0,1,0])
(f[0,1,2,0,1] <-> f[0,1,2,0,2])
(f[0,1,2,0,2] <-> f[0,1,2,0,2,0])
(f[0,1,2,0,2,0] <-> arg3[])
(factor[0] <-> factor[0,1])
(factor[0,1] <-> factor[0,1,2])
(factor[0,1,2] <-> factor[0,1,2,0])
(factor[0,1,2,0] <-> (factor[0,1,2,0,1] | factor[0,1,2,0,2]))
(factor[0,1,2,0,1] <-> factor[0,1,2,0,1,1])
(fresh1[0,1,2,0,1,1] <-> fresh1[0,1,2,0,1,1,0])
(fresh1[0,1,2,0,1,1] <-> fresh1[0,1,2,0,1,1,1])
(fresh1[0,1,2,0,1,1,0] <-> fresh1[0,1,2,0,1,1,0,0])
(fresh1[0,1,2,0,1,1,1] <-> fresh1[0,1,2,0,1,1,1,0])
(fresh1[0,1,2,0,1,1,1,0] <-> arg3[])
(id[0] <-> id[0,1])
(id[0,1] <-> (id[0,1,1] | id[0,1,2]))
(id[0,1,2] <-> id[0,1,2,0])
(id[0,1,2,0] <-> id[0,1,2,0,1])
(id[0,1,2,0,1] <-> id[0,1,2,0,1,1])
(n[0,1] <-> n[0,1,2])
(n[0,1,2] <-> n[0,1,2,0])
(n[0,1,2,0] <-> n[0,1,2,0,2])
(n[0,1,2,0,2] <-> n[0,1,2,0,2,0])
(n[0,1,2,0,2,0] <-> arg1[])
(p[0,0] <-> ps[0,0])
(p[0,1] <-> p[0,1,2])
(p[0,1,2] <-> p[0,1,2,0])
(p[0,1,2,0,1,1] <-> p[0,1,2,0,1,1,0])
(p[0,1,2,0,1,1] <-> p[0,1,2,0,1,1,1])
(p[0,1,2,0,1,1,0] <-> p[0,1,2,0,1,1,0,0])
(p[0,1,2,0,1,1,1] <-> p[0,1,2,0,1,1,1,2])
(p0[0] <-> p0[0,1])
(p1[0] <-> p1[0,1])
(p2[0,1,2,0,1,1,1,1] <-> ps0[0,1,2,0,1,1,1,1])
(pp[0] <-> pp[0,1])
(ps[0,1] <-> ps[0,1,2])
(ps[0,1,2] <-> ps[0,1,2,0])
(ps[0,1,2,0] <-> (ps[0,1,2,0,1] | ps[0,1,2,0,2]))
(ps[0,1,2,0,1] <-> ps[0,1,2,0,1,1])
(ps[0,1,2,0,1] <-> ps[0,1,2,0,2])
(ps[0,1,2,0,1,1] <-> ps[0,1,2,0,1,1,1])
(ps[0,1,2,0,1,1,1] <-> ps[0,1,2,0,1,1,1,3])
(ps[0,1,2,0,2] <-> ps[0,1,2,0,2,0])
(ps[0,1,2,0,2,0] <-> arg2[])
(timesInt[0] <-> timesInt[0,1])
(timesInt[0,1] <-> timesInt[0,1,0])
1
-}

factor = rget $ (procedure @'[ 'In, 'In, 'In ] factorIII) :& (procedure @'[ 'In, 'In, 'Out ] factorIIO) :& RNil
  where
    factorIII = \arg1 arg2 arg3 -> Logic.once $ do
      -- solution: d[0,1,2,0,0] d[0,1,2,0,0,0] data0[0] data0[0,1] data0[0,1,2] data0[0,1,2,0] data0[0,1,2,0,0,1] data1[0,1,2,0,1,1,1,1] f[0,3] fresh1[0,1,2,0,1,0] n[0,2] p[0,0] p0[0] p0[0,1] p0[0,1,0,1] p1[0] p1[0,1] p1[0,1,0,2] p2[0,1,2,0,1,1,1,2] pp[0] pp[0,1] pp[0,1,0,0] ps[0,0] ps0[0,1,2,0,1,1,1,3]
      -- cost: 9
      () <- (do
        n <- pure arg1
        (p:ps) <- pure arg2
        f <- pure arg3
        () <- Logic.ifte ((do
          p0 <- pure p
          p1 <- pure p
          (OneTuple (pp)) <- runProcedure @'[ 'In, 'In, 'Out ] timesInt p0 p1
          guard $ (>) pp n
          pure ()
         )) (\() -> (do
          () <- runProcedure @'[ 'In, 'In ] id n f
          pure ()
         )) ((do
          () <- Logic.ifte ((do
            data0 <- pure 0
            (OneTuple (d)) <- runProcedure @'[ 'In, 'In, 'Out, 'In ] divMod n p data0
            pure (d)
           )) (\(d) -> (do
            fresh1 <- pure f
            () <- (do
              () <- runProcedure @'[ 'In, 'In ] id p fresh1
              pure ()
             ) <|> (do
              p2 <- pure p
              ps0 <- pure ps
              data1 <- pure (p2:ps0)
              () <- factorIII d data1 fresh1
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
      -- solution: arg3[] arg3[0] arg3[0,3] d[0,1,2,0,0] d[0,1,2,0,0,0] data0[0] data0[0,1] data0[0,1,2] data0[0,1,2,0] data0[0,1,2,0,0,1] data1[0,1,2,0,1,1,1,1] f[0,1] f[0,1,1] f[0,1,1,0] f[0,1,2] f[0,1,2,0] f[0,1,2,0,1] f[0,1,2,0,1,0] f[0,1,2,0,2] f[0,1,2,0,2,0] fresh1[0,1,2,0,1,1] fresh1[0,1,2,0,1,1,0] fresh1[0,1,2,0,1,1,0,0] fresh1[0,1,2,0,1,1,1] fresh1[0,1,2,0,1,1,1,0] n[0,2] p[0,0] p0[0] p0[0,1] p0[0,1,0,1] p1[0] p1[0,1] p1[0,1,0,2] p2[0,1,2,0,1,1,1,2] pp[0] pp[0,1] pp[0,1,0,0] ps[0,0] ps0[0,1,2,0,1,1,1,3]
      -- cost: 13
      (arg3) <- (do
        n <- pure arg1
        (p:ps) <- pure arg2
        (f) <- Logic.ifte ((do
          p0 <- pure p
          p1 <- pure p
          (OneTuple (pp)) <- runProcedure @'[ 'In, 'In, 'Out ] timesInt p0 p1
          guard $ (>) pp n
          pure ()
         )) (\() -> (do
          (OneTuple (f)) <- runProcedure @'[ 'In, 'Out ] id n
          pure (f)
         )) ((do
          (f) <- Logic.ifte ((do
            data0 <- pure 0
            (OneTuple (d)) <- runProcedure @'[ 'In, 'In, 'Out, 'In ] divMod n p data0
            pure (d)
           )) (\(d) -> (do
            (fresh1) <- (do
              (OneTuple (fresh1)) <- runProcedure @'[ 'In, 'Out ] id p
              pure (fresh1)
             ) <|> (do
              p2 <- pure p
              ps0 <- pure ps
              data1 <- pure (p2:ps0)
              (OneTuple (fresh1)) <- factorIIO d data1
              pure (fresh1)
             )
            f <- pure fresh1
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
      -- solution: arg1[] arg1[0] arg1[0,0] arg1[1] arg1[1,6] curry1[1,4,0] curry1[1,4,0,0] d[1] d[1,5] d[1,5,0,0] data0[1,2] p[1,0] primes[1,3]
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
      -- solution: x_0[0,0] x_0[0,1,0] x_0[0,1,0,0]
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
      -- solution: carg3[] carg3[0] carg3[0,2] x_0[0,0] x_0[0,1,0] x_0[0,1,0,0]
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
      -- solution: x_0[0,0] x_0[0,1,0] x_0[0,1,0,0]
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
      -- solution: carg3[] carg3[0] carg3[0,2] x_0[0,0] x_0[0,1,0] x_0[0,1,0,0]
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
    
{- palindrome/1
palindrome s :- ((reverse s s0, s0 = s)).
constraints:
~reverse[0]
~(s[0,0] & s[0,1])
~(s0[0,0] & s0[0,1])
~(s0[0,1] & s[0,1])
(s0[0,0] | s0[0,1])
((s[0,0] & ~s0[0,0]) | ((~s[0,0] & s0[0,0]) | (~s[0,0] & ~s0[0,0])))
(s[] <-> s[0])
(s[0] <-> (s[0,0] | s[0,1]))
1
-}
--mode ordering failure, cyclic dependency: [0] reverse::I s::I s0::O -> [1] s0::I = s::O
--mode ordering failure, cyclic dependency: [0] reverse::I s::O s0::I -> [1] s0::O = s::I
palindrome = rget $ (procedure @'[ 'In ] palindromeI) :& RNil
  where
    palindromeI = \s -> Logic.once $ do
      -- solution: s0[0,1]
      -- cost: 1
      () <- (do
        s0 <- pure s
        () <- runProcedure @'[ 'In, 'In ] reverse s s0
        pure ()
       )
      pure ()
    
{- euler4/1
euler4 fresh1 :- ((elem' data3_2 x_0, data1_2 = 10, data2_2 = 99, data3_2 = .. data1_2 data2_2, elem' data7_3 y_0, data5_3 = 10, data6_3 = 99, data7_3 = .. data5_3 data6_3, timesInt x_0 y_0 fresh1, palindrome x_1, read x_1 fresh1)).
constraints:
~elem'[0]
~palindrome[0]
~read[0]
~timesInt[0]
~x_1[0,9]
~(data1_2[0,1] & data1_2[0,3])
~(data2_2[0,2] & data2_2[0,3])
~(data3_2[0,0] & data3_2[0,3])
~(data3_2[0,3] & data1_2[0,3])
~(data5_3[0,5] & data5_3[0,7])
~(data6_3[0,6] & data6_3[0,7])
~(data7_3[0,4] & data7_3[0,7])
~(data7_3[0,7] & data5_3[0,7])
~(fresh1[0,8] & fresh1[0,10])
~(x_0[0,0] & x_0[0,8])
~(x_1[0,9] & x_1[0,10])
~(y_0[0,4] & y_0[0,8])
(data1_2[0,1] | data1_2[0,3])
(data2_2[0,2] | data2_2[0,3])
(data3_2[0,0] | data3_2[0,3])
(data5_3[0,5] | data5_3[0,7])
(data6_3[0,6] | data6_3[0,7])
(data7_3[0,4] | data7_3[0,7])
(x_0[0,0] | x_0[0,8])
(x_1[0,9] | x_1[0,10])
(y_0[0,4] | y_0[0,8])
((x_0[0,8] & (~y_0[0,8] & ~fresh1[0,8])) | ((~x_0[0,8] & (y_0[0,8] & ~fresh1[0,8])) | ((~x_0[0,8] & (~y_0[0,8] & fresh1[0,8])) | (~x_0[0,8] & (~y_0[0,8] & ~fresh1[0,8])))))
((x_1[0,10] & ~fresh1[0,10]) | ((~x_1[0,10] & fresh1[0,10]) | (~x_1[0,10] & ~fresh1[0,10])))
((~data3_2[0,0] & x_0[0,0]) | (~data3_2[0,0] & ~x_0[0,0]))
((~data7_3[0,4] & y_0[0,4]) | (~data7_3[0,4] & ~y_0[0,4]))
(data1_2[0,3] <-> data2_2[0,3])
(data5_3[0,7] <-> data6_3[0,7])
(fresh1[] <-> fresh1[0])
(fresh1[0] <-> (fresh1[0,8] | fresh1[0,10]))
1
-}

euler4 = rget $ (procedure @'[ 'In ] euler4I) :& (procedure @'[ 'Out ] euler4O) :& RNil
  where
    euler4I = \fresh1 -> Logic.once $ do
      -- solution: data1_2[0,1] data2_2[0,2] data3_2[0,3] data5_3[0,5] data6_3[0,6] data7_3[0,7] x_0[0,8] x_1[0,10] y_0[0,4]
      -- cost: 8
      () <- (do
        data1_2 <- pure 10
        data2_2 <- pure 99
        data3_2 <- pure [data1_2..data2_2]
        data5_3 <- pure 10
        data6_3 <- pure 99
        data7_3 <- pure [data5_3..data6_3]
        (OneTuple (y_0)) <- runProcedure @'[ 'In, 'Out ] elem' data7_3
        (OneTuple (x_1)) <- runProcedure @'[ 'Out, 'In ] read fresh1
        () <- runProcedure @'[ 'In ] palindrome x_1
        (OneTuple (x_0)) <- runProcedure @'[ 'Out, 'In, 'In ] timesInt y_0 fresh1
        () <- runProcedure @'[ 'In, 'In ] elem' data3_2 x_0
        pure ()
       )
      pure ()
    
    euler4O = do
      -- solution: data1_2[0,1] data2_2[0,2] data3_2[0,3] data5_3[0,5] data6_3[0,6] data7_3[0,7] fresh1[] fresh1[0] fresh1[0,8] x_0[0,0] x_1[0,10] y_0[0,4]
      -- cost: 9
      (fresh1) <- (do
        data1_2 <- pure 10
        data2_2 <- pure 99
        data3_2 <- pure [data1_2..data2_2]
        data5_3 <- pure 10
        data6_3 <- pure 99
        data7_3 <- pure [data5_3..data6_3]
        (OneTuple (x_0)) <- runProcedure @'[ 'In, 'Out ] elem' data3_2
        (OneTuple (y_0)) <- runProcedure @'[ 'In, 'Out ] elem' data7_3
        (OneTuple (fresh1)) <- runProcedure @'[ 'In, 'In, 'Out ] timesInt x_0 y_0
        (OneTuple (x_1)) <- runProcedure @'[ 'Out, 'In ] read fresh1
        () <- runProcedure @'[ 'In ] palindrome x_1
        pure (fresh1)
       )
      pure (OneTuple (fresh1))
    
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
      -- solution: x_0[0,0] x_0[0,1,0] x_0[0,1,0,0]
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
      -- solution: carg3[] carg3[0] carg3[0,2] x_0[0,0] x_0[0,1,0] x_0[0,1,0,0]
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
euler5 fresh1 :- ((nat fresh1, (>) fresh2 data0, data0 = 0, fresh1 = fresh2, all' pred1 data4 fresh1, data2 = 1, data3 = 5, data4 = .. data2 data3, (pred1 curry1 curry2 :- (multiple curry1 curry2)))).
constraints:
~(>)[0]
~all'[0]
~curry1[0]
~curry2[0]
~multiple[0,8,0]
~nat[0]
~pred1[0,4]
~(data0[0,1] & data0[0,2])
~(data2[0,5] & data2[0,7])
~(data3[0,6] & data3[0,7])
~(data4[0,4] & data4[0,7])
~(data4[0,7] & data2[0,7])
~(fresh1[0,0] & fresh1[0,3])
~(fresh1[0,0] & fresh1[0,4])
~(fresh1[0,3] & fresh1[0,4])
~(fresh1[0,3] & fresh2[0,3])
~(fresh2[0,1] & fresh2[0,3])
(~curry1[0,8,0,0] & ~curry2[0,8,0,0])
(~fresh2[0,1] & ~data0[0,1])
(data0[0,1] | data0[0,2])
(data2[0,5] | data2[0,7])
(data3[0,6] | data3[0,7])
(data4[0,4] | data4[0,7])
(fresh1[0,0] | ~fresh1[0,0])
(fresh2[0,1] | fresh2[0,3])
((~pred1[0,4] & (pred1(1) & (pred1(2) & (data4[0,4] & ~fresh1[0,4])))) | ((~pred1[0,4] & (pred1(1) & (~pred1(2) & (data4[0,4] & ~fresh1[0,4])))) | ((~pred1[0,4] & (~pred1(1) & (pred1(2) & (~data4[0,4] & ~fresh1[0,4])))) | (~pred1[0,4] & (~pred1(1) & (~pred1(2) & (~data4[0,4] & ~fresh1[0,4])))))))
(curry1[0,8,0] <-> curry1[0,8,0,0])
(curry2[0,8,0] <-> curry2[0,8,0,0])
(data2[0,7] <-> data3[0,7])
(fresh1[] <-> fresh1[0])
(fresh1[0] <-> (fresh1[0,0] | (fresh1[0,3] | fresh1[0,4])))
(multiple[0] <-> multiple[0,8])
(pred1(1) <-> curry1[0,8,0])
(pred1(2) <-> curry2[0,8,0])
1
-}

euler5 = rget $ (procedure @'[ 'In ] euler5I) :& (procedure @'[ 'Out ] euler5O) :& RNil
  where
    euler5I = \fresh1 -> Logic.once $ do
      -- solution: data0[0,2] data2[0,5] data3[0,6] data4[0,7] fresh2[0,3]
      -- cost: 4
      () <- (do
        data0 <- pure 0
        data2 <- pure 1
        data3 <- pure 5
        data4 <- pure [data2..data3]
        fresh2 <- pure fresh1
        guard $ (>) fresh2 data0
        () <- runProcedure @'[ 'In ] nat fresh1
        let pred1 = procedure @'[ 'In, 'In ] $
              \curry1 curry2 -> do
                () <- (do
                  () <- runProcedure @'[ 'In, 'In ] multiple curry1 curry2
                  pure ()
                 )
                pure ()
        () <- runProcedure @'[ 'PredMode '[ 'In, 'In ], 'In, 'In ] all' pred1 data4 fresh1
        pure ()
       )
      pure ()
    
    euler5O = do
      -- solution: data0[0,2] data2[0,5] data3[0,6] data4[0,7] fresh1[] fresh1[0] fresh1[0,0] fresh2[0,3]
      -- cost: 5
      (fresh1) <- (do
        data0 <- pure 0
        data2 <- pure 1
        data3 <- pure 5
        data4 <- pure [data2..data3]
        let pred1 = procedure @'[ 'In, 'In ] $
              \curry1 curry2 -> do
                () <- (do
                  () <- runProcedure @'[ 'In, 'In ] multiple curry1 curry2
                  pure ()
                 )
                pure ()
        (OneTuple (fresh1)) <- runProcedure @'[ 'Out ] nat 
        fresh2 <- pure fresh1
        guard $ (>) fresh2 data0
        () <- runProcedure @'[ 'PredMode '[ 'In, 'In ], 'In, 'In ] all' pred1 data4 fresh1
        pure (fresh1)
       )
      pure (OneTuple (fresh1))
    