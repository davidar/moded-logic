{-# LANGUAGE NoImplicitPrelude, NoMonomorphismRestriction #-}
module Euler where

import Prelude (Eq(..), Ord(..), Maybe(..), Integer, ($), (.))
import Control.Applicative
import Control.Monad
import qualified Control.Monad.Logic as Logic
import Control.Monad.Logic.Moded.Prelude
import Control.Monad.Logic.Moded.Relation
import Data.List (nub)
import Data.MemoTrie

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

nat = R1 { callI = natI, callO = natO }
  where
    natI = \arg1 -> Logic.once $ do
      -- solution: n[1,1] n'[1,2] ~arg1[] ~arg1[0] ~arg1[0,0] ~arg1[1] ~arg1[1,2] ~n[1,0] ~n'[1,1]
      -- cost: 3
      () <- (do
        guard $ arg1 == 0
        pure ()
       ) <|> (do
        n' <- pure arg1
        (n) <- callOI succ n'
        () <- callI nat n
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
        (n) <- callO nat 
        (n') <- callIO succ n
        arg1 <- pure n'
        pure (arg1)
       )
      pure (arg1 :: Integer)
    
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

oddNat = R1 { callI = oddNatI, callO = oddNatO }
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
        (n) <- callOII plus data0 n'
        () <- callI oddNat n
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
        (n) <- callO oddNat 
        (n') <- callIIO plus n data0
        arg1 <- pure n'
        pure (arg1)
       )
      pure (arg1)
    
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

even = R1 { callI = evenI }
  where
    evenI = \x -> Logic.once $ do
      -- solution: data0[0,1] data1[0,2] ~data0[0,0] ~data1[0,0] ~x[] ~x[0] ~x[0,0]
      -- cost: 1
      () <- (do
        data1 <- pure 0
        data0 <- pure 2
        () <- callIII mod x data0 data1
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

elem = R2 { callOI = elemOI }
  where
    elemOI = \arg2 -> do
      -- solution: x[] x[0] x[0,0] x[1] x[1,1] xs[1,0] ~arg2[] ~arg2[0] ~arg2[0,0] ~arg2[1] ~arg2[1,0] ~xs[1,1]
      -- cost: 2
      (x) <- (do
        (x:_) <- pure arg2
        pure (x)
       ) <|> (do
        (_:xs) <- pure arg2
        (x) <- callOI elem xs
        pure (x)
       )
      pure (x)
    
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

span = R4 { callIIII = spanP1IIII, callIIIO = spanP1IIIO, callIIOI = spanP1IIOI, callIIOO = spanP1IIOO }
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
          () <- callI p x
          pure ()
         )) (\() -> (do
          (x2:yt) <- pure ys
          guard $ x2 == x
          () <- callIIII span p xs yt zs
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
          () <- callI p x
          pure ()
         )) (\() -> (do
          (x2:yt) <- pure ys
          guard $ x2 == x
          (zs) <- callIIIO span p xs yt
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
      pure (arg4)
    
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
          () <- callI p x
          pure ()
         )) (\() -> (do
          x2 <- pure x
          (yt) <- callIIOI span p xs zs
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
      pure (arg3)
    
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
          () <- callI p x
          pure ()
         )) (\() -> (do
          x2 <- pure x
          (yt,zs) <- callIIOO span p xs
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

reverseDL = R3 { callIII = reverseDLIII, callIIO = reverseDLIIO, callIOI = reverseDLIOI, callOOI = reverseDLOOI }
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
        () <- callIII reverseDL t data0 r
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
        (r) <- callIIO reverseDL t data0
        arg3 <- pure r
        pure (arg3)
       )
      pure (arg3)
    
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
        (data0) <- callIOI reverseDL t r
        (h1:rest) <- pure data0
        arg2 <- pure rest
        guard $ h1 == h
        pure (arg2)
       )
      pure (arg2)
    
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
        (t,data0) <- callOOI reverseDL r
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

reverse = R2 { callII = reverseII, callIO = reverseIO, callOI = reverseOI }
  where
    reverseII = \s r -> Logic.once $ do
      -- solution: data0[0,1] ~data0[0,0] ~r[] ~r[0] ~r[0,0] ~s[] ~s[0] ~s[0,0]
      -- cost: 1
      () <- (do
        data0 <- pure []
        () <- callIII reverseDL s data0 r
        pure ()
       )
      pure ()
    
    reverseIO = \s -> do
      -- solution: data0[0,1] r[] r[0] r[0,0] ~data0[0,0] ~s[] ~s[0] ~s[0,0]
      -- cost: 2
      (r) <- (do
        data0 <- pure []
        (r) <- callIIO reverseDL s data0
        pure (r)
       )
      pure (r)
    
    reverseOI = \r -> do
      -- solution: data0[0,0] s[] s[0] s[0,0] ~data0[0,1] ~r[] ~r[0] ~r[0,0]
      -- cost: 3
      (s) <- (do
        (s,data0) <- callOOI reverseDL r
        guard $ data0 == []
        pure (s)
       )
      pure (s)
    
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

all = R2 { callII = allP1II }
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
          () <- callI p h
          pure ()
         )) (\() -> (do
          () <- callII all p t
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

multiple = R2 { callII = multipleII }
  where
    multipleII = \x y -> Logic.once $ do
      -- solution: data0[0,1] ~data0[0,0] ~x[] ~x[0] ~x[0,0] ~y[] ~y[0] ~y[0,0]
      -- cost: 1
      () <- (do
        data0 <- pure 0
        () <- callIII mod x y data0
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

euler1 = R1 { callO = euler1O }
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
        (x) <- callOI elem data2
        () <- callII multiple x y
        pure (x)
       )
      pure (x)
    
{- euler1'/1
euler1' s :- ((observeAll pred0 r, (pred0 x :- (euler1 x)), sum r s)).
constraints:
x[0,1,0,0]
~pred0[0,0]
~x[0]
~(r[0,0] & r[0,2])
(~pred0[0,0] & (pred0(1) & r[0,0]))
(r[0,0] | r[0,2])
((~r[0,2] & s[0,2]) | (~r[0,2] & ~s[0,2]))
(s[] <-> s[0])
(s[0] <-> s[0,2])
(x[0,1,0] <-> x[0,1,0,0])
(pred0(1) <-> x[0,1,0])
1
-}

euler1' = R1 { callI = euler1'I, callO = euler1'O }
  where
    euler1'I = \s -> Logic.once $ do
      -- solution: r[0,0] x[0,1,0] x[0,1,0,0] pred0(1) ~pred0[0,0] ~r[0,2] ~s[] ~s[0] ~s[0,2] ~x[0]
      -- cost: 5
      () <- (do
        let pred0 = R1 { callO =
              do
                (x) <- (do
                  (x) <- callO euler1 
                  pure (x)
                 )
                pure (x)
              }
        (r) <- callIO observeAll pred0
        () <- callII sum r s
        pure ()
       )
      pure ()
    
    euler1'O = do
      -- solution: r[0,0] s[] s[0] s[0,2] x[0,1,0] x[0,1,0,0] pred0(1) ~pred0[0,0] ~r[0,2] ~x[0]
      -- cost: 6
      (s) <- (do
        let pred0 = R1 { callO =
              do
                (x) <- (do
                  (x) <- callO euler1 
                  pure (x)
                 )
                pure (x)
              }
        (r) <- callIO observeAll pred0
        (s) <- callIO sum r
        pure (s)
       )
      pure (s)
    
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

fib = R2 { callIO = fibIO, callOO = fibOO }
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
        (j) <- callOI succ k
        (fj) <- callIO fib j
        (i) <- callOI succ j
        (fi) <- callIO fib i
        (fk) <- callIIO plus fi fj
        arg2 <- pure fk
        pure (arg2)
       )
      pure (arg2)
    
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
        (i,fi) <- callOO fib 
        (j,fj) <- callOO fib 
        () <- callII succ i j
        (fk) <- callIIO plus fi fj
        arg2 <- pure fk
        (k) <- callIO succ j
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

fib' = R1 { callO = fib'O }
  where
    fib'O = do
      -- solution: f[] f[0] f[0,1] i[0,0] ~i[0,1]
      -- cost: 4
      (f) <- (do
        (i) <- callO nat 
        (f) <- callIO fib i
        pure (f)
       )
      pure (f)
    
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

euler2 = R1 { callI = euler2I, callO = euler2O }
  where
    euler2I = \s -> Logic.once $ do
      -- solution: data1[0,3] data1[0,4,0] data1[0,4,0,1] fs[0,0] x[0,1,0] x[0,1,0,0] xs[0,2] pred0(1) ~data1[0,4,0,0] ~fs[0,2] ~pred0[0,0] ~pred2[0,2] ~s[] ~s[0] ~s[0,5] ~x[0] ~x[0,1,0,1] ~x[0,4,0] ~x[0,4,0,0] ~xs[0,5] ~pred2(1)
      -- cost: 10
      () <- (do
        data1 <- pure 1000000
        let pred0 = R1 { callO =
              do
                (x) <- (do
                  (x) <- callO fib' 
                  () <- callI even x
                  pure (x)
                 )
                pure (x)
              }
        let pred2 = R1 { callI =
              \x -> do
                (data1) <- (do
                  data1 <- pure 1000000
                  guard $ (<) x data1
                  pure (data1)
                 )
                pure ()
              }
        (fs) <- callIO observeAll pred0
        (xs,_) <- callIIOO span pred2 fs
        () <- callII sum xs s
        pure ()
       )
      pure ()
    
    euler2O = do
      -- solution: data1[0,3] data1[0,4,0] data1[0,4,0,1] fs[0,0] s[] s[0] s[0,5] x[0,1,0] x[0,1,0,0] xs[0,2] pred0(1) ~data1[0,4,0,0] ~fs[0,2] ~pred0[0,0] ~pred2[0,2] ~x[0] ~x[0,1,0,1] ~x[0,4,0] ~x[0,4,0,0] ~xs[0,5] ~pred2(1)
      -- cost: 11
      (s) <- (do
        data1 <- pure 1000000
        let pred0 = R1 { callO =
              do
                (x) <- (do
                  (x) <- callO fib' 
                  () <- callI even x
                  pure (x)
                 )
                pure (x)
              }
        let pred2 = R1 { callI =
              \x -> do
                (data1) <- (do
                  data1 <- pure 1000000
                  guard $ (<) x data1
                  pure (data1)
                 )
                pure ()
              }
        (fs) <- callIO observeAll pred0
        (xs,_) <- callIIOO span pred2 fs
        (s) <- callIO sum xs
        pure (s)
       )
      pure (s)
    
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

nontrivialDivisor = R2 { callIO = nontrivialDivisorIO }
  where
    nontrivialDivisorIO = \n -> do
      -- solution: d[] d[0] d[0,1] data0[0,2] data1[0,3] data2[0,5] n'[0,0] ~d[0,4] ~data0[0,3] ~data1[0,1] ~data2[0,4] ~n[] ~n[0] ~n[0,0] ~n[0,4] ~n'[0,3]
      -- cost: 5
      (d) <- (do
        data2 <- pure 0
        data0 <- pure 2
        (n') <- callOI succ n
        data1 <- pure [data0..n']
        (d) <- callOI elem data1
        () <- callIII mod n d data2
        pure (d)
       )
      pure (d)
    
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

primeSlow = R1 { callI = primeSlowI, callO = primeSlowO }
  where
    primeSlowI = \n -> Logic.once $ do
      -- solution: _[0] _[0,3] data0[0,2] ~data0[0,1] ~n[] ~n[0] ~n[0,0] ~n[0,1] ~n[0,3] ~n[0,3,0,0]
      -- cost: 5
      () <- (do
        data0 <- pure 1
        guard $ (>) n data0
        () <- callI nat n
        () <- Logic.ifte ((do
          (_) <- callIO nontrivialDivisor n
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
        (n) <- callO nat 
        guard $ (>) n data0
        () <- Logic.ifte ((do
          (_) <- callIO nontrivialDivisor n
          pure ()
         )) (\() -> (do
          () <- empty 
          pure ()
         )) ((do
          
          pure ()
         ))
        pure (n)
       )
      pure (n)
    
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

factor = R3 { callIII = factorIII, callIIO = factorIIO }
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
          (pp) <- callIIO timesInt p2 p3
          guard $ (>) pp n
          pure ()
         )) (\() -> (do
          guard $ f == n
          pure ()
         )) ((do
          () <- Logic.ifte ((do
            data0 <- pure 0
            (d) <- callIIOI divMod n p data0
            pure (d)
           )) (\(d) -> (do
            () <- (do
              guard $ f == p
              pure ()
             ) <|> (do
              p4 <- pure p
              ps5 <- pure ps
              data1 <- pure (p4:ps5)
              () <- callIII factor data1 d f
              pure ()
             )
            pure ()
           )) ((do
            () <- callIII factor ps n f
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
          (pp) <- callIIO timesInt p2 p3
          guard $ (>) pp n
          pure ()
         )) (\() -> (do
          f <- pure n
          pure (f)
         )) ((do
          (f) <- Logic.ifte ((do
            data0 <- pure 0
            (d) <- callIIOI divMod n p data0
            pure (d)
           )) (\(d) -> (do
            (f) <- (do
              f <- pure p
              pure (f)
             ) <|> (do
              p4 <- pure p
              ps5 <- pure ps
              data1 <- pure (p4:ps5)
              (f) <- callIIO factor data1 d
              pure (f)
             )
            pure (f)
           )) ((do
            (f) <- callIIO factor ps n
            pure (f)
           ))
          pure (f)
         ))
        pure (f)
       )
      pure (f)
    
{- prime/1
prime arg1 :- ((arg1 = 2); (oddNat p, (>) p data0, data0 = 2, observeAll pred1 primes, (pred1 x :- (prime x)), if (factor primes p d, (/=) p d) then (empty) else (), arg1 = p)).
constraints:
d[1,5]
~p[1,5]
~pred1[1,3]
~primes[1,5]
~primes[1,5,0,0]
~x[1]
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
(d[1] <-> d[1,5])
(x[1,4,0] <-> x[1,4,0,0])
(x[1,4,0,0] <-> arg1[])
(pred1(1) <-> x[1,4,0])
1
-}

prime = R1 { callO = primeO }
  where
    primeO = choose . Logic.observeAll $ do
      -- solution: arg1[] arg1[0] arg1[0,0] arg1[1] arg1[1,6] d[1] d[1,5] d[1,5,0,0] data0[1,2] p[1,0] primes[1,3] x[1,4,0] x[1,4,0,0] pred1(1) ~d[1,5,0,1] ~data0[1,1] ~p[1,1] ~p[1,5] ~p[1,5,0,0] ~p[1,5,0,1] ~p[1,6] ~pred1[1,3] ~primes[1,5] ~primes[1,5,0,0] ~x[1]
      -- cost: 11
      (arg1) <- (do
        arg1 <- pure 2
        pure (arg1)
       ) <|> (do
        data0 <- pure 2
        (p) <- callO oddNat 
        arg1 <- pure p
        guard $ (>) p data0
        let pred1 = R1 { callO =
              do
                (x) <- (do
                  (x) <- callO prime 
                  pure (x)
                 )
                pure (x)
              }
        (primes) <- callIO observeAll pred1
        () <- Logic.ifte ((do
          (d) <- callIIO factor primes p
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
      pure (arg1)
    
{- primeFactor/2
primeFactor n d :- ((observeAll pred0 primes, (pred0 x :- (prime x)), factor primes n d)).
constraints:
x[0,1,0,0]
~pred0[0,0]
~x[0]
~(primes[0,0] & primes[0,2])
(~pred0[0,0] & (pred0(1) & primes[0,0]))
(primes[0,0] | primes[0,2])
((~primes[0,2] & (~n[0,2] & d[0,2])) | (~primes[0,2] & (~n[0,2] & ~d[0,2])))
(d[] <-> d[0])
(d[0] <-> d[0,2])
(n[] <-> n[0])
(n[0] <-> n[0,2])
(x[0,1,0] <-> x[0,1,0,0])
(pred0(1) <-> x[0,1,0])
1
-}

primeFactor = R2 { callII = primeFactorII, callIO = primeFactorIO }
  where
    primeFactorII = \n d -> Logic.once $ do
      -- solution: primes[0,0] x[0,1,0] x[0,1,0,0] pred0(1) ~d[] ~d[0] ~d[0,2] ~n[] ~n[0] ~n[0,2] ~pred0[0,0] ~primes[0,2] ~x[0]
      -- cost: 5
      () <- (do
        let pred0 = R1 { callO =
              do
                (x) <- (do
                  (x) <- callO prime 
                  pure (x)
                 )
                pure (x)
              }
        (primes) <- callIO observeAll pred0
        () <- callIII factor primes n d
        pure ()
       )
      pure ()
    
    primeFactorIO = \n -> do
      -- solution: d[] d[0] d[0,2] primes[0,0] x[0,1,0] x[0,1,0,0] pred0(1) ~n[] ~n[0] ~n[0,2] ~pred0[0,0] ~primes[0,2] ~x[0]
      -- cost: 6
      (d) <- (do
        let pred0 = R1 { callO =
              do
                (x) <- (do
                  (x) <- callO prime 
                  pure (x)
                 )
                pure (x)
              }
        (primes) <- callIO observeAll pred0
        (d) <- callIIO factor primes n
        pure (d)
       )
      pure (d)
    
{- euler3/2
euler3 n r :- ((observeAll pred0 fs, (pred0 d :- (primeFactor n d)), maximum fs r)).
constraints:
~d[0]
~n[0]
~pred0[0,0]
~(fs[0,0] & fs[0,2])
(~pred0[0,0] & (pred0(1) & fs[0,0]))
(fs[0,0] | fs[0,2])
((~fs[0,2] & r[0,2]) | (~fs[0,2] & ~r[0,2]))
((~n[0,1,0,0] & d[0,1,0,0]) | (~n[0,1,0,0] & ~d[0,1,0,0]))
(d[0,1,0] <-> d[0,1,0,0])
(n[] <-> n[0])
(n[0,1,0] <-> n[0,1,0,0])
(r[] <-> r[0])
(r[0] <-> r[0,2])
(pred0(1) <-> d[0,1,0])
1
-}

euler3 = R2 { callII = euler3II, callIO = euler3IO }
  where
    euler3II = \n r -> Logic.once $ do
      -- solution: d[0,1,0] d[0,1,0,0] fs[0,0] pred0(1) ~d[0] ~fs[0,2] ~n[] ~n[0] ~n[0,1,0] ~n[0,1,0,0] ~pred0[0,0] ~r[] ~r[0] ~r[0,2]
      -- cost: 5
      () <- (do
        let pred0 = R1 { callO =
              do
                (d) <- (do
                  (d) <- callIO primeFactor n
                  pure (d)
                 )
                pure (d)
              }
        (fs) <- callIO observeAll pred0
        () <- callII maximum fs r
        pure ()
       )
      pure ()
    
    euler3IO = \n -> do
      -- solution: d[0,1,0] d[0,1,0,0] fs[0,0] r[] r[0] r[0,2] pred0(1) ~d[0] ~fs[0,2] ~n[] ~n[0] ~n[0,1,0] ~n[0,1,0,0] ~pred0[0,0]
      -- cost: 6
      (r) <- (do
        let pred0 = R1 { callO =
              do
                (d) <- (do
                  (d) <- callIO primeFactor n
                  pure (d)
                 )
                pure (d)
              }
        (fs) <- callIO observeAll pred0
        (r) <- callIO maximum fs
        pure (r)
       )
      pure (r)
    
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
euler4 = R1 { callO = euler4O }
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
        (x) <- callOI elem data2
        (y) <- callOI elem data5
        (n) <- callIIO timesInt x y
        (s) <- callIO show n
        s0 <- pure s
        s1 <- pure s
        () <- callII reverse s0 s1
        pure (n)
       )
      pure (n)
    
{- euler4'/1
euler4' n :- ((observeAll pred0 s, (pred0 x :- (euler4 x)), maximum s n)).
constraints:
x[0,1,0,0]
~pred0[0,0]
~x[0]
~(s[0,0] & s[0,2])
(~pred0[0,0] & (pred0(1) & s[0,0]))
(s[0,0] | s[0,2])
((~s[0,2] & n[0,2]) | (~s[0,2] & ~n[0,2]))
(n[] <-> n[0])
(n[0] <-> n[0,2])
(x[0,1,0] <-> x[0,1,0,0])
(pred0(1) <-> x[0,1,0])
1
-}

euler4' = R1 { callI = euler4'I, callO = euler4'O }
  where
    euler4'I = \n -> Logic.once $ do
      -- solution: s[0,0] x[0,1,0] x[0,1,0,0] pred0(1) ~n[] ~n[0] ~n[0,2] ~pred0[0,0] ~s[0,2] ~x[0]
      -- cost: 5
      () <- (do
        let pred0 = R1 { callO =
              do
                (x) <- (do
                  (x) <- callO euler4 
                  pure (x)
                 )
                pure (x)
              }
        (s) <- callIO observeAll pred0
        () <- callII maximum s n
        pure ()
       )
      pure ()
    
    euler4'O = do
      -- solution: n[] n[0] n[0,2] s[0,0] x[0,1,0] x[0,1,0,0] pred0(1) ~pred0[0,0] ~s[0,2] ~x[0]
      -- cost: 6
      (n) <- (do
        let pred0 = R1 { callO =
              do
                (x) <- (do
                  (x) <- callO euler4 
                  pure (x)
                 )
                pure (x)
              }
        (s) <- callIO observeAll pred0
        (n) <- callIO maximum s
        pure (n)
       )
      pure (n)
    
{- euler5/1
euler5 n :- ((nat n, (>) n data0, data0 = 0, all pred1 data4, data2 = 1, data3 = 5, data4 = .. data2 data3, (pred1 x :- (multiple n x)))).
constraints:
~pred1[0,3]
~x[0]
~(data0[0,1] & data0[0,2])
~(data2[0,4] & data2[0,6])
~(data3[0,5] & data3[0,6])
~(data4[0,3] & data4[0,6])
~(data4[0,6] & data2[0,6])
~(n[0,0] & n[0,1])
(~n[0,1] & ~data0[0,1])
(~n[0,7,0,0] & ~x[0,7,0,0])
(~pred1[0,3] & (~pred1(1) & ~data4[0,3]))
(data0[0,1] | data0[0,2])
(data2[0,4] | data2[0,6])
(data3[0,5] | data3[0,6])
(data4[0,3] | data4[0,6])
(n[0,0] | ~n[0,0])
(data2[0,6] <-> data3[0,6])
(n[] <-> n[0])
(n[0] <-> (n[0,0] | n[0,1]))
(n[0,7,0] <-> n[0,7,0,0])
(x[0,7,0] <-> x[0,7,0,0])
(pred1(1) <-> x[0,7,0])
1
-}

euler5 = R1 { callI = euler5I, callO = euler5O }
  where
    euler5I = \n -> Logic.once $ do
      -- solution: data0[0,2] data2[0,4] data3[0,5] data4[0,6] ~data0[0,1] ~data2[0,6] ~data3[0,6] ~data4[0,3] ~n[] ~n[0] ~n[0,0] ~n[0,1] ~n[0,7,0] ~n[0,7,0,0] ~pred1[0,3] ~x[0] ~x[0,7,0] ~x[0,7,0,0] ~pred1(1)
      -- cost: 4
      () <- (do
        data0 <- pure 0
        data2 <- pure 1
        data3 <- pure 5
        data4 <- pure [data2..data3]
        guard $ (>) n data0
        () <- callI nat n
        let pred1 = R1 { callI =
              \x -> do
                () <- (do
                  () <- callII multiple n x
                  pure ()
                 )
                pure ()
              }
        () <- callII all pred1 data4
        pure ()
       )
      pure ()
    
    euler5O = do
      -- solution: data0[0,2] data2[0,4] data3[0,5] data4[0,6] n[] n[0] n[0,0] ~data0[0,1] ~data2[0,6] ~data3[0,6] ~data4[0,3] ~n[0,1] ~n[0,7,0] ~n[0,7,0,0] ~pred1[0,3] ~x[0] ~x[0,7,0] ~x[0,7,0,0] ~pred1(1)
      -- cost: 5
      (n) <- (do
        data0 <- pure 0
        data2 <- pure 1
        data3 <- pure 5
        data4 <- pure [data2..data3]
        (n) <- callO nat 
        guard $ (>) n data0
        let pred1 = R1 { callI =
              \x -> do
                () <- (do
                  () <- callII multiple n x
                  pure ()
                 )
                pure ()
              }
        () <- callII all pred1 data4
        pure (n)
       )
      pure (n)
    