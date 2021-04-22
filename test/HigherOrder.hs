{-# LANGUAGE NoImplicitPrelude, NoMonomorphismRestriction #-}
module HigherOrder where

import Prelude (Eq(..), Ord(..), Maybe(..), Integer, ($), (.))
import Control.Applicative
import Control.Monad
import qualified Control.Monad.Logic as Logic
import Control.Monad.Logic.Moded.Prelude
import Control.Monad.Logic.Moded.Relation
import Data.List (nub)
import Data.MemoTrie

{- even/1
even n :- ((mod n data0 data1, data0 = 2, data1 = 0)).
constraints:
~(data0[0,0] & data0[0,1])
~(data1[0,0] & data1[0,2])
(data0[0,0] | data0[0,1])
(data1[0,0] | data1[0,2])
((~n[0,0] & (~data0[0,0] & data1[0,0])) | (~n[0,0] & (~data0[0,0] & ~data1[0,0])))
(n[] <-> n[0])
(n[0] <-> n[0,0])
1
-}

even = R1 { callI = evenI }
  where
    evenI = \n -> Logic.once $ do
      -- solution: data0[0,1] data1[0,2] ~data0[0,0] ~data1[0,0] ~n[] ~n[0] ~n[0,0]
      -- cost: 1
      () <- (do
        data1 <- pure 0
        data0 <- pure 2
        () <- callIII mod n data0 data1
        pure ()
       )
      pure ()
    
{- map/3
map p arg2 arg3 :- ((arg2 = [], arg3 = []); (arg2 = x:xs, arg3 = y:ys, p x y, map p xs ys)).
constraints:
~p[]
~(arg2[1,0] & x[1,0])
~(arg3[1,1] & y[1,1])
~(x[1,0] & x[1,2])
~(xs[1,0] & xs[1,3])
~(y[1,1] & y[1,2])
~(ys[1,1] & ys[1,3])
(x[1,0] | x[1,2])
(xs[1,0] | xs[1,3])
(y[1,1] | y[1,2])
(ys[1,1] | ys[1,3])
(arg2[] <-> arg2[0])
(arg2[] <-> arg2[1])
(arg2[0] <-> arg2[0,0])
(arg2[1] <-> arg2[1,0])
(arg3[] <-> arg3[0])
(arg3[] <-> arg3[1])
(arg3[0] <-> arg3[0,1])
(arg3[1] <-> arg3[1,1])
(p[] <-> p[1])
(p[1] <-> p[1,3])
(p[1,3] <-> p[])
(x[1,0] <-> xs[1,0])
(x[1,2] <-> p(1))
(xs[1,3] <-> arg2[])
(y[1,1] <-> ys[1,1])
(y[1,2] <-> p(2))
(ys[1,3] <-> arg3[])
1
-}

map = R3 { callIII = mapP2IIII, callIIO = mapP2IOIO, callIOI = mapP2OIOI, callIOO = mapP2OOOO }
  where
    mapP2IIII = \p arg2 arg3 -> Logic.once $ do
      -- solution: x[1,0] xs[1,0] y[1,1] ys[1,1] ~arg2[] ~arg2[0] ~arg2[0,0] ~arg2[1] ~arg2[1,0] ~arg3[] ~arg3[0] ~arg3[0,1] ~arg3[1] ~arg3[1,1] ~p[] ~p[1] ~p[1,3] ~x[1,2] ~xs[1,3] ~y[1,2] ~ys[1,3] ~p(1) ~p(2)
      -- cost: 2
      () <- (do
        guard $ arg2 == []
        guard $ arg3 == []
        pure ()
       ) <|> (do
        (x:xs) <- pure arg2
        (y:ys) <- pure arg3
        () <- callIII map p xs ys
        () <- callII p x y
        pure ()
       )
      pure ()
    
    mapP2IOIO = \p arg2 -> do
      -- solution: arg3[] arg3[0] arg3[0,1] arg3[1] arg3[1,1] x[1,0] xs[1,0] y[1,2] ys[1,3] p(2) ~arg2[] ~arg2[0] ~arg2[0,0] ~arg2[1] ~arg2[1,0] ~p[] ~p[1] ~p[1,3] ~x[1,2] ~xs[1,3] ~y[1,1] ~ys[1,1] ~p(1)
      -- cost: 4
      (arg3) <- (do
        guard $ arg2 == []
        arg3 <- pure []
        pure (arg3)
       ) <|> (do
        (x:xs) <- pure arg2
        (ys) <- callIIO map p xs
        (y) <- callIO p x
        arg3 <- pure (y:ys)
        pure (arg3)
       )
      pure (arg3)
    
    mapP2OIOI = \p arg3 -> do
      -- solution: arg2[] arg2[0] arg2[0,0] arg2[1] arg2[1,0] x[1,2] xs[1,3] y[1,1] ys[1,1] p(1) ~arg3[] ~arg3[0] ~arg3[0,1] ~arg3[1] ~arg3[1,1] ~p[] ~p[1] ~p[1,3] ~x[1,0] ~xs[1,0] ~y[1,2] ~ys[1,3] ~p(2)
      -- cost: 4
      (arg2) <- (do
        arg2 <- pure []
        guard $ arg3 == []
        pure (arg2)
       ) <|> (do
        (y:ys) <- pure arg3
        (xs) <- callIOI map p ys
        (x) <- callOI p y
        arg2 <- pure (x:xs)
        pure (arg2)
       )
      pure (arg2)
    
    mapP2OOOO = \p -> do
      -- solution: arg2[] arg2[0] arg2[0,0] arg2[1] arg2[1,0] arg3[] arg3[0] arg3[0,1] arg3[1] arg3[1,1] x[1,2] xs[1,3] y[1,2] ys[1,3] p(1) p(2) ~p[] ~p[1] ~p[1,3] ~x[1,0] ~xs[1,0] ~y[1,1] ~ys[1,1]
      -- cost: 6
      (arg2,arg3) <- (do
        arg2 <- pure []
        arg3 <- pure []
        pure (arg2,arg3)
       ) <|> (do
        (xs,ys) <- callIOO map p
        (x,y) <- callOO p 
        arg2 <- pure (x:xs)
        arg3 <- pure (y:ys)
        pure (arg2,arg3)
       )
      pure (arg2,arg3)
    
{- succs/2
succs xs ys :- ((map pred0 xs ys, (pred0 x y :- (succ x y)))).
constraints:
~pred0[0,0]
~x[0]
~y[0]
((x[0,1,0,0] & ~y[0,1,0,0]) | ((~x[0,1,0,0] & y[0,1,0,0]) | (~x[0,1,0,0] & ~y[0,1,0,0])))
((~pred0[0,0] & (pred0(1) & (pred0(2) & (xs[0,0] & ys[0,0])))) | ((~pred0[0,0] & (pred0(1) & (~pred0(2) & (xs[0,0] & ~ys[0,0])))) | ((~pred0[0,0] & (~pred0(1) & (pred0(2) & (~xs[0,0] & ys[0,0])))) | (~pred0[0,0] & (~pred0(1) & (~pred0(2) & (~xs[0,0] & ~ys[0,0])))))))
(x[0,1,0] <-> x[0,1,0,0])
(xs[] <-> xs[0])
(xs[0] <-> xs[0,0])
(y[0,1,0] <-> y[0,1,0,0])
(ys[] <-> ys[0])
(ys[0] <-> ys[0,0])
(pred0(1) <-> x[0,1,0])
(pred0(2) <-> y[0,1,0])
1
-}

succs = R2 { callII = succsII, callIO = succsIO, callOI = succsOI }
  where
    succsII = \xs ys -> Logic.once $ do
      -- solution: ~pred0[0,0] ~x[0] ~x[0,1,0] ~x[0,1,0,0] ~xs[] ~xs[0] ~xs[0,0] ~y[0] ~y[0,1,0] ~y[0,1,0,0] ~ys[] ~ys[0] ~ys[0,0] ~pred0(1) ~pred0(2)
      -- cost: 2
      () <- (do
        let pred0 = R2 { callII =
              \x y -> do
                () <- (do
                  () <- callII succ x y
                  pure ()
                 )
                pure ()
              }
        () <- callIII map pred0 xs ys
        pure ()
       )
      pure ()
    
    succsIO = \xs -> do
      -- solution: y[0,1,0] y[0,1,0,0] ys[] ys[0] ys[0,0] pred0(2) ~pred0[0,0] ~x[0] ~x[0,1,0] ~x[0,1,0,0] ~xs[] ~xs[0] ~xs[0,0] ~y[0] ~pred0(1)
      -- cost: 4
      (ys) <- (do
        let pred0 = R2 { callIO =
              \x -> do
                (y) <- (do
                  (y) <- callIO succ x
                  pure (y)
                 )
                pure (y)
              }
        (ys) <- callIIO map pred0 xs
        pure (ys)
       )
      pure (ys)
    
    succsOI = \ys -> do
      -- solution: x[0,1,0] x[0,1,0,0] xs[] xs[0] xs[0,0] pred0(1) ~pred0[0,0] ~x[0] ~y[0] ~y[0,1,0] ~y[0,1,0,0] ~ys[] ~ys[0] ~ys[0,0] ~pred0(2)
      -- cost: 4
      (xs) <- (do
        let pred0 = R2 { callOI =
              \y -> do
                (x) <- (do
                  (x) <- callOI succ y
                  pure (x)
                 )
                pure (x)
              }
        (xs) <- callIOI map pred0 ys
        pure (xs)
       )
      pure (xs)
    
{- filter/3
filter p arg2 arg3 :- ((arg2 = [], arg3 = []); (arg2 = h0:t, h0 = h, if (p h) then (filter p t t', ts = h1:t', h1 = h) else (filter p t ts), arg3 = ts)).
constraints:
~h[1,2]
~h[1,2,0,0]
~h[1,2,1,2]
~p[]
~(arg2[1,0] & h0[1,0])
~(arg3[1,3] & ts[1,3])
~(h[1,1] & h[1,2])
~(h0[1,0] & h0[1,1])
~(h0[1,1] & h[1,1])
~(h1[1,2,1,1] & h1[1,2,1,2])
~(h1[1,2,1,2] & h[1,2,1,2])
~(t[1,0] & t[1,2])
~(t'[1,2,1,0] & t'[1,2,1,1])
~(ts[1,2] & ts[1,3])
~(ts[1,2,1,1] & h1[1,2,1,1])
(h[1,1] | h[1,2])
(h0[1,0] | h0[1,1])
(h1[1,2,1,1] | h1[1,2,1,2])
(t[1,0] | t[1,2])
(t'[1,2,1,0] | t'[1,2,1,1])
(ts[1,2] | ts[1,3])
(arg2[] <-> arg2[0])
(arg2[] <-> arg2[1])
(arg2[0] <-> arg2[0,0])
(arg2[1] <-> arg2[1,0])
(arg3[] <-> arg3[0])
(arg3[] <-> arg3[1])
(arg3[0] <-> arg3[0,1])
(arg3[1] <-> arg3[1,3])
(h[1,2,0,0] <-> p(1))
(h0[1,0] <-> t[1,0])
(h1[1,2,1,1] <-> t'[1,2,1,1])
(p[] <-> p[1])
(p[1] <-> p[1,2])
(p[1,2] <-> (p[1,2,1] | p[1,2,2]))
(p[1,2,1] <-> p[1,2,1,0])
(p[1,2,1] <-> p[1,2,2])
(p[1,2,1,0] <-> p[])
(p[1,2,2] <-> p[1,2,2,0])
(p[1,2,2,0] <-> p[])
(t[1,2] <-> (t[1,2,1] | t[1,2,2]))
(t[1,2,1] <-> t[1,2,1,0])
(t[1,2,1] <-> t[1,2,2])
(t[1,2,1,0] <-> arg2[])
(t[1,2,2] <-> t[1,2,2,0])
(t[1,2,2,0] <-> arg2[])
(t'[1,2,1,0] <-> arg3[])
(ts[1,2] <-> (ts[1,2,1] | ts[1,2,2]))
(ts[1,2,1] <-> ts[1,2,1,1])
(ts[1,2,1] <-> ts[1,2,2])
(ts[1,2,2] <-> ts[1,2,2,0])
(ts[1,2,2,0] <-> arg3[])
1
-}

filter = R3 { callIII = filterP1III, callIIO = filterP1IIO }
  where
    filterP1III = \p arg2 arg3 -> Logic.once $ do
      -- solution: h[1,1] h0[1,0] h1[1,2,1,1] t[1,0] t'[1,2,1,1] ts[1,3] ~arg2[] ~arg2[0] ~arg2[0,0] ~arg2[1] ~arg2[1,0] ~arg3[] ~arg3[0] ~arg3[0,1] ~arg3[1] ~arg3[1,3] ~h[1,2] ~h[1,2,0,0] ~h[1,2,1,2] ~h0[1,1] ~h1[1,2,1,2] ~p[] ~p[1] ~p[1,2] ~p[1,2,1] ~p[1,2,1,0] ~p[1,2,2] ~p[1,2,2,0] ~t[1,2] ~t[1,2,1] ~t[1,2,1,0] ~t[1,2,2] ~t[1,2,2,0] ~t'[1,2,1,0] ~ts[1,2] ~ts[1,2,1] ~ts[1,2,1,1] ~ts[1,2,2] ~ts[1,2,2,0] ~p(1)
      -- cost: 3
      () <- (do
        guard $ arg2 == []
        guard $ arg3 == []
        pure ()
       ) <|> (do
        ts <- pure arg3
        (h0:t) <- pure arg2
        h <- pure h0
        () <- Logic.ifte ((do
          () <- callI p h
          pure ()
         )) (\() -> (do
          (h1:t') <- pure ts
          guard $ h1 == h
          () <- callIII filter p t t'
          pure ()
         )) ((do
          () <- callIII filter p t ts
          pure ()
         ))
        pure ()
       )
      pure ()
    
    filterP1IIO = \p arg2 -> do
      -- solution: arg3[] arg3[0] arg3[0,1] arg3[1] arg3[1,3] h[1,1] h0[1,0] h1[1,2,1,2] t[1,0] t'[1,2,1,0] ts[1,2] ts[1,2,1] ts[1,2,1,1] ts[1,2,2] ts[1,2,2,0] ~arg2[] ~arg2[0] ~arg2[0,0] ~arg2[1] ~arg2[1,0] ~h[1,2] ~h[1,2,0,0] ~h[1,2,1,2] ~h0[1,1] ~h1[1,2,1,1] ~p[] ~p[1] ~p[1,2] ~p[1,2,1] ~p[1,2,1,0] ~p[1,2,2] ~p[1,2,2,0] ~t[1,2] ~t[1,2,1] ~t[1,2,1,0] ~t[1,2,2] ~t[1,2,2,0] ~t'[1,2,1,1] ~ts[1,3] ~p(1)
      -- cost: 5
      (arg3) <- (do
        guard $ arg2 == []
        arg3 <- pure []
        pure (arg3)
       ) <|> (do
        (h0:t) <- pure arg2
        h <- pure h0
        (ts) <- Logic.ifte ((do
          () <- callI p h
          pure ()
         )) (\() -> (do
          h1 <- pure h
          (t') <- callIIO filter p t
          ts <- pure (h1:t')
          pure (ts)
         )) ((do
          (ts) <- callIIO filter p t
          pure (ts)
         ))
        arg3 <- pure ts
        pure (arg3)
       )
      pure (arg3)
    
{- evens/2
evens xs ys :- ((filter pred0 xs ys, (pred0 x :- (even x)))).
constraints:
~pred0[0,0]
~x[0]
~x[0,1,0,0]
((~pred0[0,0] & (~pred0(1) & (~xs[0,0] & ys[0,0]))) | (~pred0[0,0] & (~pred0(1) & (~xs[0,0] & ~ys[0,0]))))
(x[0,1,0] <-> x[0,1,0,0])
(xs[] <-> xs[0])
(xs[0] <-> xs[0,0])
(ys[] <-> ys[0])
(ys[0] <-> ys[0,0])
(pred0(1) <-> x[0,1,0])
1
-}

evens = R2 { callII = evensII, callIO = evensIO }
  where
    evensII = \xs ys -> Logic.once $ do
      -- solution: ~pred0[0,0] ~x[0] ~x[0,1,0] ~x[0,1,0,0] ~xs[] ~xs[0] ~xs[0,0] ~ys[] ~ys[0] ~ys[0,0] ~pred0(1)
      -- cost: 2
      () <- (do
        let pred0 = R1 { callI =
              \x -> do
                () <- (do
                  () <- callI even x
                  pure ()
                 )
                pure ()
              }
        () <- callIII filter pred0 xs ys
        pure ()
       )
      pure ()
    
    evensIO = \xs -> do
      -- solution: ys[] ys[0] ys[0,0] ~pred0[0,0] ~x[0] ~x[0,1,0] ~x[0,1,0,0] ~xs[] ~xs[0] ~xs[0,0] ~pred0(1)
      -- cost: 3
      (ys) <- (do
        let pred0 = R1 { callI =
              \x -> do
                () <- (do
                  () <- callI even x
                  pure ()
                 )
                pure ()
              }
        (ys) <- callIIO filter pred0 xs
        pure (ys)
       )
      pure (ys)
    
{- foldl/4
foldl p arg2 a arg4 :- ((arg2 = [], arg4 = a); (arg2 = h:t, p h a a', foldl p t a' a'', arg4 = a'')).
constraints:
~p[]
~(a'[1,1] & a'[1,2])
~(a''[1,2] & a''[1,3])
~(arg2[1,0] & h[1,0])
~(arg4[0,1] & a[0,1])
~(arg4[1,3] & a''[1,3])
~(h[1,0] & h[1,1])
~(t[1,0] & t[1,2])
(a'[1,1] | a'[1,2])
(a''[1,2] | a''[1,3])
(h[1,0] | h[1,1])
(t[1,0] | t[1,2])
(a[] <-> a[0])
(a[] <-> a[1])
(a[0] <-> a[0,1])
(a[1] <-> a[1,1])
(a[1,1] <-> p(2))
(a'[1,1] <-> p(3))
(a'[1,2] <-> a[])
(a''[1,2] <-> arg4[])
(arg2[] <-> arg2[0])
(arg2[] <-> arg2[1])
(arg2[0] <-> arg2[0,0])
(arg2[1] <-> arg2[1,0])
(arg4[] <-> arg4[0])
(arg4[] <-> arg4[1])
(arg4[0] <-> arg4[0,1])
(arg4[1] <-> arg4[1,3])
(h[1,0] <-> t[1,0])
(h[1,1] <-> p(1))
(p[] <-> p[1])
(p[1] <-> p[1,2])
(p[1,2] <-> p[])
(t[1,2] <-> arg2[])
1
-}

foldl = R4 { callIIII = foldlP3IIOIII, callIIIO = foldlP3IIOIIO, callIIOI = foldlP3IOIIOI, callIOII = foldlP3OIOOII, callIOIO = foldlP3OIOOIO, callIOOI = foldlP3OOIOOI }
  where
    foldlP3IIOIII = \p arg2 a arg4 -> Logic.once $ do
      -- solution: a'[1,1] a''[1,3] h[1,0] t[1,0] p(3) ~a[] ~a[0] ~a[0,1] ~a[1] ~a[1,1] ~a'[1,2] ~a''[1,2] ~arg2[] ~arg2[0] ~arg2[0,0] ~arg2[1] ~arg2[1,0] ~arg4[] ~arg4[0] ~arg4[0,1] ~arg4[1] ~arg4[1,3] ~h[1,1] ~p[] ~p[1] ~p[1,2] ~t[1,2] ~p(1) ~p(2)
      -- cost: 3
      () <- (do
        guard $ arg4 == a
        guard $ arg2 == []
        pure ()
       ) <|> (do
        a'' <- pure arg4
        (h:t) <- pure arg2
        (a') <- callIIO p h a
        () <- callIIII foldl p t a' a''
        pure ()
       )
      pure ()
    
    foldlP3IIOIIO = \p arg2 a -> do
      -- solution: a'[1,1] a''[1,2] arg4[] arg4[0] arg4[0,1] arg4[1] arg4[1,3] h[1,0] t[1,0] p(3) ~a[] ~a[0] ~a[0,1] ~a[1] ~a[1,1] ~a'[1,2] ~a''[1,3] ~arg2[] ~arg2[0] ~arg2[0,0] ~arg2[1] ~arg2[1,0] ~h[1,1] ~p[] ~p[1] ~p[1,2] ~t[1,2] ~p(1) ~p(2)
      -- cost: 4
      (arg4) <- (do
        arg4 <- pure a
        guard $ arg2 == []
        pure (arg4)
       ) <|> (do
        (h:t) <- pure arg2
        (a') <- callIIO p h a
        (a'') <- callIIIO foldl p t a'
        arg4 <- pure a''
        pure (arg4)
       )
      pure (arg4)
    
    foldlP3IOIIOI = \p arg2 arg4 -> do
      -- solution: a[] a[0] a[0,1] a[1] a[1,1] a'[1,2] a''[1,3] h[1,0] t[1,0] p(2) ~a'[1,1] ~a''[1,2] ~arg2[] ~arg2[0] ~arg2[0,0] ~arg2[1] ~arg2[1,0] ~arg4[] ~arg4[0] ~arg4[0,1] ~arg4[1] ~arg4[1,3] ~h[1,1] ~p[] ~p[1] ~p[1,2] ~t[1,2] ~p(1) ~p(3)
      -- cost: 4
      (a) <- (do
        a <- pure arg4
        guard $ arg2 == []
        pure (a)
       ) <|> (do
        a'' <- pure arg4
        (h:t) <- pure arg2
        (a') <- callIIOI foldl p t a''
        (a) <- callIOI p h a'
        pure (a)
       )
      pure (a)
    
    foldlP3OIOOII = \p a arg4 -> do
      -- solution: a'[1,1] a''[1,3] arg2[] arg2[0] arg2[0,0] arg2[1] arg2[1,0] h[1,1] t[1,2] p(1) p(3) ~a[] ~a[0] ~a[0,1] ~a[1] ~a[1,1] ~a'[1,2] ~a''[1,2] ~arg4[] ~arg4[0] ~arg4[0,1] ~arg4[1] ~arg4[1,3] ~h[1,0] ~p[] ~p[1] ~p[1,2] ~t[1,0] ~p(2)
      -- cost: 5
      (arg2) <- (do
        guard $ arg4 == a
        arg2 <- pure []
        pure (arg2)
       ) <|> (do
        a'' <- pure arg4
        (h,a') <- callOIO p a
        (t) <- callIOII foldl p a' a''
        arg2 <- pure (h:t)
        pure (arg2)
       )
      pure (arg2)
    
    foldlP3OIOOIO = \p a -> do
      -- solution: a'[1,1] a''[1,2] arg2[] arg2[0] arg2[0,0] arg2[1] arg2[1,0] arg4[] arg4[0] arg4[0,1] arg4[1] arg4[1,3] h[1,1] t[1,2] p(1) p(3) ~a[] ~a[0] ~a[0,1] ~a[1] ~a[1,1] ~a'[1,2] ~a''[1,3] ~h[1,0] ~p[] ~p[1] ~p[1,2] ~t[1,0] ~p(2)
      -- cost: 6
      (arg2,arg4) <- (do
        arg4 <- pure a
        arg2 <- pure []
        pure (arg2,arg4)
       ) <|> (do
        (h,a') <- callOIO p a
        (t,a'') <- callIOIO foldl p a'
        arg4 <- pure a''
        arg2 <- pure (h:t)
        pure (arg2,arg4)
       )
      pure (arg2,arg4)
    
    foldlP3OOIOOI = \p arg4 -> do
      -- solution: a[] a[0] a[0,1] a[1] a[1,1] a'[1,2] a''[1,3] arg2[] arg2[0] arg2[0,0] arg2[1] arg2[1,0] h[1,1] t[1,2] p(1) p(2) ~a'[1,1] ~a''[1,2] ~arg4[] ~arg4[0] ~arg4[0,1] ~arg4[1] ~arg4[1,3] ~h[1,0] ~p[] ~p[1] ~p[1,2] ~t[1,0] ~p(3)
      -- cost: 6
      (a,arg2) <- (do
        a <- pure arg4
        arg2 <- pure []
        pure (a,arg2)
       ) <|> (do
        a'' <- pure arg4
        (t,a') <- callIOOI foldl p a''
        (h,a) <- callOOI p a'
        arg2 <- pure (h:t)
        pure (a,arg2)
       )
      pure (arg2,a)
    
{- sum/3
sum xs z r :- ((foldl pred0 xs z r, (pred0 x a a' :- (plus x a a')))).
constraints:
~a[0]
~a'[0]
~pred0[0,0]
~x[0]
((x[0,1,0,0] & (~a[0,1,0,0] & ~a'[0,1,0,0])) | ((~x[0,1,0,0] & (a[0,1,0,0] & ~a'[0,1,0,0])) | (~x[0,1,0,0] & (~a[0,1,0,0] & a'[0,1,0,0]))))
((~pred0[0,0] & (pred0(1) & (pred0(2) & (~pred0(3) & (xs[0,0] & (z[0,0] & ~r[0,0])))))) | ((~pred0[0,0] & (pred0(1) & (~pred0(2) & (pred0(3) & (xs[0,0] & (~z[0,0] & r[0,0])))))) | ((~pred0[0,0] & (pred0(1) & (~pred0(2) & (pred0(3) & (xs[0,0] & (~z[0,0] & ~r[0,0])))))) | ((~pred0[0,0] & (~pred0(1) & (pred0(2) & (~pred0(3) & (~xs[0,0] & (z[0,0] & ~r[0,0])))))) | ((~pred0[0,0] & (~pred0(1) & (~pred0(2) & (pred0(3) & (~xs[0,0] & (~z[0,0] & r[0,0])))))) | (~pred0[0,0] & (~pred0(1) & (~pred0(2) & (pred0(3) & (~xs[0,0] & (~z[0,0] & ~r[0,0])))))))))))
(a[0,1,0] <-> a[0,1,0,0])
(a'[0,1,0] <-> a'[0,1,0,0])
(r[] <-> r[0])
(r[0] <-> r[0,0])
(x[0,1,0] <-> x[0,1,0,0])
(xs[] <-> xs[0])
(xs[0] <-> xs[0,0])
(z[] <-> z[0])
(z[0] <-> z[0,0])
(pred0(1) <-> x[0,1,0])
(pred0(2) <-> a[0,1,0])
(pred0(3) <-> a'[0,1,0])
1
-}

sum = R3 { callIII = sumIII, callIIO = sumIIO, callIOI = sumIOI }
  where
    sumIII = \xs z r -> Logic.once $ do
      -- solution: a'[0,1,0] a'[0,1,0,0] pred0(3) ~a[0] ~a[0,1,0] ~a[0,1,0,0] ~a'[0] ~pred0[0,0] ~r[] ~r[0] ~r[0,0] ~x[0] ~x[0,1,0] ~x[0,1,0,0] ~xs[] ~xs[0] ~xs[0,0] ~z[] ~z[0] ~z[0,0] ~pred0(1) ~pred0(2)
      -- cost: 3
      () <- (do
        let pred0 = R3 { callIIO =
              \x a -> do
                (a') <- (do
                  (a') <- callIIO plus x a
                  pure (a')
                 )
                pure (a')
              }
        () <- callIIII foldl pred0 xs z r
        pure ()
       )
      pure ()
    
    sumIIO = \xs z -> do
      -- solution: a'[0,1,0] a'[0,1,0,0] r[] r[0] r[0,0] pred0(3) ~a[0] ~a[0,1,0] ~a[0,1,0,0] ~a'[0] ~pred0[0,0] ~x[0] ~x[0,1,0] ~x[0,1,0,0] ~xs[] ~xs[0] ~xs[0,0] ~z[] ~z[0] ~z[0,0] ~pred0(1) ~pred0(2)
      -- cost: 4
      (r) <- (do
        let pred0 = R3 { callIIO =
              \x a -> do
                (a') <- (do
                  (a') <- callIIO plus x a
                  pure (a')
                 )
                pure (a')
              }
        (r) <- callIIIO foldl pred0 xs z
        pure (r)
       )
      pure (r)
    
    sumIOI = \xs r -> do
      -- solution: a[0,1,0] a[0,1,0,0] z[] z[0] z[0,0] pred0(2) ~a[0] ~a'[0] ~a'[0,1,0] ~a'[0,1,0,0] ~pred0[0,0] ~r[] ~r[0] ~r[0,0] ~x[0] ~x[0,1,0] ~x[0,1,0,0] ~xs[] ~xs[0] ~xs[0,0] ~pred0(1) ~pred0(3)
      -- cost: 4
      (z) <- (do
        let pred0 = R3 { callIOI =
              \x a' -> do
                (a) <- (do
                  (a) <- callIOI plus x a'
                  pure (a)
                 )
                pure (a)
              }
        (z) <- callIIOI foldl pred0 xs r
        pure (z)
       )
      pure (z)
    
{- split/3
split xs z r :- ((foldl pred0 xs z r, (pred0 x a a' :- (a = x:a')))).
constraints:
~a[0]
~a'[0]
~pred0[0,0]
~x[0]
~(a[0,1,0,0] & x[0,1,0,0])
((~pred0[0,0] & (pred0(1) & (pred0(2) & (~pred0(3) & (xs[0,0] & (z[0,0] & ~r[0,0])))))) | ((~pred0[0,0] & (pred0(1) & (~pred0(2) & (pred0(3) & (xs[0,0] & (~z[0,0] & r[0,0])))))) | ((~pred0[0,0] & (pred0(1) & (~pred0(2) & (pred0(3) & (xs[0,0] & (~z[0,0] & ~r[0,0])))))) | ((~pred0[0,0] & (~pred0(1) & (pred0(2) & (~pred0(3) & (~xs[0,0] & (z[0,0] & ~r[0,0])))))) | ((~pred0[0,0] & (~pred0(1) & (~pred0(2) & (pred0(3) & (~xs[0,0] & (~z[0,0] & r[0,0])))))) | (~pred0[0,0] & (~pred0(1) & (~pred0(2) & (pred0(3) & (~xs[0,0] & (~z[0,0] & ~r[0,0])))))))))))
(a[0,1,0] <-> a[0,1,0,0])
(a'[0,1,0] <-> a'[0,1,0,0])
(r[] <-> r[0])
(r[0] <-> r[0,0])
(x[0,1,0] <-> x[0,1,0,0])
(x[0,1,0,0] <-> a'[0,1,0,0])
(xs[] <-> xs[0])
(xs[0] <-> xs[0,0])
(z[] <-> z[0])
(z[0] <-> z[0,0])
(pred0(1) <-> x[0,1,0])
(pred0(2) <-> a[0,1,0])
(pred0(3) <-> a'[0,1,0])
1
-}

split = R3 { callIOI = splitIOI, callOII = splitOII, callOIO = splitOIO }
  where
    splitIOI = \xs r -> do
      -- solution: a[0,1,0] a[0,1,0,0] z[] z[0] z[0,0] pred0(2) ~a[0] ~a'[0] ~a'[0,1,0] ~a'[0,1,0,0] ~pred0[0,0] ~r[] ~r[0] ~r[0,0] ~x[0] ~x[0,1,0] ~x[0,1,0,0] ~xs[] ~xs[0] ~xs[0,0] ~pred0(1) ~pred0(3)
      -- cost: 2
      (z) <- (do
        let pred0 = R3 { callIOI =
              \x a' -> do
                (a) <- (do
                  a <- pure (x:a')
                  pure (a)
                 )
                pure (a)
              }
        (z) <- callIIOI foldl pred0 xs r
        pure (z)
       )
      pure (z)
    
    splitOII = \z r -> do
      -- solution: a'[0,1,0] a'[0,1,0,0] x[0,1,0] x[0,1,0,0] xs[] xs[0] xs[0,0] pred0(1) pred0(3) ~a[0] ~a[0,1,0] ~a[0,1,0,0] ~a'[0] ~pred0[0,0] ~r[] ~r[0] ~r[0,0] ~x[0] ~z[] ~z[0] ~z[0,0] ~pred0(2)
      -- cost: 2
      (xs) <- (do
        let pred0 = R3 { callOIO =
              \a -> do
                (a',x) <- (do
                  (x:a') <- pure a
                  pure (a',x)
                 )
                pure (x,a')
              }
        (xs) <- callIOII foldl pred0 z r
        pure (xs)
       )
      pure (xs)
    
    splitOIO = \z -> do
      -- solution: a'[0,1,0] a'[0,1,0,0] r[] r[0] r[0,0] x[0,1,0] x[0,1,0,0] xs[] xs[0] xs[0,0] pred0(1) pred0(3) ~a[0] ~a[0,1,0] ~a[0,1,0,0] ~a'[0] ~pred0[0,0] ~x[0] ~z[] ~z[0] ~z[0,0] ~pred0(2)
      -- cost: 3
      (r,xs) <- (do
        let pred0 = R3 { callOIO =
              \a -> do
                (a',x) <- (do
                  (x:a') <- pure a
                  pure (a',x)
                 )
                pure (x,a')
              }
        (xs,r) <- callIOIO foldl pred0 z
        pure (r,xs)
       )
      pure (xs,r)
    
{- splitr/3
splitr xs z r :- ((foldl pred0 xs z r, (pred0 x a a' :- (a' = x:a)))).
constraints:
~a[0]
~a'[0]
~pred0[0,0]
~x[0]
~(a'[0,1,0,0] & x[0,1,0,0])
((~pred0[0,0] & (pred0(1) & (pred0(2) & (~pred0(3) & (xs[0,0] & (z[0,0] & ~r[0,0])))))) | ((~pred0[0,0] & (pred0(1) & (~pred0(2) & (pred0(3) & (xs[0,0] & (~z[0,0] & r[0,0])))))) | ((~pred0[0,0] & (pred0(1) & (~pred0(2) & (pred0(3) & (xs[0,0] & (~z[0,0] & ~r[0,0])))))) | ((~pred0[0,0] & (~pred0(1) & (pred0(2) & (~pred0(3) & (~xs[0,0] & (z[0,0] & ~r[0,0])))))) | ((~pred0[0,0] & (~pred0(1) & (~pred0(2) & (pred0(3) & (~xs[0,0] & (~z[0,0] & r[0,0])))))) | (~pred0[0,0] & (~pred0(1) & (~pred0(2) & (pred0(3) & (~xs[0,0] & (~z[0,0] & ~r[0,0])))))))))))
(a[0,1,0] <-> a[0,1,0,0])
(a'[0,1,0] <-> a'[0,1,0,0])
(r[] <-> r[0])
(r[0] <-> r[0,0])
(x[0,1,0] <-> x[0,1,0,0])
(x[0,1,0,0] <-> a[0,1,0,0])
(xs[] <-> xs[0])
(xs[0] <-> xs[0,0])
(z[] <-> z[0])
(z[0] <-> z[0,0])
(pred0(1) <-> x[0,1,0])
(pred0(2) <-> a[0,1,0])
(pred0(3) <-> a'[0,1,0])
1
-}

splitr = R3 { callIII = splitrIII, callIIO = splitrIIO, callOOI = splitrOOI }
  where
    splitrIII = \xs z r -> Logic.once $ do
      -- solution: a'[0,1,0] a'[0,1,0,0] pred0(3) ~a[0] ~a[0,1,0] ~a[0,1,0,0] ~a'[0] ~pred0[0,0] ~r[] ~r[0] ~r[0,0] ~x[0] ~x[0,1,0] ~x[0,1,0,0] ~xs[] ~xs[0] ~xs[0,0] ~z[] ~z[0] ~z[0,0] ~pred0(1) ~pred0(2)
      -- cost: 1
      () <- (do
        let pred0 = R3 { callIIO =
              \x a -> do
                (a') <- (do
                  a' <- pure (x:a)
                  pure (a')
                 )
                pure (a')
              }
        () <- callIIII foldl pred0 xs z r
        pure ()
       )
      pure ()
    
    splitrIIO = \xs z -> do
      -- solution: a'[0,1,0] a'[0,1,0,0] r[] r[0] r[0,0] pred0(3) ~a[0] ~a[0,1,0] ~a[0,1,0,0] ~a'[0] ~pred0[0,0] ~x[0] ~x[0,1,0] ~x[0,1,0,0] ~xs[] ~xs[0] ~xs[0,0] ~z[] ~z[0] ~z[0,0] ~pred0(1) ~pred0(2)
      -- cost: 2
      (r) <- (do
        let pred0 = R3 { callIIO =
              \x a -> do
                (a') <- (do
                  a' <- pure (x:a)
                  pure (a')
                 )
                pure (a')
              }
        (r) <- callIIIO foldl pred0 xs z
        pure (r)
       )
      pure (r)
    
    splitrOOI = \r -> do
      -- solution: a[0,1,0] a[0,1,0,0] x[0,1,0] x[0,1,0,0] xs[] xs[0] xs[0,0] z[] z[0] z[0,0] pred0(1) pred0(2) ~a[0] ~a'[0] ~a'[0,1,0] ~a'[0,1,0,0] ~pred0[0,0] ~r[] ~r[0] ~r[0,0] ~x[0] ~pred0(3)
      -- cost: 3
      (xs,z) <- (do
        let pred0 = R3 { callOOI =
              \a' -> do
                (a,x) <- (do
                  (x:a) <- pure a'
                  pure (a,x)
                 )
                pure (x,a)
              }
        (xs,z) <- callIOOI foldl pred0 r
        pure (xs,z)
       )
      pure (xs,z)
    