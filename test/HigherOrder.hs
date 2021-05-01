{-# LANGUAGE DataKinds, FlexibleContexts, NoImplicitPrelude, NoMonomorphismRestriction, TypeApplications #-}
module HigherOrder where

import qualified Control.Monad.Logic as Logic
import Control.Monad.Logic.Moded.Prelude

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

even = rget $ (procedure @'[ 'In ] evenI) :& RNil
  where
    evenI = \n -> Logic.once $ do
      -- solution: data0[0,1] data1[0,2] ~data0[0,0] ~data1[0,0] ~n[] ~n[0] ~n[0,0]
      -- cost: 1
      () <- (do
        data1 <- pure 0
        data0 <- pure 2
        () <- runProcedure @'[ 'In, 'In, 'In ] mod n data0 data1
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

map = rget $ (procedure @'[ 'PredMode '[ 'In, 'In ], 'In, 'In ] mapP2IIII) :& (procedure @'[ 'PredMode '[ 'In, 'Out ], 'In, 'Out ] mapP2IOIO) :& (procedure @'[ 'PredMode '[ 'Out, 'In ], 'Out, 'In ] mapP2OIOI) :& (procedure @'[ 'PredMode '[ 'Out, 'Out ], 'Out, 'Out ] mapP2OOOO) :& RNil
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
        () <- mapP2IIII p xs ys
        () <- runProcedure p x y
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
        (OneTuple (ys)) <- mapP2IOIO p xs
        (OneTuple (y)) <- runProcedure p x
        arg3 <- pure (y:ys)
        pure (arg3)
       )
      pure (OneTuple (arg3))
    
    mapP2OIOI = \p arg3 -> do
      -- solution: arg2[] arg2[0] arg2[0,0] arg2[1] arg2[1,0] x[1,2] xs[1,3] y[1,1] ys[1,1] p(1) ~arg3[] ~arg3[0] ~arg3[0,1] ~arg3[1] ~arg3[1,1] ~p[] ~p[1] ~p[1,3] ~x[1,0] ~xs[1,0] ~y[1,2] ~ys[1,3] ~p(2)
      -- cost: 4
      (arg2) <- (do
        arg2 <- pure []
        guard $ arg3 == []
        pure (arg2)
       ) <|> (do
        (y:ys) <- pure arg3
        (OneTuple (xs)) <- mapP2OIOI p ys
        (OneTuple (x)) <- runProcedure p y
        arg2 <- pure (x:xs)
        pure (arg2)
       )
      pure (OneTuple (arg2))
    
    mapP2OOOO = \p -> do
      -- solution: arg2[] arg2[0] arg2[0,0] arg2[1] arg2[1,0] arg3[] arg3[0] arg3[0,1] arg3[1] arg3[1,1] x[1,2] xs[1,3] y[1,2] ys[1,3] p(1) p(2) ~p[] ~p[1] ~p[1,3] ~x[1,0] ~xs[1,0] ~y[1,1] ~ys[1,1]
      -- cost: 6
      (arg2,arg3) <- (do
        arg2 <- pure []
        arg3 <- pure []
        pure (arg2,arg3)
       ) <|> (do
        (xs,ys) <- mapP2OOOO p
        (x,y) <- runProcedure p 
        arg2 <- pure (x:xs)
        arg3 <- pure (y:ys)
        pure (arg2,arg3)
       )
      pure (arg2,arg3)
    
{- succs/2
succs xs ys :- ((map pred0 xs ys, (pred0 curry1 curry2 :- (succ curry1 curry2)))).
constraints:
~curry1[0]
~curry2[0]
~pred0[0,0]
((curry1[0,1,0,0] & ~curry2[0,1,0,0]) | ((~curry1[0,1,0,0] & curry2[0,1,0,0]) | (~curry1[0,1,0,0] & ~curry2[0,1,0,0])))
((~pred0[0,0] & (pred0(1) & (pred0(2) & (xs[0,0] & ys[0,0])))) | ((~pred0[0,0] & (pred0(1) & (~pred0(2) & (xs[0,0] & ~ys[0,0])))) | ((~pred0[0,0] & (~pred0(1) & (pred0(2) & (~xs[0,0] & ys[0,0])))) | (~pred0[0,0] & (~pred0(1) & (~pred0(2) & (~xs[0,0] & ~ys[0,0])))))))
(curry1[0,1,0] <-> curry1[0,1,0,0])
(curry2[0,1,0] <-> curry2[0,1,0,0])
(xs[] <-> xs[0])
(xs[0] <-> xs[0,0])
(ys[] <-> ys[0])
(ys[0] <-> ys[0,0])
(pred0(1) <-> curry1[0,1,0])
(pred0(2) <-> curry2[0,1,0])
1
-}

succs = rget $ (procedure @'[ 'In, 'In ] succsII) :& (procedure @'[ 'In, 'Out ] succsIO) :& (procedure @'[ 'Out, 'In ] succsOI) :& RNil
  where
    succsII = \xs ys -> Logic.once $ do
      -- solution: ~curry1[0] ~curry1[0,1,0] ~curry1[0,1,0,0] ~curry2[0] ~curry2[0,1,0] ~curry2[0,1,0,0] ~pred0[0,0] ~xs[] ~xs[0] ~xs[0,0] ~ys[] ~ys[0] ~ys[0,0] ~pred0(1) ~pred0(2)
      -- cost: 2
      () <- (do
        let pred0 = procedure @'[ 'In, 'In ] $
              \curry1 curry2 -> do
                () <- (do
                  () <- runProcedure @'[ 'In, 'In ] succ curry1 curry2
                  pure ()
                 )
                pure ()
        () <- runProcedure @'[ 'PredMode '[ 'In, 'In ], 'In, 'In ] map pred0 xs ys
        pure ()
       )
      pure ()
    
    succsIO = \xs -> do
      -- solution: curry2[0,1,0] curry2[0,1,0,0] ys[] ys[0] ys[0,0] pred0(2) ~curry1[0] ~curry1[0,1,0] ~curry1[0,1,0,0] ~curry2[0] ~pred0[0,0] ~xs[] ~xs[0] ~xs[0,0] ~pred0(1)
      -- cost: 4
      (ys) <- (do
        let pred0 = procedure @'[ 'In, 'Out ] $
              \curry1 -> do
                (curry2) <- (do
                  (OneTuple (curry2)) <- runProcedure @'[ 'In, 'Out ] succ curry1
                  pure (curry2)
                 )
                pure (OneTuple (curry2))
        (OneTuple (ys)) <- runProcedure @'[ 'PredMode '[ 'In, 'Out ], 'In, 'Out ] map pred0 xs
        pure (ys)
       )
      pure (OneTuple (ys))
    
    succsOI = \ys -> do
      -- solution: curry1[0,1,0] curry1[0,1,0,0] xs[] xs[0] xs[0,0] pred0(1) ~curry1[0] ~curry2[0] ~curry2[0,1,0] ~curry2[0,1,0,0] ~pred0[0,0] ~ys[] ~ys[0] ~ys[0,0] ~pred0(2)
      -- cost: 4
      (xs) <- (do
        let pred0 = procedure @'[ 'Out, 'In ] $
              \curry2 -> do
                (curry1) <- (do
                  (OneTuple (curry1)) <- runProcedure @'[ 'Out, 'In ] succ curry2
                  pure (curry1)
                 )
                pure (OneTuple (curry1))
        (OneTuple (xs)) <- runProcedure @'[ 'PredMode '[ 'Out, 'In ], 'Out, 'In ] map pred0 ys
        pure (xs)
       )
      pure (OneTuple (xs))
    
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

filter = rget $ (procedure @'[ 'PredMode '[ 'In ], 'In, 'In ] filterP1III) :& (procedure @'[ 'PredMode '[ 'In ], 'In, 'Out ] filterP1IIO) :& RNil
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
          () <- runProcedure p h
          pure ()
         )) (\() -> (do
          (h1:t') <- pure ts
          guard $ h1 == h
          () <- filterP1III p t t'
          pure ()
         )) ((do
          () <- filterP1III p t ts
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
          () <- runProcedure p h
          pure ()
         )) (\() -> (do
          h1 <- pure h
          (OneTuple (t')) <- filterP1IIO p t
          ts <- pure (h1:t')
          pure (ts)
         )) ((do
          (OneTuple (ts)) <- filterP1IIO p t
          pure (ts)
         ))
        arg3 <- pure ts
        pure (arg3)
       )
      pure (OneTuple (arg3))
    
{- evens/2
evens xs ys :- ((filter pred0 xs ys, (pred0 curry1 :- (even curry1)))).
constraints:
~curry1[0]
~curry1[0,1,0,0]
~pred0[0,0]
((~pred0[0,0] & (~pred0(1) & (~xs[0,0] & ys[0,0]))) | (~pred0[0,0] & (~pred0(1) & (~xs[0,0] & ~ys[0,0]))))
(curry1[0,1,0] <-> curry1[0,1,0,0])
(xs[] <-> xs[0])
(xs[0] <-> xs[0,0])
(ys[] <-> ys[0])
(ys[0] <-> ys[0,0])
(pred0(1) <-> curry1[0,1,0])
1
-}

evens = rget $ (procedure @'[ 'In, 'In ] evensII) :& (procedure @'[ 'In, 'Out ] evensIO) :& RNil
  where
    evensII = \xs ys -> Logic.once $ do
      -- solution: ~curry1[0] ~curry1[0,1,0] ~curry1[0,1,0,0] ~pred0[0,0] ~xs[] ~xs[0] ~xs[0,0] ~ys[] ~ys[0] ~ys[0,0] ~pred0(1)
      -- cost: 2
      () <- (do
        let pred0 = procedure @'[ 'In ] $
              \curry1 -> do
                () <- (do
                  () <- runProcedure @'[ 'In ] even curry1
                  pure ()
                 )
                pure ()
        () <- runProcedure @'[ 'PredMode '[ 'In ], 'In, 'In ] filter pred0 xs ys
        pure ()
       )
      pure ()
    
    evensIO = \xs -> do
      -- solution: ys[] ys[0] ys[0,0] ~curry1[0] ~curry1[0,1,0] ~curry1[0,1,0,0] ~pred0[0,0] ~xs[] ~xs[0] ~xs[0,0] ~pred0(1)
      -- cost: 3
      (ys) <- (do
        let pred0 = procedure @'[ 'In ] $
              \curry1 -> do
                () <- (do
                  () <- runProcedure @'[ 'In ] even curry1
                  pure ()
                 )
                pure ()
        (OneTuple (ys)) <- runProcedure @'[ 'PredMode '[ 'In ], 'In, 'Out ] filter pred0 xs
        pure (ys)
       )
      pure (OneTuple (ys))
    
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

foldl = rget $ (procedure @'[ 'PredMode '[ 'In, 'In, 'Out ], 'In, 'In, 'In ] foldlP3IIOIII) :& (procedure @'[ 'PredMode '[ 'In, 'In, 'Out ], 'In, 'In, 'Out ] foldlP3IIOIIO) :& (procedure @'[ 'PredMode '[ 'In, 'Out, 'In ], 'In, 'Out, 'In ] foldlP3IOIIOI) :& (procedure @'[ 'PredMode '[ 'Out, 'In, 'Out ], 'Out, 'In, 'In ] foldlP3OIOOII) :& (procedure @'[ 'PredMode '[ 'Out, 'In, 'Out ], 'Out, 'In, 'Out ] foldlP3OIOOIO) :& (procedure @'[ 'PredMode '[ 'Out, 'Out, 'In ], 'Out, 'Out, 'In ] foldlP3OOIOOI) :& RNil
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
        (OneTuple (a')) <- runProcedure p h a
        () <- foldlP3IIOIII p t a' a''
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
        (OneTuple (a')) <- runProcedure p h a
        (OneTuple (a'')) <- foldlP3IIOIIO p t a'
        arg4 <- pure a''
        pure (arg4)
       )
      pure (OneTuple (arg4))
    
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
        (OneTuple (a')) <- foldlP3IOIIOI p t a''
        (OneTuple (a)) <- runProcedure p h a'
        pure (a)
       )
      pure (OneTuple (a))
    
    foldlP3OIOOII = \p a arg4 -> do
      -- solution: a'[1,1] a''[1,3] arg2[] arg2[0] arg2[0,0] arg2[1] arg2[1,0] h[1,1] t[1,2] p(1) p(3) ~a[] ~a[0] ~a[0,1] ~a[1] ~a[1,1] ~a'[1,2] ~a''[1,2] ~arg4[] ~arg4[0] ~arg4[0,1] ~arg4[1] ~arg4[1,3] ~h[1,0] ~p[] ~p[1] ~p[1,2] ~t[1,0] ~p(2)
      -- cost: 5
      (arg2) <- (do
        guard $ arg4 == a
        arg2 <- pure []
        pure (arg2)
       ) <|> (do
        a'' <- pure arg4
        (h,a') <- runProcedure p a
        (OneTuple (t)) <- foldlP3OIOOII p a' a''
        arg2 <- pure (h:t)
        pure (arg2)
       )
      pure (OneTuple (arg2))
    
    foldlP3OIOOIO = \p a -> do
      -- solution: a'[1,1] a''[1,2] arg2[] arg2[0] arg2[0,0] arg2[1] arg2[1,0] arg4[] arg4[0] arg4[0,1] arg4[1] arg4[1,3] h[1,1] t[1,2] p(1) p(3) ~a[] ~a[0] ~a[0,1] ~a[1] ~a[1,1] ~a'[1,2] ~a''[1,3] ~h[1,0] ~p[] ~p[1] ~p[1,2] ~t[1,0] ~p(2)
      -- cost: 6
      (arg2,arg4) <- (do
        arg4 <- pure a
        arg2 <- pure []
        pure (arg2,arg4)
       ) <|> (do
        (h,a') <- runProcedure p a
        (t,a'') <- foldlP3OIOOIO p a'
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
        (t,a') <- foldlP3OOIOOI p a''
        (h,a) <- runProcedure p a'
        arg2 <- pure (h:t)
        pure (a,arg2)
       )
      pure (arg2,a)
    
{- sum/3
sum xs z r :- ((foldl pred0 xs z r, (pred0 curry1 curry2 curry3 :- (plus curry1 curry2 curry3)))).
constraints:
~curry1[0]
~curry2[0]
~curry3[0]
~pred0[0,0]
((curry1[0,1,0,0] & (~curry2[0,1,0,0] & ~curry3[0,1,0,0])) | ((~curry1[0,1,0,0] & (curry2[0,1,0,0] & ~curry3[0,1,0,0])) | ((~curry1[0,1,0,0] & (~curry2[0,1,0,0] & curry3[0,1,0,0])) | (~curry1[0,1,0,0] & (~curry2[0,1,0,0] & ~curry3[0,1,0,0])))))
((~pred0[0,0] & (pred0(1) & (pred0(2) & (~pred0(3) & (xs[0,0] & (z[0,0] & ~r[0,0])))))) | ((~pred0[0,0] & (pred0(1) & (~pred0(2) & (pred0(3) & (xs[0,0] & (~z[0,0] & r[0,0])))))) | ((~pred0[0,0] & (pred0(1) & (~pred0(2) & (pred0(3) & (xs[0,0] & (~z[0,0] & ~r[0,0])))))) | ((~pred0[0,0] & (~pred0(1) & (pred0(2) & (~pred0(3) & (~xs[0,0] & (z[0,0] & ~r[0,0])))))) | ((~pred0[0,0] & (~pred0(1) & (~pred0(2) & (pred0(3) & (~xs[0,0] & (~z[0,0] & r[0,0])))))) | (~pred0[0,0] & (~pred0(1) & (~pred0(2) & (pred0(3) & (~xs[0,0] & (~z[0,0] & ~r[0,0])))))))))))
(curry1[0,1,0] <-> curry1[0,1,0,0])
(curry2[0,1,0] <-> curry2[0,1,0,0])
(curry3[0,1,0] <-> curry3[0,1,0,0])
(r[] <-> r[0])
(r[0] <-> r[0,0])
(xs[] <-> xs[0])
(xs[0] <-> xs[0,0])
(z[] <-> z[0])
(z[0] <-> z[0,0])
(pred0(1) <-> curry1[0,1,0])
(pred0(2) <-> curry2[0,1,0])
(pred0(3) <-> curry3[0,1,0])
1
-}

sum = rget $ (procedure @'[ 'In, 'In, 'In ] sumIII) :& (procedure @'[ 'In, 'In, 'Out ] sumIIO) :& (procedure @'[ 'In, 'Out, 'In ] sumIOI) :& RNil
  where
    sumIII = \xs z r -> Logic.once $ do
      -- solution: curry3[0,1,0] curry3[0,1,0,0] pred0(3) ~curry1[0] ~curry1[0,1,0] ~curry1[0,1,0,0] ~curry2[0] ~curry2[0,1,0] ~curry2[0,1,0,0] ~curry3[0] ~pred0[0,0] ~r[] ~r[0] ~r[0,0] ~xs[] ~xs[0] ~xs[0,0] ~z[] ~z[0] ~z[0,0] ~pred0(1) ~pred0(2)
      -- cost: 3
      () <- (do
        let pred0 = procedure @'[ 'In, 'In, 'Out ] $
              \curry1 curry2 -> do
                (curry3) <- (do
                  (OneTuple (curry3)) <- runProcedure @'[ 'In, 'In, 'Out ] plus curry1 curry2
                  pure (curry3)
                 )
                pure (OneTuple (curry3))
        () <- runProcedure @'[ 'PredMode '[ 'In, 'In, 'Out ], 'In, 'In, 'In ] foldl pred0 xs z r
        pure ()
       )
      pure ()
    
    sumIIO = \xs z -> do
      -- solution: curry3[0,1,0] curry3[0,1,0,0] r[] r[0] r[0,0] pred0(3) ~curry1[0] ~curry1[0,1,0] ~curry1[0,1,0,0] ~curry2[0] ~curry2[0,1,0] ~curry2[0,1,0,0] ~curry3[0] ~pred0[0,0] ~xs[] ~xs[0] ~xs[0,0] ~z[] ~z[0] ~z[0,0] ~pred0(1) ~pred0(2)
      -- cost: 4
      (r) <- (do
        let pred0 = procedure @'[ 'In, 'In, 'Out ] $
              \curry1 curry2 -> do
                (curry3) <- (do
                  (OneTuple (curry3)) <- runProcedure @'[ 'In, 'In, 'Out ] plus curry1 curry2
                  pure (curry3)
                 )
                pure (OneTuple (curry3))
        (OneTuple (r)) <- runProcedure @'[ 'PredMode '[ 'In, 'In, 'Out ], 'In, 'In, 'Out ] foldl pred0 xs z
        pure (r)
       )
      pure (OneTuple (r))
    
    sumIOI = \xs r -> do
      -- solution: curry2[0,1,0] curry2[0,1,0,0] z[] z[0] z[0,0] pred0(2) ~curry1[0] ~curry1[0,1,0] ~curry1[0,1,0,0] ~curry2[0] ~curry3[0] ~curry3[0,1,0] ~curry3[0,1,0,0] ~pred0[0,0] ~r[] ~r[0] ~r[0,0] ~xs[] ~xs[0] ~xs[0,0] ~pred0(1) ~pred0(3)
      -- cost: 4
      (z) <- (do
        let pred0 = procedure @'[ 'In, 'Out, 'In ] $
              \curry1 curry3 -> do
                (curry2) <- (do
                  (OneTuple (curry2)) <- runProcedure @'[ 'In, 'Out, 'In ] plus curry1 curry3
                  pure (curry2)
                 )
                pure (OneTuple (curry2))
        (OneTuple (z)) <- runProcedure @'[ 'PredMode '[ 'In, 'Out, 'In ], 'In, 'Out, 'In ] foldl pred0 xs r
        pure (z)
       )
      pure (OneTuple (z))
    
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

split = rget $ (procedure @'[ 'In, 'Out, 'In ] splitIOI) :& (procedure @'[ 'Out, 'In, 'In ] splitOII) :& (procedure @'[ 'Out, 'In, 'Out ] splitOIO) :& RNil
  where
    splitIOI = \xs r -> do
      -- solution: a[0,1,0] a[0,1,0,0] z[] z[0] z[0,0] pred0(2) ~a[0] ~a'[0] ~a'[0,1,0] ~a'[0,1,0,0] ~pred0[0,0] ~r[] ~r[0] ~r[0,0] ~x[0] ~x[0,1,0] ~x[0,1,0,0] ~xs[] ~xs[0] ~xs[0,0] ~pred0(1) ~pred0(3)
      -- cost: 2
      (z) <- (do
        let pred0 = procedure @'[ 'In, 'Out, 'In ] $
              \x a' -> do
                (a) <- (do
                  a <- pure (x:a')
                  pure (a)
                 )
                pure (OneTuple (a))
        (OneTuple (z)) <- runProcedure @'[ 'PredMode '[ 'In, 'Out, 'In ], 'In, 'Out, 'In ] foldl pred0 xs r
        pure (z)
       )
      pure (OneTuple (z))
    
    splitOII = \z r -> do
      -- solution: a'[0,1,0] a'[0,1,0,0] x[0,1,0] x[0,1,0,0] xs[] xs[0] xs[0,0] pred0(1) pred0(3) ~a[0] ~a[0,1,0] ~a[0,1,0,0] ~a'[0] ~pred0[0,0] ~r[] ~r[0] ~r[0,0] ~x[0] ~z[] ~z[0] ~z[0,0] ~pred0(2)
      -- cost: 2
      (xs) <- (do
        let pred0 = procedure @'[ 'Out, 'In, 'Out ] $
              \a -> do
                (a',x) <- (do
                  (x:a') <- pure a
                  pure (a',x)
                 )
                pure (x,a')
        (OneTuple (xs)) <- runProcedure @'[ 'PredMode '[ 'Out, 'In, 'Out ], 'Out, 'In, 'In ] foldl pred0 z r
        pure (xs)
       )
      pure (OneTuple (xs))
    
    splitOIO = \z -> do
      -- solution: a'[0,1,0] a'[0,1,0,0] r[] r[0] r[0,0] x[0,1,0] x[0,1,0,0] xs[] xs[0] xs[0,0] pred0(1) pred0(3) ~a[0] ~a[0,1,0] ~a[0,1,0,0] ~a'[0] ~pred0[0,0] ~x[0] ~z[] ~z[0] ~z[0,0] ~pred0(2)
      -- cost: 3
      (r,xs) <- (do
        let pred0 = procedure @'[ 'Out, 'In, 'Out ] $
              \a -> do
                (a',x) <- (do
                  (x:a') <- pure a
                  pure (a',x)
                 )
                pure (x,a')
        (xs,r) <- runProcedure @'[ 'PredMode '[ 'Out, 'In, 'Out ], 'Out, 'In, 'Out ] foldl pred0 z
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

splitr = rget $ (procedure @'[ 'In, 'In, 'In ] splitrIII) :& (procedure @'[ 'In, 'In, 'Out ] splitrIIO) :& (procedure @'[ 'Out, 'Out, 'In ] splitrOOI) :& RNil
  where
    splitrIII = \xs z r -> Logic.once $ do
      -- solution: a'[0,1,0] a'[0,1,0,0] pred0(3) ~a[0] ~a[0,1,0] ~a[0,1,0,0] ~a'[0] ~pred0[0,0] ~r[] ~r[0] ~r[0,0] ~x[0] ~x[0,1,0] ~x[0,1,0,0] ~xs[] ~xs[0] ~xs[0,0] ~z[] ~z[0] ~z[0,0] ~pred0(1) ~pred0(2)
      -- cost: 1
      () <- (do
        let pred0 = procedure @'[ 'In, 'In, 'Out ] $
              \x a -> do
                (a') <- (do
                  a' <- pure (x:a)
                  pure (a')
                 )
                pure (OneTuple (a'))
        () <- runProcedure @'[ 'PredMode '[ 'In, 'In, 'Out ], 'In, 'In, 'In ] foldl pred0 xs z r
        pure ()
       )
      pure ()
    
    splitrIIO = \xs z -> do
      -- solution: a'[0,1,0] a'[0,1,0,0] r[] r[0] r[0,0] pred0(3) ~a[0] ~a[0,1,0] ~a[0,1,0,0] ~a'[0] ~pred0[0,0] ~x[0] ~x[0,1,0] ~x[0,1,0,0] ~xs[] ~xs[0] ~xs[0,0] ~z[] ~z[0] ~z[0,0] ~pred0(1) ~pred0(2)
      -- cost: 2
      (r) <- (do
        let pred0 = procedure @'[ 'In, 'In, 'Out ] $
              \x a -> do
                (a') <- (do
                  a' <- pure (x:a)
                  pure (a')
                 )
                pure (OneTuple (a'))
        (OneTuple (r)) <- runProcedure @'[ 'PredMode '[ 'In, 'In, 'Out ], 'In, 'In, 'Out ] foldl pred0 xs z
        pure (r)
       )
      pure (OneTuple (r))
    
    splitrOOI = \r -> do
      -- solution: a[0,1,0] a[0,1,0,0] x[0,1,0] x[0,1,0,0] xs[] xs[0] xs[0,0] z[] z[0] z[0,0] pred0(1) pred0(2) ~a[0] ~a'[0] ~a'[0,1,0] ~a'[0,1,0,0] ~pred0[0,0] ~r[] ~r[0] ~r[0,0] ~x[0] ~pred0(3)
      -- cost: 3
      (xs,z) <- (do
        let pred0 = procedure @'[ 'Out, 'Out, 'In ] $
              \a' -> do
                (a,x) <- (do
                  (x:a) <- pure a'
                  pure (a,x)
                 )
                pure (x,a)
        (xs,z) <- runProcedure @'[ 'PredMode '[ 'Out, 'Out, 'In ], 'Out, 'Out, 'In ] foldl pred0 r
        pure (xs,z)
       )
      pure (xs,z)
    
{- closure/3
closure p x y :- ((p x y); (p x z, closure p z y)).
constraints:
~p[]
~(z[1,0] & z[1,1])
(z[1,0] | z[1,1])
(p[] <-> p[1])
(p[1] <-> p[1,1])
(p[1,1] <-> p[])
(x[] <-> x[0])
(x[] <-> x[1])
(x[0] <-> x[0,0])
(x[0,0] <-> p(1))
(x[1] <-> x[1,0])
(x[1,0] <-> p(1))
(y[] <-> y[0])
(y[] <-> y[1])
(y[0] <-> y[0,0])
(y[0,0] <-> p(2))
(y[1] <-> y[1,1])
(y[1,1] <-> y[])
(z[1,0] <-> p(2))
(z[1,1] <-> x[])
1
-}

closure = rget $ (procedure @'[ 'PredMode '[ 'In, 'Out ], 'In, 'Out ] closureP2IOIO) :& (procedure @'[ 'PredMode '[ 'Out, 'In ], 'Out, 'In ] closureP2OIOI) :& RNil
  where
    closureP2IOIO = \p x -> do
      -- solution: y[] y[0] y[0,0] y[1] y[1,1] z[1,0] p(2) ~p[] ~p[1] ~p[1,1] ~x[] ~x[0] ~x[0,0] ~x[1] ~x[1,0] ~z[1,1] ~p(1)
      -- cost: 6
      (y) <- (do
        (OneTuple (y)) <- runProcedure p x
        pure (y)
       ) <|> (do
        (OneTuple (z)) <- runProcedure p x
        (OneTuple (y)) <- closureP2IOIO p z
        pure (y)
       )
      pure (OneTuple (y))
    
    closureP2OIOI = \p y -> do
      -- solution: x[] x[0] x[0,0] x[1] x[1,0] z[1,1] p(1) ~p[] ~p[1] ~p[1,1] ~y[] ~y[0] ~y[0,0] ~y[1] ~y[1,1] ~z[1,0] ~p(2)
      -- cost: 6
      (x) <- (do
        (OneTuple (x)) <- runProcedure p y
        pure (x)
       ) <|> (do
        (OneTuple (z)) <- closureP2OIOI p y
        (OneTuple (x)) <- runProcedure p z
        pure (x)
       )
      pure (OneTuple (x))
    
{- smaller/2
smaller arg1 arg2 :- ((arg1 = 1, arg2 = 2); (arg1 = 2, arg2 = 3)).
constraints:
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg1[0] <-> arg1[0,0])
(arg1[1] <-> arg1[1,0])
(arg2[] <-> arg2[0])
(arg2[] <-> arg2[1])
(arg2[0] <-> arg2[0,1])
(arg2[1] <-> arg2[1,1])
1
-}

smaller = rget $ (procedure @'[ 'In, 'In ] smallerII) :& (procedure @'[ 'In, 'Out ] smallerIO) :& (procedure @'[ 'Out, 'In ] smallerOI) :& (procedure @'[ 'Out, 'Out ] smallerOO) :& RNil
  where
    smallerII = \arg1 arg2 -> Logic.once $ do
      -- solution: ~arg1[] ~arg1[0] ~arg1[0,0] ~arg1[1] ~arg1[1,0] ~arg2[] ~arg2[0] ~arg2[0,1] ~arg2[1] ~arg2[1,1]
      -- cost: 0
      () <- (do
        guard $ arg1 == 1
        guard $ arg2 == 2
        pure ()
       ) <|> (do
        guard $ arg1 == 2
        guard $ arg2 == 3
        pure ()
       )
      pure ()
    
    smallerIO = \arg1 -> do
      -- solution: arg2[] arg2[0] arg2[0,1] arg2[1] arg2[1,1] ~arg1[] ~arg1[0] ~arg1[0,0] ~arg1[1] ~arg1[1,0]
      -- cost: 0
      (arg2) <- (do
        guard $ arg1 == 1
        arg2 <- pure 2
        pure (arg2)
       ) <|> (do
        guard $ arg1 == 2
        arg2 <- pure 3
        pure (arg2)
       )
      pure (OneTuple (arg2))
    
    smallerOI = \arg2 -> do
      -- solution: arg1[] arg1[0] arg1[0,0] arg1[1] arg1[1,0] ~arg2[] ~arg2[0] ~arg2[0,1] ~arg2[1] ~arg2[1,1]
      -- cost: 0
      (arg1) <- (do
        arg1 <- pure 1
        guard $ arg2 == 2
        pure (arg1)
       ) <|> (do
        arg1 <- pure 2
        guard $ arg2 == 3
        pure (arg1)
       )
      pure (OneTuple (arg1))
    
    smallerOO = do
      -- solution: arg1[] arg1[0] arg1[0,0] arg1[1] arg1[1,0] arg2[] arg2[0] arg2[0,1] arg2[1] arg2[1,1]
      -- cost: 0
      (arg1,arg2) <- (do
        arg1 <- pure 1
        arg2 <- pure 2
        pure (arg1,arg2)
       ) <|> (do
        arg1 <- pure 2
        arg2 <- pure 3
        pure (arg1,arg2)
       )
      pure (arg1,arg2)
    
{- smallerTransitive/2
smallerTransitive x y :- ((closure pred0 x y, (pred0 curry1 curry2 :- (smaller curry1 curry2)))).
constraints:
~curry1[0]
~curry2[0]
~pred0[0,0]
((curry1[0,1,0,0] & curry2[0,1,0,0]) | ((curry1[0,1,0,0] & ~curry2[0,1,0,0]) | ((~curry1[0,1,0,0] & curry2[0,1,0,0]) | (~curry1[0,1,0,0] & ~curry2[0,1,0,0]))))
((~pred0[0,0] & (pred0(1) & (~pred0(2) & (x[0,0] & ~y[0,0])))) | (~pred0[0,0] & (~pred0(1) & (pred0(2) & (~x[0,0] & y[0,0])))))
(curry1[0,1,0] <-> curry1[0,1,0,0])
(curry2[0,1,0] <-> curry2[0,1,0,0])
(x[] <-> x[0])
(x[0] <-> x[0,0])
(y[] <-> y[0])
(y[0] <-> y[0,0])
(pred0(1) <-> curry1[0,1,0])
(pred0(2) <-> curry2[0,1,0])
1
-}

smallerTransitive = rget $ (procedure @'[ 'In, 'Out ] smallerTransitiveIO) :& (procedure @'[ 'Out, 'In ] smallerTransitiveOI) :& RNil
  where
    smallerTransitiveIO = \x -> do
      -- solution: curry2[0,1,0] curry2[0,1,0,0] y[] y[0] y[0,0] pred0(2) ~curry1[0] ~curry1[0,1,0] ~curry1[0,1,0,0] ~curry2[0] ~pred0[0,0] ~x[] ~x[0] ~x[0,0] ~pred0(1)
      -- cost: 4
      (y) <- (do
        let pred0 = procedure @'[ 'In, 'Out ] $
              \curry1 -> do
                (curry2) <- (do
                  (OneTuple (curry2)) <- runProcedure @'[ 'In, 'Out ] smaller curry1
                  pure (curry2)
                 )
                pure (OneTuple (curry2))
        (OneTuple (y)) <- runProcedure @'[ 'PredMode '[ 'In, 'Out ], 'In, 'Out ] closure pred0 x
        pure (y)
       )
      pure (OneTuple (y))
    
    smallerTransitiveOI = \y -> do
      -- solution: curry1[0,1,0] curry1[0,1,0,0] x[] x[0] x[0,0] pred0(1) ~curry1[0] ~curry2[0] ~curry2[0,1,0] ~curry2[0,1,0,0] ~pred0[0,0] ~y[] ~y[0] ~y[0,0] ~pred0(2)
      -- cost: 4
      (x) <- (do
        let pred0 = procedure @'[ 'Out, 'In ] $
              \curry2 -> do
                (curry1) <- (do
                  (OneTuple (curry1)) <- runProcedure @'[ 'Out, 'In ] smaller curry2
                  pure (curry1)
                 )
                pure (OneTuple (curry1))
        (OneTuple (x)) <- runProcedure @'[ 'PredMode '[ 'Out, 'In ], 'Out, 'In ] closure pred0 y
        pure (x)
       )
      pure (OneTuple (x))
    
{- compose/4
compose f g a z :- ((g a b, f b z)).
constraints:
~(b[0,0] & b[0,1])
(b[0,0] | b[0,1])
(a[] <-> a[0])
(a[0] <-> a[0,0])
(a[0,0] <-> g(1))
(b[0,0] <-> g(2))
(b[0,1] <-> f(1))
(z[] <-> z[0])
(z[0] <-> z[0,1])
(z[0,1] <-> f(2))
1
-}

compose = rget $ (procedure @'[ 'PredMode '[ 'In, 'In ], 'PredMode '[ 'In, 'Out ], 'In, 'In ] composeP2IIP2IOII) :& (procedure @'[ 'PredMode '[ 'In, 'In ], 'PredMode '[ 'Out, 'Out ], 'Out, 'In ] composeP2IIP2OOOI) :& (procedure @'[ 'PredMode '[ 'In, 'Out ], 'PredMode '[ 'In, 'Out ], 'In, 'Out ] composeP2IOP2IOIO) :& (procedure @'[ 'PredMode '[ 'In, 'Out ], 'PredMode '[ 'Out, 'Out ], 'Out, 'Out ] composeP2IOP2OOOO) :& (procedure @'[ 'PredMode '[ 'Out, 'In ], 'PredMode '[ 'In, 'In ], 'In, 'In ] composeP2OIP2IIII) :& (procedure @'[ 'PredMode '[ 'Out, 'In ], 'PredMode '[ 'Out, 'In ], 'Out, 'In ] composeP2OIP2OIOI) :& (procedure @'[ 'PredMode '[ 'Out, 'Out ], 'PredMode '[ 'In, 'In ], 'In, 'Out ] composeP2OOP2IIIO) :& (procedure @'[ 'PredMode '[ 'Out, 'Out ], 'PredMode '[ 'Out, 'In ], 'Out, 'Out ] composeP2OOP2OIOO) :& RNil
  where
    composeP2IIP2IOII = \f g a z -> Logic.once $ do
      -- solution: b[0,0] g(2) ~a[] ~a[0] ~a[0,0] ~b[0,1] ~z[] ~z[0] ~z[0,1] ~f(1) ~f(2) ~g(1)
      -- cost: 3
      () <- (do
        (OneTuple (b)) <- runProcedure g a
        () <- runProcedure f b z
        pure ()
       )
      pure ()
    
    composeP2IIP2OOOI = \f g z -> do
      -- solution: a[] a[0] a[0,0] b[0,0] g(1) g(2) ~b[0,1] ~z[] ~z[0] ~z[0,1] ~f(1) ~f(2)
      -- cost: 4
      (a) <- (do
        (a,b) <- runProcedure g 
        () <- runProcedure f b z
        pure (a)
       )
      pure (OneTuple (a))
    
    composeP2IOP2IOIO = \f g a -> do
      -- solution: b[0,0] z[] z[0] z[0,1] f(2) g(2) ~a[] ~a[0] ~a[0,0] ~b[0,1] ~f(1) ~g(1)
      -- cost: 4
      (z) <- (do
        (OneTuple (b)) <- runProcedure g a
        (OneTuple (z)) <- runProcedure f b
        pure (z)
       )
      pure (OneTuple (z))
    
    composeP2IOP2OOOO = \f g -> do
      -- solution: a[] a[0] a[0,0] b[0,0] z[] z[0] z[0,1] f(2) g(1) g(2) ~b[0,1] ~f(1)
      -- cost: 5
      (a,z) <- (do
        (a,b) <- runProcedure g 
        (OneTuple (z)) <- runProcedure f b
        pure (a,z)
       )
      pure (a,z)
    
    composeP2OIP2IIII = \f g a z -> Logic.once $ do
      -- solution: b[0,1] f(1) ~a[] ~a[0] ~a[0,0] ~b[0,0] ~z[] ~z[0] ~z[0,1] ~f(2) ~g(1) ~g(2)
      -- cost: 3
      () <- (do
        (OneTuple (b)) <- runProcedure f z
        () <- runProcedure g a b
        pure ()
       )
      pure ()
    
    composeP2OIP2OIOI = \f g z -> do
      -- solution: a[] a[0] a[0,0] b[0,1] f(1) g(1) ~b[0,0] ~z[] ~z[0] ~z[0,1] ~f(2) ~g(2)
      -- cost: 4
      (a) <- (do
        (OneTuple (b)) <- runProcedure f z
        (OneTuple (a)) <- runProcedure g b
        pure (a)
       )
      pure (OneTuple (a))
    
    composeP2OOP2IIIO = \f g a -> do
      -- solution: b[0,1] z[] z[0] z[0,1] f(1) f(2) ~a[] ~a[0] ~a[0,0] ~b[0,0] ~g(1) ~g(2)
      -- cost: 4
      (z) <- (do
        (b,z) <- runProcedure f 
        () <- runProcedure g a b
        pure (z)
       )
      pure (OneTuple (z))
    
    composeP2OOP2OIOO = \f g -> do
      -- solution: a[] a[0] a[0,0] b[0,1] z[] z[0] z[0,1] f(1) f(2) g(1) ~b[0,0] ~g(2)
      -- cost: 5
      (a,z) <- (do
        (b,z) <- runProcedure f 
        (OneTuple (a)) <- runProcedure g b
        pure (a,z)
       )
      pure (a,z)
    
{- composeTest/2
composeTest a z :- ((compose pred1 pred3 a z, (pred1 curry1 curry2 :- (times data0 curry1 curry2, data0 = 2)), (pred3 curry1 curry2 :- (plus data2 curry1 curry2, data2 = 1)))).
constraints:
~curry1[0]
~curry2[0]
~pred1[0,0]
~pred3[0,0]
~(data0[0,1,0,0] & data0[0,1,0,1])
~(data2[0,2,0,0] & data2[0,2,0,1])
(data0[0,1,0,0] | data0[0,1,0,1])
(data2[0,2,0,0] | data2[0,2,0,1])
((data0[0,1,0,0] & (~curry1[0,1,0,0] & ~curry2[0,1,0,0])) | ((~data0[0,1,0,0] & (curry1[0,1,0,0] & ~curry2[0,1,0,0])) | ((~data0[0,1,0,0] & (~curry1[0,1,0,0] & curry2[0,1,0,0])) | (~data0[0,1,0,0] & (~curry1[0,1,0,0] & ~curry2[0,1,0,0])))))
((data2[0,2,0,0] & (~curry1[0,2,0,0] & ~curry2[0,2,0,0])) | ((~data2[0,2,0,0] & (curry1[0,2,0,0] & ~curry2[0,2,0,0])) | ((~data2[0,2,0,0] & (~curry1[0,2,0,0] & curry2[0,2,0,0])) | (~data2[0,2,0,0] & (~curry1[0,2,0,0] & ~curry2[0,2,0,0])))))
((~pred1[0,0] & (pred1(1) & (pred1(2) & (~pred3[0,0] & (pred3(1) & (~pred3(2) & (a[0,0] & z[0,0]))))))) | ((~pred1[0,0] & (pred1(1) & (pred1(2) & (~pred3[0,0] & (~pred3(1) & (~pred3(2) & (~a[0,0] & z[0,0]))))))) | ((~pred1[0,0] & (pred1(1) & (~pred1(2) & (~pred3[0,0] & (pred3(1) & (~pred3(2) & (a[0,0] & ~z[0,0]))))))) | ((~pred1[0,0] & (pred1(1) & (~pred1(2) & (~pred3[0,0] & (~pred3(1) & (~pred3(2) & (~a[0,0] & ~z[0,0]))))))) | ((~pred1[0,0] & (~pred1(1) & (pred1(2) & (~pred3[0,0] & (pred3(1) & (pred3(2) & (a[0,0] & z[0,0]))))))) | ((~pred1[0,0] & (~pred1(1) & (pred1(2) & (~pred3[0,0] & (~pred3(1) & (pred3(2) & (~a[0,0] & z[0,0]))))))) | ((~pred1[0,0] & (~pred1(1) & (~pred1(2) & (~pred3[0,0] & (pred3(1) & (pred3(2) & (a[0,0] & ~z[0,0]))))))) | (~pred1[0,0] & (~pred1(1) & (~pred1(2) & (~pred3[0,0] & (~pred3(1) & (pred3(2) & (~a[0,0] & ~z[0,0]))))))))))))))
(a[] <-> a[0])
(a[0] <-> a[0,0])
(curry1[0,1,0] <-> curry1[0,1,0,0])
(curry1[0,2,0] <-> curry1[0,2,0,0])
(curry2[0,1,0] <-> curry2[0,1,0,0])
(curry2[0,2,0] <-> curry2[0,2,0,0])
(data0[0] <-> data0[0,1])
(data2[0] <-> data2[0,2])
(z[] <-> z[0])
(z[0] <-> z[0,0])
(pred1(1) <-> curry1[0,1,0])
(pred1(2) <-> curry2[0,1,0])
(pred3(1) <-> curry1[0,2,0])
(pred3(2) <-> curry2[0,2,0])
1
-}

composeTest = rget $ (procedure @'[ 'In, 'In ] composeTestII) :& (procedure @'[ 'In, 'Out ] composeTestIO) :& (procedure @'[ 'Out, 'In ] composeTestOI) :& RNil
  where
    composeTestII = \a z -> Logic.once $ do
      -- solution: curry1[0,1,0] curry1[0,1,0,0] data0[0] data0[0,1] data0[0,1,0,1] data2[0] data2[0,2] data2[0,2,0,1] pred1(1) ~a[] ~a[0] ~a[0,0] ~curry1[0] ~curry1[0,2,0] ~curry1[0,2,0,0] ~curry2[0] ~curry2[0,1,0] ~curry2[0,1,0,0] ~curry2[0,2,0] ~curry2[0,2,0,0] ~data0[0,1,0,0] ~data2[0,2,0,0] ~pred1[0,0] ~pred3[0,0] ~z[] ~z[0] ~z[0,0] ~pred1(2) ~pred3(1) ~pred3(2)
      -- cost: 4
      () <- (do
        let pred1 = procedure @'[ 'Out, 'In ] $
              \curry2 -> do
                (curry1) <- (do
                  data0 <- pure 2
                  (OneTuple (curry1)) <- runProcedure @'[ 'In, 'Out, 'In ] times data0 curry2
                  pure (curry1)
                 )
                pure (OneTuple (curry1))
        let pred3 = procedure @'[ 'In, 'In ] $
              \curry1 curry2 -> do
                () <- (do
                  data2 <- pure 1
                  () <- runProcedure @'[ 'In, 'In, 'In ] plus data2 curry1 curry2
                  pure ()
                 )
                pure ()
        () <- runProcedure @'[ 'PredMode '[ 'Out, 'In ], 'PredMode '[ 'In, 'In ], 'In, 'In ] compose pred1 pred3 a z
        pure ()
       )
      pure ()
    
    composeTestIO = \a -> do
      -- solution: curry2[0,1,0] curry2[0,1,0,0] curry2[0,2,0] curry2[0,2,0,0] data0[0] data0[0,1] data0[0,1,0,1] data2[0] data2[0,2] data2[0,2,0,1] z[] z[0] z[0,0] pred1(2) pred3(2) ~a[] ~a[0] ~a[0,0] ~curry1[0] ~curry1[0,1,0] ~curry1[0,1,0,0] ~curry1[0,2,0] ~curry1[0,2,0,0] ~curry2[0] ~data0[0,1,0,0] ~data2[0,2,0,0] ~pred1[0,0] ~pred3[0,0] ~pred1(1) ~pred3(1)
      -- cost: 6
      (z) <- (do
        let pred1 = procedure @'[ 'In, 'Out ] $
              \curry1 -> do
                (curry2) <- (do
                  data0 <- pure 2
                  (OneTuple (curry2)) <- runProcedure @'[ 'In, 'In, 'Out ] times data0 curry1
                  pure (curry2)
                 )
                pure (OneTuple (curry2))
        let pred3 = procedure @'[ 'In, 'Out ] $
              \curry1 -> do
                (curry2) <- (do
                  data2 <- pure 1
                  (OneTuple (curry2)) <- runProcedure @'[ 'In, 'In, 'Out ] plus data2 curry1
                  pure (curry2)
                 )
                pure (OneTuple (curry2))
        (OneTuple (z)) <- runProcedure @'[ 'PredMode '[ 'In, 'Out ], 'PredMode '[ 'In, 'Out ], 'In, 'Out ] compose pred1 pred3 a
        pure (z)
       )
      pure (OneTuple (z))
    
    composeTestOI = \z -> do
      -- solution: a[] a[0] a[0,0] curry1[0,1,0] curry1[0,1,0,0] curry1[0,2,0] curry1[0,2,0,0] data0[0] data0[0,1] data0[0,1,0,1] data2[0] data2[0,2] data2[0,2,0,1] pred1(1) pred3(1) ~curry1[0] ~curry2[0] ~curry2[0,1,0] ~curry2[0,1,0,0] ~curry2[0,2,0] ~curry2[0,2,0,0] ~data0[0,1,0,0] ~data2[0,2,0,0] ~pred1[0,0] ~pred3[0,0] ~z[] ~z[0] ~z[0,0] ~pred1(2) ~pred3(2)
      -- cost: 6
      (a) <- (do
        let pred1 = procedure @'[ 'Out, 'In ] $
              \curry2 -> do
                (curry1) <- (do
                  data0 <- pure 2
                  (OneTuple (curry1)) <- runProcedure @'[ 'In, 'Out, 'In ] times data0 curry2
                  pure (curry1)
                 )
                pure (OneTuple (curry1))
        let pred3 = procedure @'[ 'Out, 'In ] $
              \curry2 -> do
                (curry1) <- (do
                  data2 <- pure 1
                  (OneTuple (curry1)) <- runProcedure @'[ 'In, 'Out, 'In ] plus data2 curry2
                  pure (curry1)
                 )
                pure (OneTuple (curry1))
        (OneTuple (a)) <- runProcedure @'[ 'PredMode '[ 'Out, 'In ], 'PredMode '[ 'Out, 'In ], 'Out, 'In ] compose pred1 pred3 z
        pure (a)
       )
      pure (OneTuple (a))
    