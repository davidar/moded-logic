{-# LANGUAGE DataKinds, FlexibleContexts, NoImplicitPrelude, NoMonomorphismRestriction, TypeApplications #-}
module HigherOrder where

import qualified Control.Monad.Logic as Logic
import Control.Monad.Logic.Moded.Prelude

{- even/1
even n :- ((mod n data0 data1, data0 = 2, data1 = 0)).
constraints:
~mod[0]
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
      -- solution: data0[0,1] data1[0,2]
      -- cost: 1
      () <- (do
        data0 <- pure 2
        data1 <- pure 0
        () <- runProcedure @'[ 'In, 'In, 'In ] mod n data0 data1
        pure ()
       )
      pure ()
    
{- map/3
map arg1 arg2 arg3 :- ((arg2 = [], arg3 = []); (arg2 = x:xs, arg3 = y:ys, p x y, map p xs ys, arg1 = p)).
constraints:
~arg1[]
~map[1]
~(arg1[1,4] & p[1,4])
~(arg2[1,0] & x[1,0])
~(arg3[1,1] & y[1,1])
~(p[1,3] & p[1,4])
~(x[1,0] & x[1,2])
~(xs[1,0] & xs[1,3])
~(y[1,1] & y[1,2])
~(ys[1,1] & ys[1,3])
(p[1,3] | p[1,4])
(x[1,0] | x[1,2])
(xs[1,0] | xs[1,3])
(y[1,1] | y[1,2])
(ys[1,1] | ys[1,3])
(arg1[] <-> arg1[1])
(arg1[1] <-> arg1[1,4])
(arg2[] <-> arg2[0])
(arg2[] <-> arg2[1])
(arg2[0] <-> arg2[0,0])
(arg2[1] <-> arg2[1,0])
(arg3[] <-> arg3[0])
(arg3[] <-> arg3[1])
(arg3[0] <-> arg3[0,1])
(arg3[1] <-> arg3[1,1])
(p[1,3] <-> arg1[])
(x[1,0] <-> xs[1,0])
(x[1,2] <-> arg1(1))
(x[1,2] <-> p(1))
(xs[1,3] <-> arg2[])
(y[1,1] <-> ys[1,1])
(y[1,2] <-> arg1(2))
(y[1,2] <-> p(2))
(ys[1,3] <-> arg3[])
1
-}

map = rget $ (procedure @'[ 'PredMode '[ 'In, 'In ], 'In, 'In ] mapP2IIII) :& (procedure @'[ 'PredMode '[ 'In, 'Out ], 'In, 'Out ] mapP2IOIO) :& (procedure @'[ 'PredMode '[ 'Out, 'In ], 'Out, 'In ] mapP2OIOI) :& (procedure @'[ 'PredMode '[ 'Out, 'Out ], 'Out, 'Out ] mapP2OOOO) :& RNil
  where
    mapP2IIII = \arg1 arg2 arg3 -> Logic.once $ do
      -- solution: p[1,4] x[1,0] xs[1,0] y[1,1] ys[1,1]
      -- cost: 2
      () <- (do
        guard $ arg2 == []
        guard $ arg3 == []
        pure ()
       ) <|> (do
        p <- pure arg1
        (x:xs) <- pure arg2
        (y:ys) <- pure arg3
        () <- mapP2IIII p xs ys
        () <- runProcedure @'[ 'In, 'In ] p x y
        pure ()
       )
      pure ()
    
    mapP2IOIO = \arg1 arg2 -> do
      -- solution: arg3[] arg3[0] arg3[0,1] arg3[1] arg3[1,1] p[1,4] x[1,0] xs[1,0] y[1,2] ys[1,3]
      -- cost: 4
      (arg3) <- (do
        guard $ arg2 == []
        arg3 <- pure []
        pure (arg3)
       ) <|> (do
        p <- pure arg1
        (x:xs) <- pure arg2
        (OneTuple (ys)) <- mapP2IOIO p xs
        (OneTuple (y)) <- runProcedure @'[ 'In, 'Out ] p x
        arg3 <- pure (y:ys)
        pure (arg3)
       )
      pure (OneTuple (arg3))
    
    mapP2OIOI = \arg1 arg3 -> do
      -- solution: arg2[] arg2[0] arg2[0,0] arg2[1] arg2[1,0] p[1,4] x[1,2] xs[1,3] y[1,1] ys[1,1]
      -- cost: 4
      (arg2) <- (do
        arg2 <- pure []
        guard $ arg3 == []
        pure (arg2)
       ) <|> (do
        p <- pure arg1
        (y:ys) <- pure arg3
        (OneTuple (xs)) <- mapP2OIOI p ys
        (OneTuple (x)) <- runProcedure @'[ 'Out, 'In ] p y
        arg2 <- pure (x:xs)
        pure (arg2)
       )
      pure (OneTuple (arg2))
    
    mapP2OOOO = \arg1 -> do
      -- solution: arg2[] arg2[0] arg2[0,0] arg2[1] arg2[1,0] arg3[] arg3[0] arg3[0,1] arg3[1] arg3[1,1] p[1,4] x[1,2] xs[1,3] y[1,2] ys[1,3]
      -- cost: 6
      (arg2,arg3) <- (do
        arg2 <- pure []
        arg3 <- pure []
        pure (arg2,arg3)
       ) <|> (do
        p <- pure arg1
        (xs,ys) <- mapP2OOOO p
        (x,y) <- runProcedure @'[ 'Out, 'Out ] p 
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
~map[0]
~pred0[0,0]
~succ[0,1,0]
((curry1[0,1,0,0] & ~curry2[0,1,0,0]) | ((~curry1[0,1,0,0] & curry2[0,1,0,0]) | (~curry1[0,1,0,0] & ~curry2[0,1,0,0])))
((~pred0[0,0] & (pred0(1) & (pred0(2) & (xs[0,0] & ys[0,0])))) | ((~pred0[0,0] & (pred0(1) & (~pred0(2) & (xs[0,0] & ~ys[0,0])))) | ((~pred0[0,0] & (~pred0(1) & (pred0(2) & (~xs[0,0] & ys[0,0])))) | (~pred0[0,0] & (~pred0(1) & (~pred0(2) & (~xs[0,0] & ~ys[0,0])))))))
(curry1[0,1,0] <-> curry1[0,1,0,0])
(curry2[0,1,0] <-> curry2[0,1,0,0])
(succ[0] <-> succ[0,1])
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
      -- solution: 
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
      -- solution: curry2[0,1,0] curry2[0,1,0,0] ys[] ys[0] ys[0,0]
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
      -- solution: curry1[0,1,0] curry1[0,1,0,0] xs[] xs[0] xs[0,0]
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
filter arg1 arg2 arg3 :- ((arg2 = [], arg3 = []); (arg2 = h:t, if (p h) then (filter p t t', ts = h0:t', h0 = h) else (filter p t ts), arg1 = p, arg3 = ts)).
constraints:
~arg1[]
~filter[1,1,1]
~filter[1,1,2]
~h[1,1]
~h[1,1,0,0]
~h[1,1,1,2]
~p[1,1,1,0]
~p[1,1,2]
~(arg1[1,2] & p[1,2])
~(arg2[1,0] & h[1,0])
~(arg3[1,3] & ts[1,3])
~(h[1,0] & h[1,1])
~(h0[1,1,1,1] & h0[1,1,1,2])
~(h0[1,1,1,2] & h[1,1,1,2])
~(p[1,1] & p[1,2])
~(t[1,0] & t[1,1])
~(t'[1,1,1,0] & t'[1,1,1,1])
~(ts[1,1] & ts[1,3])
~(ts[1,1,1,1] & h0[1,1,1,1])
(h[1,0] | h[1,1])
(h0[1,1,1,1] | h0[1,1,1,2])
(p[1,1] | p[1,2])
(t[1,0] | t[1,1])
(t'[1,1,1,0] | t'[1,1,1,1])
(ts[1,1] | ts[1,3])
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
(filter[1] <-> filter[1,1])
(filter[1,1] <-> (filter[1,1,1] | filter[1,1,2]))
(h[1,0] <-> t[1,0])
(h[1,1,0,0] <-> arg1(1))
(h[1,1,0,0] <-> p(1))
(h0[1,1,1,1] <-> t'[1,1,1,1])
(p[1,1] <-> p[1,1,2])
(p[1,1,1,0] <-> arg1[])
(p[1,1,2] <-> p[1,1,2,0])
(p[1,1,2,0] <-> arg1[])
(t[1,1] <-> (t[1,1,1] | t[1,1,2]))
(t[1,1,1] <-> t[1,1,1,0])
(t[1,1,1] <-> t[1,1,2])
(t[1,1,1,0] <-> arg2[])
(t[1,1,2] <-> t[1,1,2,0])
(t[1,1,2,0] <-> arg2[])
(t'[1,1,1,0] <-> arg3[])
(ts[1,1] <-> (ts[1,1,1] | ts[1,1,2]))
(ts[1,1,1] <-> ts[1,1,1,1])
(ts[1,1,1] <-> ts[1,1,2])
(ts[1,1,2] <-> ts[1,1,2,0])
(ts[1,1,2,0] <-> arg3[])
1
-}

filter = rget $ (procedure @'[ 'PredMode '[ 'In ], 'In, 'In ] filterP1III) :& (procedure @'[ 'PredMode '[ 'In ], 'In, 'Out ] filterP1IIO) :& RNil
  where
    filterP1III = \arg1 arg2 arg3 -> Logic.once $ do
      -- solution: h[1,0] h0[1,1,1,1] p[1,2] t[1,0] t'[1,1,1,1] ts[1,3]
      -- cost: 3
      () <- (do
        guard $ arg2 == []
        guard $ arg3 == []
        pure ()
       ) <|> (do
        p <- pure arg1
        (h:t) <- pure arg2
        ts <- pure arg3
        () <- Logic.ifte ((do
          () <- runProcedure @'[ 'In ] p h
          pure ()
         )) (\() -> (do
          (h0:t') <- pure ts
          guard $ h0 == h
          () <- filterP1III p t t'
          pure ()
         )) ((do
          () <- filterP1III p t ts
          pure ()
         ))
        pure ()
       )
      pure ()
    
    filterP1IIO = \arg1 arg2 -> do
      -- solution: arg3[] arg3[0] arg3[0,1] arg3[1] arg3[1,3] h[1,0] h0[1,1,1,2] p[1,2] t[1,0] t'[1,1,1,0] ts[1,1] ts[1,1,1] ts[1,1,1,1] ts[1,1,2] ts[1,1,2,0]
      -- cost: 5
      (arg3) <- (do
        guard $ arg2 == []
        arg3 <- pure []
        pure (arg3)
       ) <|> (do
        p <- pure arg1
        (h:t) <- pure arg2
        (ts) <- Logic.ifte ((do
          () <- runProcedure @'[ 'In ] p h
          pure ()
         )) (\() -> (do
          h0 <- pure h
          (OneTuple (t')) <- filterP1IIO p t
          ts <- pure (h0:t')
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
~even[0,1,0]
~filter[0]
~pred0[0,0]
((~pred0[0,0] & (~pred0(1) & (~xs[0,0] & ys[0,0]))) | (~pred0[0,0] & (~pred0(1) & (~xs[0,0] & ~ys[0,0]))))
(curry1[0,1,0] <-> curry1[0,1,0,0])
(even[0] <-> even[0,1])
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
      -- solution: 
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
      -- solution: ys[] ys[0] ys[0,0]
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
foldl arg1 arg2 arg3 arg4 :- ((arg2 = [], arg3 = a, arg4 = a); (arg2 = h:t, p h a a', foldl p t a' a'', arg1 = p, arg3 = a, arg4 = a'')).
constraints:
~arg1[]
~foldl[1]
~(a[0,1] & a[0,2])
~(a[1,1] & a[1,4])
~(a'[1,1] & a'[1,2])
~(a''[1,2] & a''[1,5])
~(arg1[1,3] & p[1,3])
~(arg2[1,0] & h[1,0])
~(arg3[0,1] & a[0,1])
~(arg3[1,4] & a[1,4])
~(arg4[0,2] & a[0,2])
~(arg4[1,5] & a''[1,5])
~(h[1,0] & h[1,1])
~(p[1,2] & p[1,3])
~(t[1,0] & t[1,2])
(a[0,1] | a[0,2])
(a[1,1] | a[1,4])
(a'[1,1] | a'[1,2])
(a''[1,2] | a''[1,5])
(h[1,0] | h[1,1])
(p[1,2] | p[1,3])
(t[1,0] | t[1,2])
(a[1,1] <-> arg1(2))
(a[1,1] <-> p(2))
(a'[1,1] <-> arg1(3))
(a'[1,1] <-> p(3))
(a'[1,2] <-> arg3[])
(a''[1,2] <-> arg4[])
(arg1[] <-> arg1[1])
(arg1[1] <-> arg1[1,3])
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
(h[1,0] <-> t[1,0])
(h[1,1] <-> arg1(1))
(h[1,1] <-> p(1))
(p[1,2] <-> arg1[])
(t[1,2] <-> arg2[])
1
-}

foldl = rget $ (procedure @'[ 'PredMode '[ 'In, 'In, 'Out ], 'In, 'In, 'In ] foldlP3IIOIII) :& (procedure @'[ 'PredMode '[ 'In, 'In, 'Out ], 'In, 'In, 'Out ] foldlP3IIOIIO) :& (procedure @'[ 'PredMode '[ 'In, 'Out, 'In ], 'In, 'Out, 'In ] foldlP3IOIIOI) :& (procedure @'[ 'PredMode '[ 'In, 'Out, 'Out ], 'In, 'In, 'In ] foldlP3IOOIII) :& (procedure @'[ 'PredMode '[ 'In, 'Out, 'Out ], 'In, 'In, 'Out ] foldlP3IOOIIO) :& (procedure @'[ 'PredMode '[ 'Out, 'In, 'Out ], 'Out, 'In, 'In ] foldlP3OIOOII) :& (procedure @'[ 'PredMode '[ 'Out, 'In, 'Out ], 'Out, 'In, 'Out ] foldlP3OIOOIO) :& (procedure @'[ 'PredMode '[ 'Out, 'Out, 'In ], 'Out, 'Out, 'In ] foldlP3OOIOOI) :& (procedure @'[ 'PredMode '[ 'Out, 'Out, 'Out ], 'Out, 'In, 'In ] foldlP3OOOOII) :& (procedure @'[ 'PredMode '[ 'Out, 'Out, 'Out ], 'Out, 'In, 'Out ] foldlP3OOOOIO) :& RNil
  where
    foldlP3IIOIII = \arg1 arg2 arg3 arg4 -> Logic.once $ do
      -- solution: a[0,1] a[1,4] a'[1,1] a''[1,5] h[1,0] p[1,3] t[1,0]
      -- cost: 3
      () <- (do
        guard $ arg2 == []
        a <- pure arg3
        guard $ arg4 == a
        pure ()
       ) <|> (do
        p <- pure arg1
        (h:t) <- pure arg2
        a <- pure arg3
        a'' <- pure arg4
        (OneTuple (a')) <- runProcedure @'[ 'In, 'In, 'Out ] p h a
        () <- foldlP3IIOIII p t a' a''
        pure ()
       )
      pure ()
    
    foldlP3IIOIIO = \arg1 arg2 arg3 -> do
      -- solution: a[0,1] a[1,4] a'[1,1] a''[1,2] arg4[] arg4[0] arg4[0,2] arg4[1] arg4[1,5] h[1,0] p[1,3] t[1,0]
      -- cost: 4
      (arg4) <- (do
        guard $ arg2 == []
        a <- pure arg3
        arg4 <- pure a
        pure (arg4)
       ) <|> (do
        p <- pure arg1
        (h:t) <- pure arg2
        a <- pure arg3
        (OneTuple (a')) <- runProcedure @'[ 'In, 'In, 'Out ] p h a
        (OneTuple (a'')) <- foldlP3IIOIIO p t a'
        arg4 <- pure a''
        pure (arg4)
       )
      pure (OneTuple (arg4))
    
    foldlP3IOIIOI = \arg1 arg2 arg4 -> do
      -- solution: a[0,2] a[1,1] a'[1,2] a''[1,5] arg3[] arg3[0] arg3[0,1] arg3[1] arg3[1,4] h[1,0] p[1,3] t[1,0]
      -- cost: 4
      (arg3) <- (do
        guard $ arg2 == []
        a <- pure arg4
        arg3 <- pure a
        pure (arg3)
       ) <|> (do
        p <- pure arg1
        (h:t) <- pure arg2
        a'' <- pure arg4
        (OneTuple (a')) <- foldlP3IOIIOI p t a''
        (OneTuple (a)) <- runProcedure @'[ 'In, 'Out, 'In ] p h a'
        arg3 <- pure a
        pure (arg3)
       )
      pure (OneTuple (arg3))
    
    foldlP3IOOIII = \arg1 arg2 arg3 arg4 -> Logic.once $ do
      -- solution: a[0,1] a[1,1] a'[1,1] a''[1,5] h[1,0] p[1,3] t[1,0]
      -- cost: 4
      () <- (do
        guard $ arg2 == []
        a <- pure arg3
        guard $ arg4 == a
        pure ()
       ) <|> (do
        p <- pure arg1
        (h:t) <- pure arg2
        a'' <- pure arg4
        (a,a') <- runProcedure @'[ 'In, 'Out, 'Out ] p h
        guard $ arg3 == a
        () <- foldlP3IOOIII p t a' a''
        pure ()
       )
      pure ()
    
    foldlP3IOOIIO = \arg1 arg2 arg3 -> do
      -- solution: a[0,1] a[1,1] a'[1,1] a''[1,2] arg4[] arg4[0] arg4[0,2] arg4[1] arg4[1,5] h[1,0] p[1,3] t[1,0]
      -- cost: 5
      (arg4) <- (do
        guard $ arg2 == []
        a <- pure arg3
        arg4 <- pure a
        pure (arg4)
       ) <|> (do
        p <- pure arg1
        (h:t) <- pure arg2
        (a,a') <- runProcedure @'[ 'In, 'Out, 'Out ] p h
        guard $ arg3 == a
        (OneTuple (a'')) <- foldlP3IOOIIO p t a'
        arg4 <- pure a''
        pure (arg4)
       )
      pure (OneTuple (arg4))
    
    foldlP3OIOOII = \arg1 arg3 arg4 -> do
      -- solution: a[0,1] a[1,4] a'[1,1] a''[1,5] arg2[] arg2[0] arg2[0,0] arg2[1] arg2[1,0] h[1,1] p[1,3] t[1,2]
      -- cost: 5
      (arg2) <- (do
        arg2 <- pure []
        a <- pure arg3
        guard $ arg4 == a
        pure (arg2)
       ) <|> (do
        p <- pure arg1
        a <- pure arg3
        a'' <- pure arg4
        (h,a') <- runProcedure @'[ 'Out, 'In, 'Out ] p a
        (OneTuple (t)) <- foldlP3OIOOII p a' a''
        arg2 <- pure (h:t)
        pure (arg2)
       )
      pure (OneTuple (arg2))
    
    foldlP3OIOOIO = \arg1 arg3 -> do
      -- solution: a[0,1] a[1,4] a'[1,1] a''[1,2] arg2[] arg2[0] arg2[0,0] arg2[1] arg2[1,0] arg4[] arg4[0] arg4[0,2] arg4[1] arg4[1,5] h[1,1] p[1,3] t[1,2]
      -- cost: 6
      (arg2,arg4) <- (do
        arg2 <- pure []
        a <- pure arg3
        arg4 <- pure a
        pure (arg2,arg4)
       ) <|> (do
        p <- pure arg1
        a <- pure arg3
        (h,a') <- runProcedure @'[ 'Out, 'In, 'Out ] p a
        (t,a'') <- foldlP3OIOOIO p a'
        arg2 <- pure (h:t)
        arg4 <- pure a''
        pure (arg2,arg4)
       )
      pure (arg2,arg4)
    
    foldlP3OOIOOI = \arg1 arg4 -> do
      -- solution: a[0,2] a[1,1] a'[1,2] a''[1,5] arg2[] arg2[0] arg2[0,0] arg2[1] arg2[1,0] arg3[] arg3[0] arg3[0,1] arg3[1] arg3[1,4] h[1,1] p[1,3] t[1,2]
      -- cost: 6
      (arg2,arg3) <- (do
        arg2 <- pure []
        a <- pure arg4
        arg3 <- pure a
        pure (arg2,arg3)
       ) <|> (do
        p <- pure arg1
        a'' <- pure arg4
        (t,a') <- foldlP3OOIOOI p a''
        (h,a) <- runProcedure @'[ 'Out, 'Out, 'In ] p a'
        arg2 <- pure (h:t)
        arg3 <- pure a
        pure (arg2,arg3)
       )
      pure (arg2,arg3)
    
    foldlP3OOOOII = \arg1 arg3 arg4 -> do
      -- solution: a[0,1] a[1,1] a'[1,1] a''[1,5] arg2[] arg2[0] arg2[0,0] arg2[1] arg2[1,0] h[1,1] p[1,3] t[1,2]
      -- cost: 6
      (arg2) <- (do
        arg2 <- pure []
        a <- pure arg3
        guard $ arg4 == a
        pure (arg2)
       ) <|> (do
        p <- pure arg1
        a'' <- pure arg4
        (h,a,a') <- runProcedure @'[ 'Out, 'Out, 'Out ] p 
        guard $ arg3 == a
        (OneTuple (t)) <- foldlP3OOOOII p a' a''
        arg2 <- pure (h:t)
        pure (arg2)
       )
      pure (OneTuple (arg2))
    
    foldlP3OOOOIO = \arg1 arg3 -> do
      -- solution: a[0,1] a[1,1] a'[1,1] a''[1,2] arg2[] arg2[0] arg2[0,0] arg2[1] arg2[1,0] arg4[] arg4[0] arg4[0,2] arg4[1] arg4[1,5] h[1,1] p[1,3] t[1,2]
      -- cost: 7
      (arg2,arg4) <- (do
        arg2 <- pure []
        a <- pure arg3
        arg4 <- pure a
        pure (arg2,arg4)
       ) <|> (do
        p <- pure arg1
        (h,a,a') <- runProcedure @'[ 'Out, 'Out, 'Out ] p 
        guard $ arg3 == a
        (t,a'') <- foldlP3OOOOIO p a'
        arg2 <- pure (h:t)
        arg4 <- pure a''
        pure (arg2,arg4)
       )
      pure (arg2,arg4)
    
{- sum/3
sum xs z r :- ((foldl pred0 xs z r, (pred0 curry1 curry2 curry3 :- (plus curry1 curry2 curry3)))).
constraints:
~curry1[0]
~curry2[0]
~curry3[0]
~foldl[0]
~plus[0,1,0]
~pred0[0,0]
((curry1[0,1,0,0] & (~curry2[0,1,0,0] & ~curry3[0,1,0,0])) | ((~curry1[0,1,0,0] & (curry2[0,1,0,0] & ~curry3[0,1,0,0])) | ((~curry1[0,1,0,0] & (~curry2[0,1,0,0] & curry3[0,1,0,0])) | (~curry1[0,1,0,0] & (~curry2[0,1,0,0] & ~curry3[0,1,0,0])))))
((~pred0[0,0] & (pred0(1) & (pred0(2) & (pred0(3) & (xs[0,0] & (~z[0,0] & r[0,0])))))) | ((~pred0[0,0] & (pred0(1) & (pred0(2) & (pred0(3) & (xs[0,0] & (~z[0,0] & ~r[0,0])))))) | ((~pred0[0,0] & (pred0(1) & (pred0(2) & (~pred0(3) & (xs[0,0] & (z[0,0] & ~r[0,0])))))) | ((~pred0[0,0] & (pred0(1) & (~pred0(2) & (pred0(3) & (xs[0,0] & (~z[0,0] & r[0,0])))))) | ((~pred0[0,0] & (pred0(1) & (~pred0(2) & (pred0(3) & (xs[0,0] & (~z[0,0] & ~r[0,0])))))) | ((~pred0[0,0] & (~pred0(1) & (pred0(2) & (pred0(3) & (~xs[0,0] & (~z[0,0] & r[0,0])))))) | ((~pred0[0,0] & (~pred0(1) & (pred0(2) & (pred0(3) & (~xs[0,0] & (~z[0,0] & ~r[0,0])))))) | ((~pred0[0,0] & (~pred0(1) & (pred0(2) & (~pred0(3) & (~xs[0,0] & (z[0,0] & ~r[0,0])))))) | ((~pred0[0,0] & (~pred0(1) & (~pred0(2) & (pred0(3) & (~xs[0,0] & (~z[0,0] & r[0,0])))))) | (~pred0[0,0] & (~pred0(1) & (~pred0(2) & (pred0(3) & (~xs[0,0] & (~z[0,0] & ~r[0,0])))))))))))))))
(curry1[0,1,0] <-> curry1[0,1,0,0])
(curry2[0,1,0] <-> curry2[0,1,0,0])
(curry3[0,1,0] <-> curry3[0,1,0,0])
(plus[0] <-> plus[0,1])
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
      -- solution: curry3[0,1,0] curry3[0,1,0,0]
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
      -- solution: curry3[0,1,0] curry3[0,1,0,0] r[] r[0] r[0,0]
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
      -- solution: curry2[0,1,0] curry2[0,1,0,0] z[] z[0] z[0,0]
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
~foldl[0]
~pred0[0,0]
~x[0]
~(a[0,1,0,0] & x[0,1,0,0])
((~pred0[0,0] & (pred0(1) & (pred0(2) & (pred0(3) & (xs[0,0] & (~z[0,0] & r[0,0])))))) | ((~pred0[0,0] & (pred0(1) & (pred0(2) & (pred0(3) & (xs[0,0] & (~z[0,0] & ~r[0,0])))))) | ((~pred0[0,0] & (pred0(1) & (pred0(2) & (~pred0(3) & (xs[0,0] & (z[0,0] & ~r[0,0])))))) | ((~pred0[0,0] & (pred0(1) & (~pred0(2) & (pred0(3) & (xs[0,0] & (~z[0,0] & r[0,0])))))) | ((~pred0[0,0] & (pred0(1) & (~pred0(2) & (pred0(3) & (xs[0,0] & (~z[0,0] & ~r[0,0])))))) | ((~pred0[0,0] & (~pred0(1) & (pred0(2) & (pred0(3) & (~xs[0,0] & (~z[0,0] & r[0,0])))))) | ((~pred0[0,0] & (~pred0(1) & (pred0(2) & (pred0(3) & (~xs[0,0] & (~z[0,0] & ~r[0,0])))))) | ((~pred0[0,0] & (~pred0(1) & (pred0(2) & (~pred0(3) & (~xs[0,0] & (z[0,0] & ~r[0,0])))))) | ((~pred0[0,0] & (~pred0(1) & (~pred0(2) & (pred0(3) & (~xs[0,0] & (~z[0,0] & r[0,0])))))) | (~pred0[0,0] & (~pred0(1) & (~pred0(2) & (pred0(3) & (~xs[0,0] & (~z[0,0] & ~r[0,0])))))))))))))))
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
      -- solution: a[0,1,0] a[0,1,0,0] z[] z[0] z[0,0]
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
      -- solution: a'[0,1,0] a'[0,1,0,0] x[0,1,0] x[0,1,0,0] xs[] xs[0] xs[0,0]
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
      -- solution: a'[0,1,0] a'[0,1,0,0] r[] r[0] r[0,0] x[0,1,0] x[0,1,0,0] xs[] xs[0] xs[0,0]
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
~foldl[0]
~pred0[0,0]
~x[0]
~(a'[0,1,0,0] & x[0,1,0,0])
((~pred0[0,0] & (pred0(1) & (pred0(2) & (pred0(3) & (xs[0,0] & (~z[0,0] & r[0,0])))))) | ((~pred0[0,0] & (pred0(1) & (pred0(2) & (pred0(3) & (xs[0,0] & (~z[0,0] & ~r[0,0])))))) | ((~pred0[0,0] & (pred0(1) & (pred0(2) & (~pred0(3) & (xs[0,0] & (z[0,0] & ~r[0,0])))))) | ((~pred0[0,0] & (pred0(1) & (~pred0(2) & (pred0(3) & (xs[0,0] & (~z[0,0] & r[0,0])))))) | ((~pred0[0,0] & (pred0(1) & (~pred0(2) & (pred0(3) & (xs[0,0] & (~z[0,0] & ~r[0,0])))))) | ((~pred0[0,0] & (~pred0(1) & (pred0(2) & (pred0(3) & (~xs[0,0] & (~z[0,0] & r[0,0])))))) | ((~pred0[0,0] & (~pred0(1) & (pred0(2) & (pred0(3) & (~xs[0,0] & (~z[0,0] & ~r[0,0])))))) | ((~pred0[0,0] & (~pred0(1) & (pred0(2) & (~pred0(3) & (~xs[0,0] & (z[0,0] & ~r[0,0])))))) | ((~pred0[0,0] & (~pred0(1) & (~pred0(2) & (pred0(3) & (~xs[0,0] & (~z[0,0] & r[0,0])))))) | (~pred0[0,0] & (~pred0(1) & (~pred0(2) & (pred0(3) & (~xs[0,0] & (~z[0,0] & ~r[0,0])))))))))))))))
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
      -- solution: a'[0,1,0] a'[0,1,0,0]
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
      -- solution: a'[0,1,0] a'[0,1,0,0] r[] r[0] r[0,0]
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
      -- solution: a[0,1,0] a[0,1,0,0] x[0,1,0] x[0,1,0,0] xs[] xs[0] xs[0,0] z[] z[0] z[0,0]
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
closure arg1 arg2 arg3 :- ((p x y, arg1 = p, arg2 = x, arg3 = y); (p x z, closure p z y, arg1 = p, arg2 = x, arg3 = y)).
constraints:
p[0,1]
~closure[1]
~(arg1[0,1] & p[0,1])
~(arg1[1,2] & p[1,2])
~(arg2[0,2] & x[0,2])
~(arg2[1,3] & x[1,3])
~(arg3[0,3] & y[0,3])
~(arg3[1,4] & y[1,4])
~(p[1,1] & p[1,2])
~(x[0,0] & x[0,2])
~(x[1,0] & x[1,3])
~(y[0,0] & y[0,3])
~(y[1,1] & y[1,4])
~(z[1,0] & z[1,1])
(p[1,1] | p[1,2])
(x[0,0] | x[0,2])
(x[1,0] | x[1,3])
(y[0,0] | y[0,3])
(y[1,1] | y[1,4])
(z[1,0] | z[1,1])
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg1[0] <-> arg1[0,1])
(arg1[1] <-> arg1[1,2])
(arg2[] <-> arg2[0])
(arg2[] <-> arg2[1])
(arg2[0] <-> arg2[0,2])
(arg2[1] <-> arg2[1,3])
(arg3[] <-> arg3[0])
(arg3[] <-> arg3[1])
(arg3[0] <-> arg3[0,3])
(arg3[1] <-> arg3[1,4])
(p[1,1] <-> arg1[])
(x[0,0] <-> arg1(1))
(x[0,0] <-> p(1))
(x[1,0] <-> arg1(1))
(x[1,0] <-> p(1))
(y[0,0] <-> arg1(2))
(y[0,0] <-> p(2))
(y[1,1] <-> arg3[])
(z[1,0] <-> arg1(2))
(z[1,0] <-> p(2))
(z[1,1] <-> arg2[])
1
-}

closure = rget $ (procedure @'[ 'PredMode '[ 'In, 'Out ], 'In, 'In ] closureP2IOII) :& (procedure @'[ 'PredMode '[ 'In, 'Out ], 'In, 'Out ] closureP2IOIO) :& (procedure @'[ 'PredMode '[ 'Out, 'In ], 'Out, 'In ] closureP2OIOI) :& (procedure @'[ 'PredMode '[ 'Out, 'Out ], 'In, 'In ] closureP2OOII) :& (procedure @'[ 'PredMode '[ 'Out, 'Out ], 'In, 'Out ] closureP2OOIO) :& RNil
  where
    closureP2IOII = \arg1 arg2 arg3 -> Logic.once $ do
      -- solution: p[0,1] p[1,2] x[0,2] x[1,3] y[0,0] y[1,4] z[1,0]
      -- cost: 5
      () <- (do
        p <- pure arg1
        x <- pure arg2
        (OneTuple (y)) <- runProcedure @'[ 'In, 'Out ] p x
        guard $ arg3 == y
        pure ()
       ) <|> (do
        p <- pure arg1
        x <- pure arg2
        y <- pure arg3
        (OneTuple (z)) <- runProcedure @'[ 'In, 'Out ] p x
        () <- closureP2IOII p z y
        pure ()
       )
      pure ()
    
    closureP2IOIO = \arg1 arg2 -> do
      -- solution: arg3[] arg3[0] arg3[0,3] arg3[1] arg3[1,4] p[0,1] p[1,2] x[0,2] x[1,3] y[0,0] y[1,1] z[1,0]
      -- cost: 6
      (arg3) <- (do
        p <- pure arg1
        x <- pure arg2
        (OneTuple (y)) <- runProcedure @'[ 'In, 'Out ] p x
        arg3 <- pure y
        pure (arg3)
       ) <|> (do
        p <- pure arg1
        x <- pure arg2
        (OneTuple (z)) <- runProcedure @'[ 'In, 'Out ] p x
        (OneTuple (y)) <- closureP2IOIO p z
        arg3 <- pure y
        pure (arg3)
       )
      pure (OneTuple (arg3))
    
    closureP2OIOI = \arg1 arg3 -> do
      -- solution: arg2[] arg2[0] arg2[0,2] arg2[1] arg2[1,3] p[0,1] p[1,2] x[0,0] x[1,0] y[0,3] y[1,4] z[1,1]
      -- cost: 6
      (arg2) <- (do
        p <- pure arg1
        y <- pure arg3
        (OneTuple (x)) <- runProcedure @'[ 'Out, 'In ] p y
        arg2 <- pure x
        pure (arg2)
       ) <|> (do
        p <- pure arg1
        y <- pure arg3
        (OneTuple (z)) <- closureP2OIOI p y
        (OneTuple (x)) <- runProcedure @'[ 'Out, 'In ] p z
        arg2 <- pure x
        pure (arg2)
       )
      pure (OneTuple (arg2))
    
    closureP2OOII = \arg1 arg2 arg3 -> Logic.once $ do
      -- solution: p[0,1] p[1,2] x[0,0] x[1,0] y[0,0] y[1,4] z[1,0]
      -- cost: 7
      () <- (do
        p <- pure arg1
        (x,y) <- runProcedure @'[ 'Out, 'Out ] p 
        guard $ arg2 == x
        guard $ arg3 == y
        pure ()
       ) <|> (do
        p <- pure arg1
        y <- pure arg3
        (x,z) <- runProcedure @'[ 'Out, 'Out ] p 
        guard $ arg2 == x
        () <- closureP2OOII p z y
        pure ()
       )
      pure ()
    
    closureP2OOIO = \arg1 arg2 -> do
      -- solution: arg3[] arg3[0] arg3[0,3] arg3[1] arg3[1,4] p[0,1] p[1,2] x[0,0] x[1,0] y[0,0] y[1,1] z[1,0]
      -- cost: 8
      (arg3) <- (do
        p <- pure arg1
        (x,y) <- runProcedure @'[ 'Out, 'Out ] p 
        guard $ arg2 == x
        arg3 <- pure y
        pure (arg3)
       ) <|> (do
        p <- pure arg1
        (x,z) <- runProcedure @'[ 'Out, 'Out ] p 
        guard $ arg2 == x
        (OneTuple (y)) <- closureP2OOIO p z
        arg3 <- pure y
        pure (arg3)
       )
      pure (OneTuple (arg3))
    
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
      -- solution: 
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
      -- solution: arg2[] arg2[0] arg2[0,1] arg2[1] arg2[1,1]
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
      -- solution: arg1[] arg1[0] arg1[0,0] arg1[1] arg1[1,0]
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
~closure[0]
~curry1[0]
~curry2[0]
~pred0[0,0]
~smaller[0,1,0]
((curry1[0,1,0,0] & curry2[0,1,0,0]) | ((curry1[0,1,0,0] & ~curry2[0,1,0,0]) | ((~curry1[0,1,0,0] & curry2[0,1,0,0]) | (~curry1[0,1,0,0] & ~curry2[0,1,0,0]))))
((~pred0[0,0] & (pred0(1) & (pred0(2) & (~x[0,0] & y[0,0])))) | ((~pred0[0,0] & (pred0(1) & (pred0(2) & (~x[0,0] & ~y[0,0])))) | ((~pred0[0,0] & (pred0(1) & (~pred0(2) & (x[0,0] & ~y[0,0])))) | ((~pred0[0,0] & (~pred0(1) & (pred0(2) & (~x[0,0] & y[0,0])))) | (~pred0[0,0] & (~pred0(1) & (pred0(2) & (~x[0,0] & ~y[0,0]))))))))
(curry1[0,1,0] <-> curry1[0,1,0,0])
(curry2[0,1,0] <-> curry2[0,1,0,0])
(smaller[0] <-> smaller[0,1])
(x[] <-> x[0])
(x[0] <-> x[0,0])
(y[] <-> y[0])
(y[0] <-> y[0,0])
(pred0(1) <-> curry1[0,1,0])
(pred0(2) <-> curry2[0,1,0])
1
-}

smallerTransitive = rget $ (procedure @'[ 'In, 'In ] smallerTransitiveII) :& (procedure @'[ 'In, 'Out ] smallerTransitiveIO) :& (procedure @'[ 'Out, 'In ] smallerTransitiveOI) :& RNil
  where
    smallerTransitiveII = \x y -> Logic.once $ do
      -- solution: curry2[0,1,0] curry2[0,1,0,0]
      -- cost: 3
      () <- (do
        let pred0 = procedure @'[ 'In, 'Out ] $
              \curry1 -> do
                (curry2) <- (do
                  (OneTuple (curry2)) <- runProcedure @'[ 'In, 'Out ] smaller curry1
                  pure (curry2)
                 )
                pure (OneTuple (curry2))
        () <- runProcedure @'[ 'PredMode '[ 'In, 'Out ], 'In, 'In ] closure pred0 x y
        pure ()
       )
      pure ()
    
    smallerTransitiveIO = \x -> do
      -- solution: curry2[0,1,0] curry2[0,1,0,0] y[] y[0] y[0,0]
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
      -- solution: curry1[0,1,0] curry1[0,1,0,0] x[] x[0] x[0,0]
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
~f[0]
~g[0]
~(b[0,0] & b[0,1])
(b[0,0] | b[0,1])
(a[] <-> a[0])
(a[0] <-> a[0,0])
(a[0,0] <-> g(1))
(b[0,0] <-> g(2))
(b[0,1] <-> f(1))
(f[] <-> f[0])
(g[] <-> g[0])
(z[] <-> z[0])
(z[0] <-> z[0,1])
(z[0,1] <-> f(2))
1
-}

compose = rget $ (procedure @'[ 'PredMode '[ 'In, 'In ], 'PredMode '[ 'In, 'Out ], 'In, 'In ] composeP2IIP2IOII) :& (procedure @'[ 'PredMode '[ 'In, 'In ], 'PredMode '[ 'Out, 'Out ], 'Out, 'In ] composeP2IIP2OOOI) :& (procedure @'[ 'PredMode '[ 'In, 'Out ], 'PredMode '[ 'In, 'Out ], 'In, 'Out ] composeP2IOP2IOIO) :& (procedure @'[ 'PredMode '[ 'In, 'Out ], 'PredMode '[ 'Out, 'Out ], 'Out, 'Out ] composeP2IOP2OOOO) :& (procedure @'[ 'PredMode '[ 'Out, 'In ], 'PredMode '[ 'In, 'In ], 'In, 'In ] composeP2OIP2IIII) :& (procedure @'[ 'PredMode '[ 'Out, 'In ], 'PredMode '[ 'Out, 'In ], 'Out, 'In ] composeP2OIP2OIOI) :& (procedure @'[ 'PredMode '[ 'Out, 'Out ], 'PredMode '[ 'In, 'In ], 'In, 'Out ] composeP2OOP2IIIO) :& (procedure @'[ 'PredMode '[ 'Out, 'Out ], 'PredMode '[ 'Out, 'In ], 'Out, 'Out ] composeP2OOP2OIOO) :& RNil
  where
    composeP2IIP2IOII = \f g a z -> Logic.once $ do
      -- solution: b[0,0]
      -- cost: 3
      () <- (do
        (OneTuple (b)) <- runProcedure g a
        () <- runProcedure f b z
        pure ()
       )
      pure ()
    
    composeP2IIP2OOOI = \f g z -> do
      -- solution: a[] a[0] a[0,0] b[0,0]
      -- cost: 4
      (a) <- (do
        (a,b) <- runProcedure g 
        () <- runProcedure f b z
        pure (a)
       )
      pure (OneTuple (a))
    
    composeP2IOP2IOIO = \f g a -> do
      -- solution: b[0,0] z[] z[0] z[0,1]
      -- cost: 4
      (z) <- (do
        (OneTuple (b)) <- runProcedure g a
        (OneTuple (z)) <- runProcedure f b
        pure (z)
       )
      pure (OneTuple (z))
    
    composeP2IOP2OOOO = \f g -> do
      -- solution: a[] a[0] a[0,0] b[0,0] z[] z[0] z[0,1]
      -- cost: 5
      (a,z) <- (do
        (a,b) <- runProcedure g 
        (OneTuple (z)) <- runProcedure f b
        pure (a,z)
       )
      pure (a,z)
    
    composeP2OIP2IIII = \f g a z -> Logic.once $ do
      -- solution: b[0,1]
      -- cost: 3
      () <- (do
        (OneTuple (b)) <- runProcedure f z
        () <- runProcedure g a b
        pure ()
       )
      pure ()
    
    composeP2OIP2OIOI = \f g z -> do
      -- solution: a[] a[0] a[0,0] b[0,1]
      -- cost: 4
      (a) <- (do
        (OneTuple (b)) <- runProcedure f z
        (OneTuple (a)) <- runProcedure g b
        pure (a)
       )
      pure (OneTuple (a))
    
    composeP2OOP2IIIO = \f g a -> do
      -- solution: b[0,1] z[] z[0] z[0,1]
      -- cost: 4
      (z) <- (do
        (b,z) <- runProcedure f 
        () <- runProcedure g a b
        pure (z)
       )
      pure (OneTuple (z))
    
    composeP2OOP2OIOO = \f g -> do
      -- solution: a[] a[0] a[0,0] b[0,1] z[] z[0] z[0,1]
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
~compose[0]
~curry1[0]
~curry2[0]
~plus[0,2,0]
~pred1[0,0]
~pred3[0,0]
~times[0,1,0]
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
(plus[0] <-> plus[0,2])
(times[0] <-> times[0,1])
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
      -- solution: curry2[0,2,0] curry2[0,2,0,0] data0[0,1,0,1] data2[0,2,0,1]
      -- cost: 4
      () <- (do
        let pred3 = procedure @'[ 'In, 'Out ] $
              \curry1 -> do
                (curry2) <- (do
                  data2 <- pure 1
                  (OneTuple (curry2)) <- runProcedure @'[ 'In, 'In, 'Out ] plus data2 curry1
                  pure (curry2)
                 )
                pure (OneTuple (curry2))
        let pred1 = procedure @'[ 'In, 'In ] $
              \curry1 curry2 -> do
                () <- (do
                  data0 <- pure 2
                  () <- runProcedure @'[ 'In, 'In, 'In ] times data0 curry1 curry2
                  pure ()
                 )
                pure ()
        () <- runProcedure @'[ 'PredMode '[ 'In, 'In ], 'PredMode '[ 'In, 'Out ], 'In, 'In ] compose pred1 pred3 a z
        pure ()
       )
      pure ()
    
    composeTestIO = \a -> do
      -- solution: curry2[0,1,0] curry2[0,1,0,0] curry2[0,2,0] curry2[0,2,0,0] data0[0,1,0,1] data2[0,2,0,1] z[] z[0] z[0,0]
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
      -- solution: a[] a[0] a[0,0] curry1[0,1,0] curry1[0,1,0,0] curry1[0,2,0] curry1[0,2,0,0] data0[0,1,0,1] data2[0,2,0,1]
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
    
{- inlineTest/1
inlineTest y :- ((data0 = y, data0 = 7)).
constraints:
~(data0[0,0] & data0[0,1])
~(data0[0,0] & y[0,0])
(data0[0,0] | data0[0,1])
(y[] <-> y[0])
(y[0] <-> y[0,0])
1
-}

inlineTest = rget $ (procedure @'[ 'In ] inlineTestI) :& (procedure @'[ 'Out ] inlineTestO) :& RNil
  where
    inlineTestI = \y -> Logic.once $ do
      -- solution: data0[0,0]
      -- cost: 0
      () <- (do
        data0 <- pure y
        guard $ data0 == 7
        pure ()
       )
      pure ()
    
    inlineTestO = do
      -- solution: data0[0,1] y[] y[0] y[0,0]
      -- cost: 0
      (y) <- (do
        data0 <- pure 7
        y <- pure data0
        pure (y)
       )
      pure (OneTuple (y))
    