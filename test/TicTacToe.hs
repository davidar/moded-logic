{-# LANGUAGE DataKinds, FlexibleContexts, NoImplicitPrelude, NoMonomorphismRestriction, TypeApplications #-}
module TicTacToe where

import qualified Control.Monad.Logic as Logic
import Control.Monad.Logic.Moded.Prelude

data Mark = X | O deriving (Eq, Ord, Read, Show)
data Location = Loc Int Int deriving (Eq, Ord, Read, Show)
data Entry = Entry Location Mark deriving (Eq, Ord, Read, Show)
data Direction = N | NE | E | SE | S | SW | W | NW deriving (Eq, Ord, Read, Show)
{- elem/2
elem arg1 arg2 :- ((arg2 = x0:_, x0 = x, arg1 = x); (arg2 = _:xs, elem x xs, arg1 = x)).
constraints:
x0[0,0]
xs[1,0]
~arg2[1,0]
~elem[1]
~(arg1[0,2] & x[0,2])
~(arg1[1,2] & x[1,2])
~(arg2[0,0] & x0[0,0])
~(x[0,1] & x[0,2])
~(x[1,1] & x[1,2])
~(x0[0,0] & x0[0,1])
~(x0[0,1] & x[0,1])
~(xs[1,0] & xs[1,1])
(x[0,1] | x[0,2])
(x[1,1] | x[1,2])
(x0[0,0] | x0[0,1])
(xs[1,0] | xs[1,1])
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg1[0] <-> arg1[0,2])
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
      -- solution: x[0,1] x[1,2] x0[0,0] xs[1,0]
      -- cost: 1
      () <- (do
        (x0:_) <- pure arg2
        x <- pure x0
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
      -- solution: arg1[] arg1[0] arg1[0,2] arg1[1] arg1[1,2] x[0,1] x[1,1] x0[0,0] xs[1,0]
      -- cost: 2
      (arg1) <- (do
        (x0:_) <- pure arg2
        x <- pure x0
        arg1 <- pure x
        pure (arg1)
       ) <|> (do
        (_:xs) <- pure arg2
        (OneTuple (x)) <- elemOI xs
        arg1 <- pure x
        pure (arg1)
       )
      pure (OneTuple (arg1))
    
{- boardSize/1
boardSize arg1 :- ((arg1 = 3)).
constraints:
(arg1[] <-> arg1[0])
(arg1[0] <-> arg1[0,0])
-}

boardSize = rget $ (procedure @'[ 'In ] boardSizeI) :& (procedure @'[ 'Out ] boardSizeO) :& RNil
  where
    boardSizeI = \arg1 -> Logic.once $ do
      -- solution: 
      -- cost: 0
      () <- (do
        guard $ arg1 == 3
        pure ()
       )
      pure ()
    
    boardSizeO = do
      -- solution: arg1[] arg1[0] arg1[0,0]
      -- cost: 0
      (arg1) <- (do
        arg1 <- pure 3
        pure (arg1)
       )
      pure (OneTuple (arg1))
    
{- marksForWin/1
marksForWin arg1 :- ((arg1 = 3)).
constraints:
(arg1[] <-> arg1[0])
(arg1[0] <-> arg1[0,0])
-}

marksForWin = rget $ (procedure @'[ 'In ] marksForWinI) :& (procedure @'[ 'Out ] marksForWinO) :& RNil
  where
    marksForWinI = \arg1 -> Logic.once $ do
      -- solution: 
      -- cost: 0
      () <- (do
        guard $ arg1 == 3
        pure ()
       )
      pure ()
    
    marksForWinO = do
      -- solution: arg1[] arg1[0] arg1[0,0]
      -- cost: 0
      (arg1) <- (do
        arg1 <- pure 3
        pure (arg1)
       )
      pure (OneTuple (arg1))
    
{- direction/2
direction arg1 arg2 :- ((arg1 = N, arg2 = S); (arg1 = NE, arg2 = SW); (arg1 = E, arg2 = W); (arg1 = SE, arg2 = NW)).
constraints:
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg1[] <-> arg1[2])
(arg1[] <-> arg1[3])
(arg1[0] <-> arg1[0,0])
(arg1[1] <-> arg1[1,0])
(arg1[2] <-> arg1[2,0])
(arg1[3] <-> arg1[3,0])
(arg2[] <-> arg2[0])
(arg2[] <-> arg2[1])
(arg2[] <-> arg2[2])
(arg2[] <-> arg2[3])
(arg2[0] <-> arg2[0,1])
(arg2[1] <-> arg2[1,1])
(arg2[2] <-> arg2[2,1])
(arg2[3] <-> arg2[3,1])
1
-}

direction = rget $ (procedure @'[ 'In, 'In ] directionII) :& (procedure @'[ 'In, 'Out ] directionIO) :& (procedure @'[ 'Out, 'In ] directionOI) :& (procedure @'[ 'Out, 'Out ] directionOO) :& RNil
  where
    directionII = \arg1 arg2 -> Logic.once $ do
      -- solution: 
      -- cost: 0
      () <- (do
        guard $ arg1 == N
        guard $ arg2 == S
        pure ()
       ) <|> (do
        guard $ arg1 == NE
        guard $ arg2 == SW
        pure ()
       ) <|> (do
        guard $ arg1 == E
        guard $ arg2 == W
        pure ()
       ) <|> (do
        guard $ arg1 == SE
        guard $ arg2 == NW
        pure ()
       )
      pure ()
    
    directionIO = \arg1 -> do
      -- solution: arg2[] arg2[0] arg2[0,1] arg2[1] arg2[1,1] arg2[2] arg2[2,1] arg2[3] arg2[3,1]
      -- cost: 0
      (arg2) <- (do
        guard $ arg1 == N
        arg2 <- pure S
        pure (arg2)
       ) <|> (do
        guard $ arg1 == NE
        arg2 <- pure SW
        pure (arg2)
       ) <|> (do
        guard $ arg1 == E
        arg2 <- pure W
        pure (arg2)
       ) <|> (do
        guard $ arg1 == SE
        arg2 <- pure NW
        pure (arg2)
       )
      pure (OneTuple (arg2))
    
    directionOI = \arg2 -> do
      -- solution: arg1[] arg1[0] arg1[0,0] arg1[1] arg1[1,0] arg1[2] arg1[2,0] arg1[3] arg1[3,0]
      -- cost: 0
      (arg1) <- (do
        arg1 <- pure N
        guard $ arg2 == S
        pure (arg1)
       ) <|> (do
        arg1 <- pure NE
        guard $ arg2 == SW
        pure (arg1)
       ) <|> (do
        arg1 <- pure E
        guard $ arg2 == W
        pure (arg1)
       ) <|> (do
        arg1 <- pure SE
        guard $ arg2 == NW
        pure (arg1)
       )
      pure (OneTuple (arg1))
    
    directionOO = do
      -- solution: arg1[] arg1[0] arg1[0,0] arg1[1] arg1[1,0] arg1[2] arg1[2,0] arg1[3] arg1[3,0] arg2[] arg2[0] arg2[0,1] arg2[1] arg2[1,1] arg2[2] arg2[2,1] arg2[3] arg2[3,1]
      -- cost: 0
      (arg1,arg2) <- (do
        arg1 <- pure N
        arg2 <- pure S
        pure (arg1,arg2)
       ) <|> (do
        arg1 <- pure NE
        arg2 <- pure SW
        pure (arg1,arg2)
       ) <|> (do
        arg1 <- pure E
        arg2 <- pure W
        pure (arg1,arg2)
       ) <|> (do
        arg1 <- pure SE
        arg2 <- pure NW
        pure (arg1,arg2)
       )
      pure (arg1,arg2)
    
{- move/3
move arg1 arg2 arg3 :- ((arg1 = N, arg2 = Loc x0 y, x0 = x, arg3 = Loc x1 y', x1 = x, succ y y'); (arg1 = NE, arg2 = Loc x y, arg3 = Loc x' y', succ x x', succ y y'); (arg1 = E, arg2 = Loc x y2, y2 = y, arg3 = Loc x' y3, y3 = y, succ x x'); (arg1 = SE, arg2 = Loc x y, arg3 = Loc x' y', succ x x', succ y' y); (arg1 = S, arg2 = Loc x4 y, x4 = x, arg3 = Loc x5 y', x5 = x, succ y' y); (arg1 = SW, arg2 = Loc x y, arg3 = Loc x' y', succ x' x, succ y' y); (arg1 = W, arg2 = Loc x y6, y6 = y, arg3 = Loc x' y7, y7 = y, succ x' x); (arg1 = NW, arg2 = Loc x y, arg3 = Loc x' y', succ x' x, succ y y')).
constraints:
~succ[0]
~succ[1]
~succ[2]
~succ[3]
~succ[4]
~succ[5]
~succ[6]
~succ[7]
~(arg2[0,1] & x0[0,1])
~(arg2[1,1] & x[1,1])
~(arg2[2,1] & x[2,1])
~(arg2[3,1] & x[3,1])
~(arg2[4,1] & x4[4,1])
~(arg2[5,1] & x[5,1])
~(arg2[6,1] & x[6,1])
~(arg2[7,1] & x[7,1])
~(arg3[0,3] & x1[0,3])
~(arg3[1,2] & x'[1,2])
~(arg3[2,3] & x'[2,3])
~(arg3[3,2] & x'[3,2])
~(arg3[4,3] & x5[4,3])
~(arg3[5,2] & x'[5,2])
~(arg3[6,3] & x'[6,3])
~(arg3[7,2] & x'[7,2])
~(x[0,2] & x[0,4])
~(x[1,1] & x[1,3])
~(x[2,1] & x[2,5])
~(x[3,1] & x[3,3])
~(x[4,2] & x[4,4])
~(x[5,1] & x[5,3])
~(x[6,1] & x[6,5])
~(x[7,1] & x[7,3])
~(x'[1,2] & x'[1,3])
~(x'[2,3] & x'[2,5])
~(x'[3,2] & x'[3,3])
~(x'[5,2] & x'[5,3])
~(x'[6,3] & x'[6,5])
~(x'[7,2] & x'[7,3])
~(x0[0,1] & x0[0,2])
~(x0[0,2] & x[0,2])
~(x1[0,3] & x1[0,4])
~(x1[0,4] & x[0,4])
~(x4[4,1] & x4[4,2])
~(x4[4,2] & x[4,2])
~(x5[4,3] & x5[4,4])
~(x5[4,4] & x[4,4])
~(y[0,1] & y[0,5])
~(y[1,1] & y[1,4])
~(y[2,2] & y[2,4])
~(y[3,1] & y[3,4])
~(y[4,1] & y[4,5])
~(y[5,1] & y[5,4])
~(y[6,2] & y[6,4])
~(y[7,1] & y[7,4])
~(y'[0,3] & y'[0,5])
~(y'[1,2] & y'[1,4])
~(y'[3,2] & y'[3,4])
~(y'[4,3] & y'[4,5])
~(y'[5,2] & y'[5,4])
~(y'[7,2] & y'[7,4])
~(y2[2,1] & y2[2,2])
~(y2[2,2] & y[2,2])
~(y3[2,3] & y3[2,4])
~(y3[2,4] & y[2,4])
~(y6[6,1] & y6[6,2])
~(y6[6,2] & y[6,2])
~(y7[6,3] & y7[6,4])
~(y7[6,4] & y[6,4])
(x[0,2] | x[0,4])
(x[1,1] | x[1,3])
(x[2,1] | x[2,5])
(x[3,1] | x[3,3])
(x[4,2] | x[4,4])
(x[5,1] | x[5,3])
(x[6,1] | x[6,5])
(x[7,1] | x[7,3])
(x'[1,2] | x'[1,3])
(x'[2,3] | x'[2,5])
(x'[3,2] | x'[3,3])
(x'[5,2] | x'[5,3])
(x'[6,3] | x'[6,5])
(x'[7,2] | x'[7,3])
(x0[0,1] | x0[0,2])
(x1[0,3] | x1[0,4])
(x4[4,1] | x4[4,2])
(x5[4,3] | x5[4,4])
(y[0,1] | y[0,5])
(y[1,1] | y[1,4])
(y[2,2] | y[2,4])
(y[3,1] | y[3,4])
(y[4,1] | y[4,5])
(y[5,1] | y[5,4])
(y[6,2] | y[6,4])
(y[7,1] | y[7,4])
(y'[0,3] | y'[0,5])
(y'[1,2] | y'[1,4])
(y'[3,2] | y'[3,4])
(y'[4,3] | y'[4,5])
(y'[5,2] | y'[5,4])
(y'[7,2] | y'[7,4])
(y2[2,1] | y2[2,2])
(y3[2,3] | y3[2,4])
(y6[6,1] | y6[6,2])
(y7[6,3] | y7[6,4])
((x[1,3] & ~x'[1,3]) | ((~x[1,3] & x'[1,3]) | (~x[1,3] & ~x'[1,3])))
((x[2,5] & ~x'[2,5]) | ((~x[2,5] & x'[2,5]) | (~x[2,5] & ~x'[2,5])))
((x[3,3] & ~x'[3,3]) | ((~x[3,3] & x'[3,3]) | (~x[3,3] & ~x'[3,3])))
((x'[5,3] & ~x[5,3]) | ((~x'[5,3] & x[5,3]) | (~x'[5,3] & ~x[5,3])))
((x'[6,5] & ~x[6,5]) | ((~x'[6,5] & x[6,5]) | (~x'[6,5] & ~x[6,5])))
((x'[7,3] & ~x[7,3]) | ((~x'[7,3] & x[7,3]) | (~x'[7,3] & ~x[7,3])))
((y[0,5] & ~y'[0,5]) | ((~y[0,5] & y'[0,5]) | (~y[0,5] & ~y'[0,5])))
((y[1,4] & ~y'[1,4]) | ((~y[1,4] & y'[1,4]) | (~y[1,4] & ~y'[1,4])))
((y[7,4] & ~y'[7,4]) | ((~y[7,4] & y'[7,4]) | (~y[7,4] & ~y'[7,4])))
((y'[3,4] & ~y[3,4]) | ((~y'[3,4] & y[3,4]) | (~y'[3,4] & ~y[3,4])))
((y'[4,5] & ~y[4,5]) | ((~y'[4,5] & y[4,5]) | (~y'[4,5] & ~y[4,5])))
((y'[5,4] & ~y[5,4]) | ((~y'[5,4] & y[5,4]) | (~y'[5,4] & ~y[5,4])))
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg1[] <-> arg1[2])
(arg1[] <-> arg1[3])
(arg1[] <-> arg1[4])
(arg1[] <-> arg1[5])
(arg1[] <-> arg1[6])
(arg1[] <-> arg1[7])
(arg1[0] <-> arg1[0,0])
(arg1[1] <-> arg1[1,0])
(arg1[2] <-> arg1[2,0])
(arg1[3] <-> arg1[3,0])
(arg1[4] <-> arg1[4,0])
(arg1[5] <-> arg1[5,0])
(arg1[6] <-> arg1[6,0])
(arg1[7] <-> arg1[7,0])
(arg2[] <-> arg2[0])
(arg2[] <-> arg2[1])
(arg2[] <-> arg2[2])
(arg2[] <-> arg2[3])
(arg2[] <-> arg2[4])
(arg2[] <-> arg2[5])
(arg2[] <-> arg2[6])
(arg2[] <-> arg2[7])
(arg2[0] <-> arg2[0,1])
(arg2[1] <-> arg2[1,1])
(arg2[2] <-> arg2[2,1])
(arg2[3] <-> arg2[3,1])
(arg2[4] <-> arg2[4,1])
(arg2[5] <-> arg2[5,1])
(arg2[6] <-> arg2[6,1])
(arg2[7] <-> arg2[7,1])
(arg3[] <-> arg3[0])
(arg3[] <-> arg3[1])
(arg3[] <-> arg3[2])
(arg3[] <-> arg3[3])
(arg3[] <-> arg3[4])
(arg3[] <-> arg3[5])
(arg3[] <-> arg3[6])
(arg3[] <-> arg3[7])
(arg3[0] <-> arg3[0,3])
(arg3[1] <-> arg3[1,2])
(arg3[2] <-> arg3[2,3])
(arg3[3] <-> arg3[3,2])
(arg3[4] <-> arg3[4,3])
(arg3[5] <-> arg3[5,2])
(arg3[6] <-> arg3[6,3])
(arg3[7] <-> arg3[7,2])
(x[1,1] <-> y[1,1])
(x[2,1] <-> y2[2,1])
(x[3,1] <-> y[3,1])
(x[5,1] <-> y[5,1])
(x[6,1] <-> y6[6,1])
(x[7,1] <-> y[7,1])
(x'[1,2] <-> y'[1,2])
(x'[2,3] <-> y3[2,3])
(x'[3,2] <-> y'[3,2])
(x'[5,2] <-> y'[5,2])
(x'[6,3] <-> y7[6,3])
(x'[7,2] <-> y'[7,2])
(x0[0,1] <-> y[0,1])
(x1[0,3] <-> y'[0,3])
(x4[4,1] <-> y[4,1])
(x5[4,3] <-> y'[4,3])
1
-}

move = rget $ (procedure @'[ 'In, 'In, 'Out ] moveIIO) :& RNil
  where
    moveIIO = \arg1 arg2 -> do
      -- solution: arg3[] arg3[0] arg3[0,3] arg3[1] arg3[1,2] arg3[2] arg3[2,3] arg3[3] arg3[3,2] arg3[4] arg3[4,3] arg3[5] arg3[5,2] arg3[6] arg3[6,3] arg3[7] arg3[7,2] x[0,2] x[1,1] x[2,1] x[3,1] x[4,2] x[5,1] x[6,1] x[7,1] x'[1,3] x'[2,5] x'[3,3] x'[5,3] x'[6,5] x'[7,3] x0[0,1] x1[0,4] x4[4,1] x5[4,4] y[0,1] y[1,1] y[2,2] y[3,1] y[4,1] y[5,1] y[6,2] y[7,1] y'[0,5] y'[1,4] y'[3,4] y'[4,5] y'[5,4] y'[7,4] y2[2,1] y3[2,4] y6[6,1] y7[6,4]
      -- cost: 24
      (arg3) <- (do
        guard $ arg1 == N
        (Loc x0 y) <- pure arg2
        x <- pure x0
        x1 <- pure x
        (OneTuple (y')) <- runProcedure @'[ 'In, 'Out ] succ y
        arg3 <- pure (Loc x1 y')
        pure (arg3)
       ) <|> (do
        guard $ arg1 == NE
        (Loc x y) <- pure arg2
        (OneTuple (x')) <- runProcedure @'[ 'In, 'Out ] succ x
        (OneTuple (y')) <- runProcedure @'[ 'In, 'Out ] succ y
        arg3 <- pure (Loc x' y')
        pure (arg3)
       ) <|> (do
        guard $ arg1 == E
        (Loc x y2) <- pure arg2
        y <- pure y2
        y3 <- pure y
        (OneTuple (x')) <- runProcedure @'[ 'In, 'Out ] succ x
        arg3 <- pure (Loc x' y3)
        pure (arg3)
       ) <|> (do
        guard $ arg1 == SE
        (Loc x y) <- pure arg2
        (OneTuple (x')) <- runProcedure @'[ 'In, 'Out ] succ x
        (OneTuple (y')) <- runProcedure @'[ 'Out, 'In ] succ y
        arg3 <- pure (Loc x' y')
        pure (arg3)
       ) <|> (do
        guard $ arg1 == S
        (Loc x4 y) <- pure arg2
        x <- pure x4
        x5 <- pure x
        (OneTuple (y')) <- runProcedure @'[ 'Out, 'In ] succ y
        arg3 <- pure (Loc x5 y')
        pure (arg3)
       ) <|> (do
        guard $ arg1 == SW
        (Loc x y) <- pure arg2
        (OneTuple (x')) <- runProcedure @'[ 'Out, 'In ] succ x
        (OneTuple (y')) <- runProcedure @'[ 'Out, 'In ] succ y
        arg3 <- pure (Loc x' y')
        pure (arg3)
       ) <|> (do
        guard $ arg1 == W
        (Loc x y6) <- pure arg2
        y <- pure y6
        y7 <- pure y
        (OneTuple (x')) <- runProcedure @'[ 'Out, 'In ] succ x
        arg3 <- pure (Loc x' y7)
        pure (arg3)
       ) <|> (do
        guard $ arg1 == NW
        (Loc x y) <- pure arg2
        (OneTuple (x')) <- runProcedure @'[ 'Out, 'In ] succ x
        (OneTuple (y')) <- runProcedure @'[ 'In, 'Out ] succ y
        arg3 <- pure (Loc x' y')
        pure (arg3)
       )
      pure (OneTuple (arg3))
    
{- location/1
location arg1 :- ((arg1 = Loc x y, boardSize n, (>=) x data0, data0 = 0, (>=) y data1, data1 = 0, (<) x n, (<) y n)).
constraints:
~(<)[0]
~(>=)[0]
~boardSize[0]
~(arg1[0,0] & x[0,0])
~(data0[0,2] & data0[0,3])
~(data1[0,4] & data1[0,5])
~(n[0,1] & n[0,6])
~(n[0,1] & n[0,7])
~(n[0,6] & n[0,7])
~(x[0,0] & x[0,2])
~(x[0,0] & x[0,6])
~(x[0,2] & x[0,6])
~(y[0,0] & y[0,4])
~(y[0,0] & y[0,7])
~(y[0,4] & y[0,7])
(~x[0,2] & ~data0[0,2])
(~x[0,6] & ~n[0,6])
(~y[0,4] & ~data1[0,4])
(~y[0,7] & ~n[0,7])
(data0[0,2] | data0[0,3])
(data1[0,4] | data1[0,5])
(n[0,1] | ~n[0,1])
(n[0,1] | (n[0,6] | n[0,7]))
(x[0,0] | (x[0,2] | x[0,6]))
(y[0,0] | (y[0,4] | y[0,7]))
(arg1[] <-> arg1[0])
(arg1[0] <-> arg1[0,0])
(x[0,0] <-> y[0,0])
1
-}

location = rget $ (procedure @'[ 'In ] locationI) :& RNil
  where
    locationI = \arg1 -> Logic.once $ do
      -- solution: data0[0,3] data1[0,5] n[0,1] x[0,0] y[0,0]
      -- cost: 6
      () <- (do
        (Loc x y) <- pure arg1
        data0 <- pure 0
        data1 <- pure 0
        guard $ (>=) x data0
        guard $ (>=) y data1
        (OneTuple (n)) <- runProcedure @'[ 'Out ] boardSize 
        guard $ (<) x n
        guard $ (<) y n
        pure ()
       )
      pure ()
    
{- loop/8
loop board dir m n loc loc' rn rloc :- ((if (location loc', elem data0 board, data0 = Entry loc' m) then (succ n n', move dir loc' loc'', loop board dir m n' loc' loc'' rn rloc) else (rn = n, rloc = loc))).
constraints:
data0[0,0]
~board[0,0]
~board[0,0,0,1]
~board[0,0,1,2]
~dir[0,0,1]
~elem[0,0,0]
~loc[0,0,2]
~loc'[0,0]
~loc'[0,0,0,0]
~location[0,0,0]
~loop[0,0,1]
~m[0,0]
~m[0,0,0,2]
~m[0,0,1,2]
~move[0,0,1]
~succ[0,0,1]
~(data0[0,0,0,1] & data0[0,0,0,2])
~(data0[0,0,0,2] & loc'[0,0,0,2])
~(dir[0,0,1,1] & dir[0,0,1,2])
~(loc'[0,0,0,0] & loc'[0,0,0,2])
~(loc'[0,0,1,1] & loc'[0,0,1,2])
~(loc''[0,0,1,1] & loc''[0,0,1,2])
~(n'[0,0,1,0] & n'[0,0,1,2])
~(rloc[0,0,2,1] & loc[0,0,2,1])
~(rn[0,0,2,0] & n[0,0,2,0])
~(loc'[0,0,0,0] | loc'[0,0,0,2])
~(loc'[0,0,1,1] | loc'[0,0,1,2])
(~dir[0,0,1,1] & (~loc'[0,0,1,1] & loc''[0,0,1,1]))
(data0[0,0,0,1] | data0[0,0,0,2])
(loc''[0,0,1,1] | loc''[0,0,1,2])
(n'[0,0,1,0] | n'[0,0,1,2])
((data0[0,0,0,1] & ~board[0,0,0,1]) | (~data0[0,0,0,1] & ~board[0,0,0,1]))
((n[0,0,1,0] & ~n'[0,0,1,0]) | ((~n[0,0,1,0] & n'[0,0,1,0]) | (~n[0,0,1,0] & ~n'[0,0,1,0])))
(board[] <-> board[0])
(board[0] <-> board[0,0])
(board[0,0,1,2] <-> board[])
(data0[0] <-> data0[0,0])
(dir[] <-> dir[0])
(dir[0] <-> dir[0,0])
(dir[0,0] <-> dir[0,0,1])
(dir[0,0,1] <-> (dir[0,0,1,1] | dir[0,0,1,2]))
(dir[0,0,1,2] <-> dir[])
(elem[0] <-> elem[0,0])
(elem[0,0] <-> elem[0,0,0])
(loc[] <-> loc[0])
(loc[0] <-> loc[0,0])
(loc[0,0] <-> loc[0,0,2])
(loc[0,0,2] <-> loc[0,0,2,1])
(loc'[] <-> loc'[0])
(loc'[0] <-> loc'[0,0])
(loc'[0,0,0,2] <-> m[0,0,0,2])
(loc'[0,0,1,2] <-> loc[])
(loc''[0,0,1,2] <-> loc'[])
(location[0] <-> location[0,0])
(location[0,0] <-> location[0,0,0])
(loop[0] <-> loop[0,0])
(loop[0,0] <-> loop[0,0,1])
(m[] <-> m[0])
(m[0] <-> m[0,0])
(m[0,0,1,2] <-> m[])
(move[0] <-> move[0,0])
(move[0,0] <-> move[0,0,1])
(n[] <-> n[0])
(n[0] <-> n[0,0])
(n[0,0] <-> (n[0,0,1] | n[0,0,2]))
(n[0,0,1] <-> n[0,0,1,0])
(n[0,0,1] <-> n[0,0,2])
(n[0,0,2] <-> n[0,0,2,0])
(n'[0,0,1,2] <-> n[])
(rloc[] <-> rloc[0])
(rloc[0] <-> rloc[0,0])
(rloc[0,0] <-> (rloc[0,0,1] | rloc[0,0,2]))
(rloc[0,0,1] <-> rloc[0,0,1,2])
(rloc[0,0,1] <-> rloc[0,0,2])
(rloc[0,0,1,2] <-> rloc[])
(rloc[0,0,2] <-> rloc[0,0,2,1])
(rn[] <-> rn[0])
(rn[0] <-> rn[0,0])
(rn[0,0] <-> (rn[0,0,1] | rn[0,0,2]))
(rn[0,0,1] <-> rn[0,0,1,2])
(rn[0,0,1] <-> rn[0,0,2])
(rn[0,0,1,2] <-> rn[])
(rn[0,0,2] <-> rn[0,0,2,0])
(succ[0] <-> succ[0,0])
(succ[0,0] <-> succ[0,0,1])
1
-}

loop = rget $ (procedure @'[ 'In, 'In, 'In, 'In, 'In, 'In, 'In, 'In ] loopIIIIIIII) :& (procedure @'[ 'In, 'In, 'In, 'In, 'In, 'In, 'In, 'Out ] loopIIIIIIIO) :& (procedure @'[ 'In, 'In, 'In, 'In, 'In, 'In, 'Out, 'In ] loopIIIIIIOI) :& (procedure @'[ 'In, 'In, 'In, 'In, 'In, 'In, 'Out, 'Out ] loopIIIIIIOO) :& (procedure @'[ 'In, 'In, 'In, 'Out, 'In, 'In, 'In, 'In ] loopIIIOIIII) :& (procedure @'[ 'In, 'In, 'In, 'Out, 'In, 'In, 'In, 'Out ] loopIIIOIIIO) :& RNil
  where
    loopIIIIIIII = \board dir m n loc loc' rn rloc -> Logic.once $ do
      -- solution: data0[0] data0[0,0] data0[0,0,0,2] loc''[0,0,1,1] n'[0,0,1,0]
      -- cost: 7
      () <- (do
        () <- Logic.ifte ((do
          data0 <- pure (Entry loc' m)
          () <- runProcedure @'[ 'In, 'In ] elem data0 board
          () <- runProcedure @'[ 'In ] location loc'
          pure ()
         )) (\() -> (do
          (OneTuple (loc'')) <- runProcedure @'[ 'In, 'In, 'Out ] move dir loc'
          (OneTuple (n')) <- runProcedure @'[ 'In, 'Out ] succ n
          () <- loopIIIIIIII board dir m n' loc' loc'' rn rloc
          pure ()
         )) ((do
          guard $ rloc == loc
          guard $ rn == n
          pure ()
         ))
        pure ()
       )
      pure ()
    
    loopIIIIIIIO = \board dir m n loc loc' rn -> do
      -- solution: data0[0] data0[0,0] data0[0,0,0,2] loc''[0,0,1,1] n'[0,0,1,0] rloc[] rloc[0] rloc[0,0] rloc[0,0,1] rloc[0,0,1,2] rloc[0,0,2] rloc[0,0,2,1]
      -- cost: 8
      (rloc) <- (do
        (rloc) <- Logic.ifte ((do
          data0 <- pure (Entry loc' m)
          () <- runProcedure @'[ 'In, 'In ] elem data0 board
          () <- runProcedure @'[ 'In ] location loc'
          pure ()
         )) (\() -> (do
          (OneTuple (loc'')) <- runProcedure @'[ 'In, 'In, 'Out ] move dir loc'
          (OneTuple (n')) <- runProcedure @'[ 'In, 'Out ] succ n
          (OneTuple (rloc)) <- loopIIIIIIIO board dir m n' loc' loc'' rn
          pure (rloc)
         )) ((do
          rloc <- pure loc
          guard $ rn == n
          pure (rloc)
         ))
        pure (rloc)
       )
      pure (OneTuple (rloc))
    
    loopIIIIIIOI = \board dir m n loc loc' rloc -> do
      -- solution: data0[0] data0[0,0] data0[0,0,0,2] loc''[0,0,1,1] n'[0,0,1,0] rn[] rn[0] rn[0,0] rn[0,0,1] rn[0,0,1,2] rn[0,0,2] rn[0,0,2,0]
      -- cost: 8
      (rn) <- (do
        (rn) <- Logic.ifte ((do
          data0 <- pure (Entry loc' m)
          () <- runProcedure @'[ 'In, 'In ] elem data0 board
          () <- runProcedure @'[ 'In ] location loc'
          pure ()
         )) (\() -> (do
          (OneTuple (loc'')) <- runProcedure @'[ 'In, 'In, 'Out ] move dir loc'
          (OneTuple (n')) <- runProcedure @'[ 'In, 'Out ] succ n
          (OneTuple (rn)) <- loopIIIIIIOI board dir m n' loc' loc'' rloc
          pure (rn)
         )) ((do
          guard $ rloc == loc
          rn <- pure n
          pure (rn)
         ))
        pure (rn)
       )
      pure (OneTuple (rn))
    
    loopIIIIIIOO = \board dir m n loc loc' -> do
      -- solution: data0[0] data0[0,0] data0[0,0,0,2] loc''[0,0,1,1] n'[0,0,1,0] rloc[] rloc[0] rloc[0,0] rloc[0,0,1] rloc[0,0,1,2] rloc[0,0,2] rloc[0,0,2,1] rn[] rn[0] rn[0,0] rn[0,0,1] rn[0,0,1,2] rn[0,0,2] rn[0,0,2,0]
      -- cost: 9
      (rloc,rn) <- (do
        (rloc,rn) <- Logic.ifte ((do
          data0 <- pure (Entry loc' m)
          () <- runProcedure @'[ 'In, 'In ] elem data0 board
          () <- runProcedure @'[ 'In ] location loc'
          pure ()
         )) (\() -> (do
          (OneTuple (loc'')) <- runProcedure @'[ 'In, 'In, 'Out ] move dir loc'
          (OneTuple (n')) <- runProcedure @'[ 'In, 'Out ] succ n
          (rn,rloc) <- loopIIIIIIOO board dir m n' loc' loc''
          pure (rloc,rn)
         )) ((do
          rloc <- pure loc
          rn <- pure n
          pure (rloc,rn)
         ))
        pure (rloc,rn)
       )
      pure (rn,rloc)
    
    loopIIIOIIII = \board dir m loc loc' rn rloc -> do
      -- solution: data0[0] data0[0,0] data0[0,0,0,2] loc''[0,0,1,1] n[] n[0] n[0,0] n[0,0,1] n[0,0,1,0] n[0,0,2] n[0,0,2,0] n'[0,0,1,2]
      -- cost: 8
      (n) <- (do
        (n) <- Logic.ifte ((do
          data0 <- pure (Entry loc' m)
          () <- runProcedure @'[ 'In, 'In ] elem data0 board
          () <- runProcedure @'[ 'In ] location loc'
          pure ()
         )) (\() -> (do
          (OneTuple (loc'')) <- runProcedure @'[ 'In, 'In, 'Out ] move dir loc'
          (OneTuple (n')) <- loopIIIOIIII board dir m loc' loc'' rn rloc
          (OneTuple (n)) <- runProcedure @'[ 'Out, 'In ] succ n'
          pure (n)
         )) ((do
          guard $ rloc == loc
          n <- pure rn
          pure (n)
         ))
        pure (n)
       )
      pure (OneTuple (n))
    
    loopIIIOIIIO = \board dir m loc loc' rn -> do
      -- solution: data0[0] data0[0,0] data0[0,0,0,2] loc''[0,0,1,1] n[] n[0] n[0,0] n[0,0,1] n[0,0,1,0] n[0,0,2] n[0,0,2,0] n'[0,0,1,2] rloc[] rloc[0] rloc[0,0] rloc[0,0,1] rloc[0,0,1,2] rloc[0,0,2] rloc[0,0,2,1]
      -- cost: 9
      (n,rloc) <- (do
        (n,rloc) <- Logic.ifte ((do
          data0 <- pure (Entry loc' m)
          () <- runProcedure @'[ 'In, 'In ] elem data0 board
          () <- runProcedure @'[ 'In ] location loc'
          pure ()
         )) (\() -> (do
          (OneTuple (loc'')) <- runProcedure @'[ 'In, 'In, 'Out ] move dir loc'
          (n',rloc) <- loopIIIOIIIO board dir m loc' loc'' rn
          (OneTuple (n)) <- runProcedure @'[ 'Out, 'In ] succ n'
          pure (n,rloc)
         )) ((do
          rloc <- pure loc
          n <- pure rn
          pure (n,rloc)
         ))
        pure (n,rloc)
       )
      pure (n,rloc)
    
{- extendLocation/6
extendLocation board dir m loc carg7 carg8 :- ((loop board dir m data0 loc loc' carg7 carg8, data0 = 0, move dir loc loc')).
constraints:
~loop[0]
~move[0]
~(data0[0,0] & data0[0,1])
~(dir[0,0] & dir[0,2])
~(loc[0,0] & loc[0,2])
~(loc'[0,0] & loc'[0,2])
(~dir[0,2] & (~loc[0,2] & loc'[0,2]))
(data0[0,0] | data0[0,1])
(loc'[0,0] | loc'[0,2])
((~board[0,0] & (~dir[0,0] & (~m[0,0] & (data0[0,0] & (~loc[0,0] & (~loc'[0,0] & (~carg7[0,0] & carg8[0,0]))))))) | ((~board[0,0] & (~dir[0,0] & (~m[0,0] & (data0[0,0] & (~loc[0,0] & (~loc'[0,0] & (~carg7[0,0] & ~carg8[0,0]))))))) | ((~board[0,0] & (~dir[0,0] & (~m[0,0] & (~data0[0,0] & (~loc[0,0] & (~loc'[0,0] & (carg7[0,0] & carg8[0,0]))))))) | ((~board[0,0] & (~dir[0,0] & (~m[0,0] & (~data0[0,0] & (~loc[0,0] & (~loc'[0,0] & (carg7[0,0] & ~carg8[0,0]))))))) | ((~board[0,0] & (~dir[0,0] & (~m[0,0] & (~data0[0,0] & (~loc[0,0] & (~loc'[0,0] & (~carg7[0,0] & carg8[0,0]))))))) | (~board[0,0] & (~dir[0,0] & (~m[0,0] & (~data0[0,0] & (~loc[0,0] & (~loc'[0,0] & (~carg7[0,0] & ~carg8[0,0]))))))))))))
(board[] <-> board[0])
(board[0] <-> board[0,0])
(carg7[] <-> carg7[0])
(carg7[0] <-> carg7[0,0])
(carg8[] <-> carg8[0])
(carg8[0] <-> carg8[0,0])
(dir[] <-> dir[0])
(dir[0] <-> (dir[0,0] | dir[0,2]))
(loc[] <-> loc[0])
(loc[0] <-> (loc[0,0] | loc[0,2]))
(m[] <-> m[0])
(m[0] <-> m[0,0])
1
-}

extendLocation = rget $ (procedure @'[ 'In, 'In, 'In, 'In, 'In, 'In ] extendLocationIIIIII) :& (procedure @'[ 'In, 'In, 'In, 'In, 'In, 'Out ] extendLocationIIIIIO) :& (procedure @'[ 'In, 'In, 'In, 'In, 'Out, 'In ] extendLocationIIIIOI) :& (procedure @'[ 'In, 'In, 'In, 'In, 'Out, 'Out ] extendLocationIIIIOO) :& RNil
  where
    extendLocationIIIIII = \board dir m loc carg7 carg8 -> Logic.once $ do
      -- solution: data0[0,1] loc'[0,2]
      -- cost: 3
      () <- (do
        data0 <- pure 0
        (OneTuple (loc')) <- runProcedure @'[ 'In, 'In, 'Out ] move dir loc
        () <- runProcedure @'[ 'In, 'In, 'In, 'In, 'In, 'In, 'In, 'In ] loop board dir m data0 loc loc' carg7 carg8
        pure ()
       )
      pure ()
    
    extendLocationIIIIIO = \board dir m loc carg7 -> do
      -- solution: carg8[] carg8[0] carg8[0,0] data0[0,1] loc'[0,2]
      -- cost: 4
      (carg8) <- (do
        data0 <- pure 0
        (OneTuple (loc')) <- runProcedure @'[ 'In, 'In, 'Out ] move dir loc
        (OneTuple (carg8)) <- runProcedure @'[ 'In, 'In, 'In, 'In, 'In, 'In, 'In, 'Out ] loop board dir m data0 loc loc' carg7
        pure (carg8)
       )
      pure (OneTuple (carg8))
    
    extendLocationIIIIOI = \board dir m loc carg8 -> do
      -- solution: carg7[] carg7[0] carg7[0,0] data0[0,1] loc'[0,2]
      -- cost: 4
      (carg7) <- (do
        data0 <- pure 0
        (OneTuple (loc')) <- runProcedure @'[ 'In, 'In, 'Out ] move dir loc
        (OneTuple (carg7)) <- runProcedure @'[ 'In, 'In, 'In, 'In, 'In, 'In, 'Out, 'In ] loop board dir m data0 loc loc' carg8
        pure (carg7)
       )
      pure (OneTuple (carg7))
    
    extendLocationIIIIOO = \board dir m loc -> do
      -- solution: carg7[] carg7[0] carg7[0,0] carg8[] carg8[0] carg8[0,0] data0[0,1] loc'[0,2]
      -- cost: 5
      (carg7,carg8) <- (do
        data0 <- pure 0
        (OneTuple (loc')) <- runProcedure @'[ 'In, 'In, 'Out ] move dir loc
        (carg7,carg8) <- runProcedure @'[ 'In, 'In, 'In, 'In, 'In, 'In, 'Out, 'Out ] loop board dir m data0 loc loc'
        pure (carg7,carg8)
       )
      pure (carg7,carg8)
    
{- cluster/7
cluster board m loc dir1 dir2 n end :- ((extendLocation board dir1 m loc n1 end, extendLocation board dir2 m loc n2 _, plus n1 n2 n', succ n' n)).
constraints:
~extendLocation[0]
~plus[0]
~succ[0]
~(board[0,0] & board[0,1])
~(loc[0,0] & loc[0,1])
~(m[0,0] & m[0,1])
~(n'[0,2] & n'[0,3])
~(n1[0,0] & n1[0,2])
~(n2[0,1] & n2[0,2])
(n'[0,2] | n'[0,3])
(n1[0,0] | n1[0,2])
(n2[0,1] | n2[0,2])
((n'[0,3] & ~n[0,3]) | ((~n'[0,3] & n[0,3]) | (~n'[0,3] & ~n[0,3])))
((n1[0,2] & (~n2[0,2] & ~n'[0,2])) | ((~n1[0,2] & (n2[0,2] & ~n'[0,2])) | ((~n1[0,2] & (~n2[0,2] & n'[0,2])) | (~n1[0,2] & (~n2[0,2] & ~n'[0,2])))))
((~board[0,0] & (~dir1[0,0] & (~m[0,0] & (~loc[0,0] & (n1[0,0] & end[0,0]))))) | ((~board[0,0] & (~dir1[0,0] & (~m[0,0] & (~loc[0,0] & (n1[0,0] & ~end[0,0]))))) | ((~board[0,0] & (~dir1[0,0] & (~m[0,0] & (~loc[0,0] & (~n1[0,0] & end[0,0]))))) | (~board[0,0] & (~dir1[0,0] & (~m[0,0] & (~loc[0,0] & (~n1[0,0] & ~end[0,0]))))))))
((~board[0,1] & (~dir2[0,1] & (~m[0,1] & (~loc[0,1] & n2[0,1])))) | (~board[0,1] & (~dir2[0,1] & (~m[0,1] & (~loc[0,1] & ~n2[0,1])))))
(board[] <-> board[0])
(board[0] <-> (board[0,0] | board[0,1]))
(dir1[] <-> dir1[0])
(dir1[0] <-> dir1[0,0])
(dir2[] <-> dir2[0])
(dir2[0] <-> dir2[0,1])
(end[] <-> end[0])
(end[0] <-> end[0,0])
(loc[] <-> loc[0])
(loc[0] <-> (loc[0,0] | loc[0,1]))
(m[] <-> m[0])
(m[0] <-> (m[0,0] | m[0,1]))
(n[] <-> n[0])
(n[0] <-> n[0,3])
1
-}

cluster = rget $ (procedure @'[ 'In, 'In, 'In, 'In, 'In, 'In, 'In ] clusterIIIIIII) :& (procedure @'[ 'In, 'In, 'In, 'In, 'In, 'In, 'Out ] clusterIIIIIIO) :& (procedure @'[ 'In, 'In, 'In, 'In, 'In, 'Out, 'In ] clusterIIIIIOI) :& (procedure @'[ 'In, 'In, 'In, 'In, 'In, 'Out, 'Out ] clusterIIIIIOO) :& RNil
  where
    clusterIIIIIII = \board m loc dir1 dir2 n end -> Logic.once $ do
      -- solution: n'[0,3] n1[0,2] n2[0,1]
      -- cost: 8
      () <- (do
        (OneTuple (n')) <- runProcedure @'[ 'Out, 'In ] succ n
        (n2,_) <- runProcedure @'[ 'In, 'In, 'In, 'In, 'Out, 'Out ] extendLocation board dir2 m loc
        (OneTuple (n1)) <- runProcedure @'[ 'Out, 'In, 'In ] plus n2 n'
        () <- runProcedure @'[ 'In, 'In, 'In, 'In, 'In, 'In ] extendLocation board dir1 m loc n1 end
        pure ()
       )
      pure ()
    
    clusterIIIIIIO = \board m loc dir1 dir2 n -> do
      -- solution: end[] end[0] end[0,0] n'[0,3] n1[0,2] n2[0,1]
      -- cost: 9
      (end) <- (do
        (OneTuple (n')) <- runProcedure @'[ 'Out, 'In ] succ n
        (n2,_) <- runProcedure @'[ 'In, 'In, 'In, 'In, 'Out, 'Out ] extendLocation board dir2 m loc
        (OneTuple (n1)) <- runProcedure @'[ 'Out, 'In, 'In ] plus n2 n'
        (OneTuple (end)) <- runProcedure @'[ 'In, 'In, 'In, 'In, 'In, 'Out ] extendLocation board dir1 m loc n1
        pure (end)
       )
      pure (OneTuple (end))
    
    clusterIIIIIOI = \board m loc dir1 dir2 end -> do
      -- solution: n[] n[0] n[0,3] n'[0,2] n1[0,0] n2[0,1]
      -- cost: 9
      (n) <- (do
        (OneTuple (n1)) <- runProcedure @'[ 'In, 'In, 'In, 'In, 'Out, 'In ] extendLocation board dir1 m loc end
        (n2,_) <- runProcedure @'[ 'In, 'In, 'In, 'In, 'Out, 'Out ] extendLocation board dir2 m loc
        (OneTuple (n')) <- runProcedure @'[ 'In, 'In, 'Out ] plus n1 n2
        (OneTuple (n)) <- runProcedure @'[ 'In, 'Out ] succ n'
        pure (n)
       )
      pure (OneTuple (n))
    
    clusterIIIIIOO = \board m loc dir1 dir2 -> do
      -- solution: end[] end[0] end[0,0] n[] n[0] n[0,3] n'[0,2] n1[0,0] n2[0,1]
      -- cost: 10
      (end,n) <- (do
        (n1,end) <- runProcedure @'[ 'In, 'In, 'In, 'In, 'Out, 'Out ] extendLocation board dir1 m loc
        (n2,_) <- runProcedure @'[ 'In, 'In, 'In, 'In, 'Out, 'Out ] extendLocation board dir2 m loc
        (OneTuple (n')) <- runProcedure @'[ 'In, 'In, 'Out ] plus n1 n2
        (OneTuple (n)) <- runProcedure @'[ 'In, 'Out ] succ n'
        pure (end,n)
       )
      pure (n,end)
    