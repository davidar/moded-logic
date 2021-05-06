{-# LANGUAGE DataKinds, FlexibleContexts, NoImplicitPrelude, NoMonomorphismRestriction, TypeApplications #-}
module Cannibals where

import qualified Control.Monad.Logic as Logic
import Control.Monad.Logic.Moded.Prelude

data State = State Int Int Int Int Int Int deriving (Eq, Ord, Read, Show)
data Action = MoveFwd Int Int | MoveBwd Int Int deriving (Eq, Ord, Read, Show)
data Search = Search State [ State ] [ Action ] deriving (Eq, Ord, Read, Show)
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
    
{- append/3
append arg1 arg2 arg3 :- ((arg1 = [], arg2 = b, arg3 = b); (arg1 = h0:t, h0 = h, arg3 = h1:tb, h1 = h, append t b tb, arg2 = b)).
constraints:
~append[1]
~(arg1[1,0] & h0[1,0])
~(arg2[0,1] & b[0,1])
~(arg2[1,5] & b[1,5])
~(arg3[0,2] & b[0,2])
~(arg3[1,2] & h1[1,2])
~(b[0,1] & b[0,2])
~(b[1,4] & b[1,5])
~(h[1,1] & h[1,3])
~(h0[1,0] & h0[1,1])
~(h0[1,1] & h[1,1])
~(h1[1,2] & h1[1,3])
~(h1[1,3] & h[1,3])
~(t[1,0] & t[1,4])
~(tb[1,2] & tb[1,4])
(b[0,1] | b[0,2])
(b[1,4] | b[1,5])
(h[1,1] | h[1,3])
(h0[1,0] | h0[1,1])
(h1[1,2] | h1[1,3])
(t[1,0] | t[1,4])
(tb[1,2] | tb[1,4])
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
(arg3[1] <-> arg3[1,2])
(b[1,4] <-> arg2[])
(h0[1,0] <-> t[1,0])
(h1[1,2] <-> tb[1,2])
(t[1,4] <-> arg1[])
(tb[1,4] <-> arg3[])
1
-}

append = rget $ (procedure @'[ 'In, 'In, 'In ] appendIII) :& (procedure @'[ 'In, 'In, 'Out ] appendIIO) :& (procedure @'[ 'In, 'Out, 'In ] appendIOI) :& (procedure @'[ 'Out, 'In, 'In ] appendOII) :& (procedure @'[ 'Out, 'Out, 'In ] appendOOI) :& RNil
  where
    appendIII = \arg1 arg2 arg3 -> Logic.once $ do
      -- solution: b[0,1] b[1,5] h[1,1] h0[1,0] h1[1,2] t[1,0] tb[1,2]
      -- cost: 1
      () <- (do
        b <- pure arg2
        guard $ arg3 == b
        guard $ arg1 == []
        pure ()
       ) <|> (do
        b <- pure arg2
        (h0:t) <- pure arg1
        h <- pure h0
        (h1:tb) <- pure arg3
        guard $ h1 == h
        () <- appendIII t b tb
        pure ()
       )
      pure ()
    
    appendIIO = \arg1 arg2 -> do
      -- solution: arg3[] arg3[0] arg3[0,2] arg3[1] arg3[1,2] b[0,1] b[1,5] h[1,1] h0[1,0] h1[1,3] t[1,0] tb[1,4]
      -- cost: 2
      (arg3) <- (do
        b <- pure arg2
        arg3 <- pure b
        guard $ arg1 == []
        pure (arg3)
       ) <|> (do
        b <- pure arg2
        (h0:t) <- pure arg1
        h <- pure h0
        h1 <- pure h
        (OneTuple (tb)) <- appendIIO t b
        arg3 <- pure (h1:tb)
        pure (arg3)
       )
      pure (OneTuple (arg3))
    
    appendIOI = \arg1 arg3 -> do
      -- solution: arg2[] arg2[0] arg2[0,1] arg2[1] arg2[1,5] b[0,2] b[1,4] h[1,1] h0[1,0] h1[1,2] t[1,0] tb[1,2]
      -- cost: 2
      (arg2) <- (do
        b <- pure arg3
        arg2 <- pure b
        guard $ arg1 == []
        pure (arg2)
       ) <|> (do
        (h0:t) <- pure arg1
        h <- pure h0
        (h1:tb) <- pure arg3
        guard $ h1 == h
        (OneTuple (b)) <- appendIOI t tb
        arg2 <- pure b
        pure (arg2)
       )
      pure (OneTuple (arg2))
    
    appendOII = \arg2 arg3 -> do
      -- solution: arg1[] arg1[0] arg1[0,0] arg1[1] arg1[1,0] b[0,1] b[1,5] h[1,3] h0[1,1] h1[1,2] t[1,4] tb[1,2]
      -- cost: 2
      (arg1) <- (do
        b <- pure arg2
        guard $ arg3 == b
        arg1 <- pure []
        pure (arg1)
       ) <|> (do
        b <- pure arg2
        (h1:tb) <- pure arg3
        h <- pure h1
        h0 <- pure h
        (OneTuple (t)) <- appendOII b tb
        arg1 <- pure (h0:t)
        pure (arg1)
       )
      pure (OneTuple (arg1))
    
    appendOOI = \arg3 -> do
      -- solution: arg1[] arg1[0] arg1[0,0] arg1[1] arg1[1,0] arg2[] arg2[0] arg2[0,1] arg2[1] arg2[1,5] b[0,2] b[1,4] h[1,3] h0[1,1] h1[1,2] t[1,4] tb[1,2]
      -- cost: 3
      (arg1,arg2) <- (do
        b <- pure arg3
        arg2 <- pure b
        arg1 <- pure []
        pure (arg1,arg2)
       ) <|> (do
        (h1:tb) <- pure arg3
        h <- pure h1
        h0 <- pure h
        (t,b) <- appendOOI tb
        arg2 <- pure b
        arg1 <- pure (h0:t)
        pure (arg1,arg2)
       )
      pure (arg1,arg2)
    
{- final/1
final arg1 :- ((arg1 = State data0 data1 _ _ _ _, data0 = 0, data1 = 0)).
constraints:
data0[0,0]
~(arg1[0,0] & data0[0,0])
~(data0[0,0] & data0[0,1])
~(data1[0,0] & data1[0,2])
(data0[0,0] | data0[0,1])
(data1[0,0] | data1[0,2])
(arg1[] <-> arg1[0])
(arg1[0] <-> arg1[0,0])
(data0[0,0] <-> data1[0,0])
1
-}

final = rget $ (procedure @'[ 'In ] finalI) :& RNil
  where
    finalI = \arg1 -> Logic.once $ do
      -- solution: data0[0,0] data1[0,0]
      -- cost: 0
      () <- (do
        (State data0 data1 _ _ _ _) <- pure arg1
        guard $ data0 == 0
        guard $ data1 == 0
        pure ()
       )
      pure ()
    
{- action/1
action arg1 :- ((arg1 = MoveFwd data0 data1, data0 = 1, data1 = 0); (arg1 = MoveFwd data2 data3, data2 = 0, data3 = 1); (arg1 = MoveFwd data4 data5, data4 = 2, data5 = 0); (arg1 = MoveFwd data6 data7, data6 = 0, data7 = 2); (arg1 = MoveFwd data8 data9, data8 = 1, data9 = 1); (arg1 = MoveBwd data10 data11, data10 = 1, data11 = 0); (arg1 = MoveBwd data12 data13, data12 = 0, data13 = 1); (arg1 = MoveBwd data14 data15, data14 = 2, data15 = 0); (arg1 = MoveBwd data16 data17, data16 = 0, data17 = 2); (arg1 = MoveBwd data18 data19, data18 = 1, data19 = 1)).
constraints:
~(arg1[0,0] & data0[0,0])
~(arg1[1,0] & data2[1,0])
~(arg1[2,0] & data4[2,0])
~(arg1[3,0] & data6[3,0])
~(arg1[4,0] & data8[4,0])
~(arg1[5,0] & data10[5,0])
~(arg1[6,0] & data12[6,0])
~(arg1[7,0] & data14[7,0])
~(arg1[8,0] & data16[8,0])
~(arg1[9,0] & data18[9,0])
~(data0[0,0] & data0[0,1])
~(data1[0,0] & data1[0,2])
~(data10[5,0] & data10[5,1])
~(data11[5,0] & data11[5,2])
~(data12[6,0] & data12[6,1])
~(data13[6,0] & data13[6,2])
~(data14[7,0] & data14[7,1])
~(data15[7,0] & data15[7,2])
~(data16[8,0] & data16[8,1])
~(data17[8,0] & data17[8,2])
~(data18[9,0] & data18[9,1])
~(data19[9,0] & data19[9,2])
~(data2[1,0] & data2[1,1])
~(data3[1,0] & data3[1,2])
~(data4[2,0] & data4[2,1])
~(data5[2,0] & data5[2,2])
~(data6[3,0] & data6[3,1])
~(data7[3,0] & data7[3,2])
~(data8[4,0] & data8[4,1])
~(data9[4,0] & data9[4,2])
(data0[0,0] | data0[0,1])
(data1[0,0] | data1[0,2])
(data10[5,0] | data10[5,1])
(data11[5,0] | data11[5,2])
(data12[6,0] | data12[6,1])
(data13[6,0] | data13[6,2])
(data14[7,0] | data14[7,1])
(data15[7,0] | data15[7,2])
(data16[8,0] | data16[8,1])
(data17[8,0] | data17[8,2])
(data18[9,0] | data18[9,1])
(data19[9,0] | data19[9,2])
(data2[1,0] | data2[1,1])
(data3[1,0] | data3[1,2])
(data4[2,0] | data4[2,1])
(data5[2,0] | data5[2,2])
(data6[3,0] | data6[3,1])
(data7[3,0] | data7[3,2])
(data8[4,0] | data8[4,1])
(data9[4,0] | data9[4,2])
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg1[] <-> arg1[2])
(arg1[] <-> arg1[3])
(arg1[] <-> arg1[4])
(arg1[] <-> arg1[5])
(arg1[] <-> arg1[6])
(arg1[] <-> arg1[7])
(arg1[] <-> arg1[8])
(arg1[] <-> arg1[9])
(arg1[0] <-> arg1[0,0])
(arg1[1] <-> arg1[1,0])
(arg1[2] <-> arg1[2,0])
(arg1[3] <-> arg1[3,0])
(arg1[4] <-> arg1[4,0])
(arg1[5] <-> arg1[5,0])
(arg1[6] <-> arg1[6,0])
(arg1[7] <-> arg1[7,0])
(arg1[8] <-> arg1[8,0])
(arg1[9] <-> arg1[9,0])
(data0[0,0] <-> data1[0,0])
(data10[5,0] <-> data11[5,0])
(data12[6,0] <-> data13[6,0])
(data14[7,0] <-> data15[7,0])
(data16[8,0] <-> data17[8,0])
(data18[9,0] <-> data19[9,0])
(data2[1,0] <-> data3[1,0])
(data4[2,0] <-> data5[2,0])
(data6[3,0] <-> data7[3,0])
(data8[4,0] <-> data9[4,0])
1
-}

action = rget $ (procedure @'[ 'In ] actionI) :& (procedure @'[ 'Out ] actionO) :& RNil
  where
    actionI = \arg1 -> Logic.once $ do
      -- solution: data0[0,0] data1[0,0] data10[5,0] data11[5,0] data12[6,0] data13[6,0] data14[7,0] data15[7,0] data16[8,0] data17[8,0] data18[9,0] data19[9,0] data2[1,0] data3[1,0] data4[2,0] data5[2,0] data6[3,0] data7[3,0] data8[4,0] data9[4,0]
      -- cost: 0
      () <- (do
        (MoveFwd data0 data1) <- pure arg1
        guard $ data1 == 0
        guard $ data0 == 1
        pure ()
       ) <|> (do
        (MoveFwd data2 data3) <- pure arg1
        guard $ data2 == 0
        guard $ data3 == 1
        pure ()
       ) <|> (do
        (MoveFwd data4 data5) <- pure arg1
        guard $ data5 == 0
        guard $ data4 == 2
        pure ()
       ) <|> (do
        (MoveFwd data6 data7) <- pure arg1
        guard $ data6 == 0
        guard $ data7 == 2
        pure ()
       ) <|> (do
        (MoveFwd data8 data9) <- pure arg1
        guard $ data8 == 1
        guard $ data9 == 1
        pure ()
       ) <|> (do
        (MoveBwd data10 data11) <- pure arg1
        guard $ data11 == 0
        guard $ data10 == 1
        pure ()
       ) <|> (do
        (MoveBwd data12 data13) <- pure arg1
        guard $ data12 == 0
        guard $ data13 == 1
        pure ()
       ) <|> (do
        (MoveBwd data14 data15) <- pure arg1
        guard $ data15 == 0
        guard $ data14 == 2
        pure ()
       ) <|> (do
        (MoveBwd data16 data17) <- pure arg1
        guard $ data16 == 0
        guard $ data17 == 2
        pure ()
       ) <|> (do
        (MoveBwd data18 data19) <- pure arg1
        guard $ data18 == 1
        guard $ data19 == 1
        pure ()
       )
      pure ()
    
    actionO = do
      -- solution: arg1[] arg1[0] arg1[0,0] arg1[1] arg1[1,0] arg1[2] arg1[2,0] arg1[3] arg1[3,0] arg1[4] arg1[4,0] arg1[5] arg1[5,0] arg1[6] arg1[6,0] arg1[7] arg1[7,0] arg1[8] arg1[8,0] arg1[9] arg1[9,0] data0[0,1] data1[0,2] data10[5,1] data11[5,2] data12[6,1] data13[6,2] data14[7,1] data15[7,2] data16[8,1] data17[8,2] data18[9,1] data19[9,2] data2[1,1] data3[1,2] data4[2,1] data5[2,2] data6[3,1] data7[3,2] data8[4,1] data9[4,2]
      -- cost: 0
      (arg1) <- (do
        data1 <- pure 0
        data0 <- pure 1
        arg1 <- pure (MoveFwd data0 data1)
        pure (arg1)
       ) <|> (do
        data2 <- pure 0
        data3 <- pure 1
        arg1 <- pure (MoveFwd data2 data3)
        pure (arg1)
       ) <|> (do
        data5 <- pure 0
        data4 <- pure 2
        arg1 <- pure (MoveFwd data4 data5)
        pure (arg1)
       ) <|> (do
        data6 <- pure 0
        data7 <- pure 2
        arg1 <- pure (MoveFwd data6 data7)
        pure (arg1)
       ) <|> (do
        data8 <- pure 1
        data9 <- pure 1
        arg1 <- pure (MoveFwd data8 data9)
        pure (arg1)
       ) <|> (do
        data11 <- pure 0
        data10 <- pure 1
        arg1 <- pure (MoveBwd data10 data11)
        pure (arg1)
       ) <|> (do
        data12 <- pure 0
        data13 <- pure 1
        arg1 <- pure (MoveBwd data12 data13)
        pure (arg1)
       ) <|> (do
        data15 <- pure 0
        data14 <- pure 2
        arg1 <- pure (MoveBwd data14 data15)
        pure (arg1)
       ) <|> (do
        data16 <- pure 0
        data17 <- pure 2
        arg1 <- pure (MoveBwd data16 data17)
        pure (arg1)
       ) <|> (do
        data18 <- pure 1
        data19 <- pure 1
        arg1 <- pure (MoveBwd data18 data19)
        pure (arg1)
       )
      pure (OneTuple (arg1))
    
{- check/1
check arg1 :- ((arg1 = State m1 c1 _ m2 c2 _, (>=) m1 data0, data0 = 0, (>=) m2 data1, data1 = 0, (>=) c1 data2, data2 = 0, (>=) c2 data3, data3 = 0, ((m1 = 0); ((<=) c1 m1)), ((m2 = 0); ((<=) c2 m2)))).
constraints:
m1[0,0]
~(<=)[0,9]
~(<=)[0,9,1]
~(<=)[0,10]
~(<=)[0,10,1]
~(>=)[0]
~c1[0,9]
~c2[0,10]
~((<=)[0,9] & (<=)[0,10])
~(arg1[0,0] & m1[0,0])
~(c1[0,0] & c1[0,5])
~(c1[0,0] & c1[0,9])
~(c1[0,5] & c1[0,9])
~(c2[0,0] & c2[0,7])
~(c2[0,0] & c2[0,10])
~(c2[0,7] & c2[0,10])
~(data0[0,1] & data0[0,2])
~(data1[0,3] & data1[0,4])
~(data2[0,5] & data2[0,6])
~(data3[0,7] & data3[0,8])
~(m1[0,0] & m1[0,1])
~(m1[0,0] & m1[0,9])
~(m1[0,1] & m1[0,9])
~(m2[0,0] & m2[0,3])
~(m2[0,0] & m2[0,10])
~(m2[0,3] & m2[0,10])
(~c1[0,5] & ~data2[0,5])
(~c1[0,9,1,0] & ~m1[0,9,1,0])
(~c2[0,7] & ~data3[0,7])
(~c2[0,10,1,0] & ~m2[0,10,1,0])
(~m1[0,1] & ~data0[0,1])
(~m2[0,3] & ~data1[0,3])
(c1[0,0] | (c1[0,5] | c1[0,9]))
(c2[0,0] | (c2[0,7] | c2[0,10]))
(data0[0,1] | data0[0,2])
(data1[0,3] | data1[0,4])
(data2[0,5] | data2[0,6])
(data3[0,7] | data3[0,8])
(m1[0,0] | (m1[0,1] | m1[0,9]))
(m2[0,0] | (m2[0,3] | m2[0,10]))
((<=)[0] <-> ((<=)[0,9] | (<=)[0,10]))
((<=)[0,9] <-> (<=)[0,9,1])
((<=)[0,10] <-> (<=)[0,10,1])
(arg1[] <-> arg1[0])
(arg1[0] <-> arg1[0,0])
(c1[0,9] <-> c1[0,9,1])
(c1[0,9,1] <-> c1[0,9,1,0])
(c2[0,10] <-> c2[0,10,1])
(c2[0,10,1] <-> c2[0,10,1,0])
(m1[0,0] <-> c1[0,0])
(m1[0,0] <-> c2[0,0])
(m1[0,0] <-> m2[0,0])
(m1[0,9] <-> m1[0,9,0])
(m1[0,9] <-> m1[0,9,1])
(m1[0,9,0] <-> m1[0,9,0,0])
(m1[0,9,1] <-> m1[0,9,1,0])
(m2[0,10] <-> m2[0,10,0])
(m2[0,10] <-> m2[0,10,1])
(m2[0,10,0] <-> m2[0,10,0,0])
(m2[0,10,1] <-> m2[0,10,1,0])
1
-}

check = rget $ (procedure @'[ 'In ] checkI) :& RNil
  where
    checkI = \arg1 -> Logic.once $ do
      -- solution: c1[0,0] c2[0,0] data0[0,2] data1[0,4] data2[0,6] data3[0,8] m1[0,0] m2[0,0]
      -- cost: 6
      () <- (do
        data0 <- pure 0
        data1 <- pure 0
        data2 <- pure 0
        data3 <- pure 0
        (State m1 c1 _ m2 c2 _) <- pure arg1
        guard $ (>=) c1 data2
        guard $ (>=) c2 data3
        guard $ (>=) m1 data0
        guard $ (>=) m2 data1
        () <- (do
          guard $ m1 == 0
          pure ()
         ) <|> (do
          guard $ (<=) c1 m1
          pure ()
         )
        () <- (do
          guard $ m2 == 0
          pure ()
         ) <|> (do
          guard $ (<=) c2 m2
          pure ()
         )
        pure ()
       )
      pure ()
    
{- move/3
move arg1 arg2 arg3 :- ((arg1 = State m1 c1 b1 m2 c2 b2, arg2 = MoveFwd mm cm, (>) b1 data0, data0 = 0, plus mm m1' m1, plus cm c1' c1, succ b1' b1, plus mm m2 m2', plus cm c2 c2', succ b2 b2', s = State m1' c1' b1' m2' c2' b2', check s, arg3 = s); (arg1 = State m1 c1 b1 m2 c2 b2, arg2 = MoveBwd mm cm, (>) b2 data1, data1 = 0, plus mm m1 m1', plus cm c1 c1', succ b1 b1', plus mm m2' m2, plus cm c2' c2, succ b2' b2, s = State m1' c1' b1' m2' c2' b2', check s, arg3 = s)).
constraints:
~(>)[0]
~(>)[1]
~check[0]
~check[1]
~plus[0]
~plus[1]
~s[0,11]
~s[1,11]
~succ[0]
~succ[1]
~(arg1[0,0] & m1[0,0])
~(arg1[1,0] & m1[1,0])
~(arg2[0,1] & mm[0,1])
~(arg2[1,1] & mm[1,1])
~(arg3[0,12] & s[0,12])
~(arg3[1,12] & s[1,12])
~(b1[0,0] & b1[0,2])
~(b1[0,0] & b1[0,6])
~(b1[0,2] & b1[0,6])
~(b1[1,0] & b1[1,6])
~(b1'[0,6] & b1'[0,10])
~(b1'[1,6] & b1'[1,10])
~(b2[0,0] & b2[0,9])
~(b2[1,0] & b2[1,2])
~(b2[1,0] & b2[1,9])
~(b2[1,2] & b2[1,9])
~(b2'[0,9] & b2'[0,10])
~(b2'[1,9] & b2'[1,10])
~(c1[0,0] & c1[0,5])
~(c1[1,0] & c1[1,5])
~(c1'[0,5] & c1'[0,10])
~(c1'[1,5] & c1'[1,10])
~(c2[0,0] & c2[0,8])
~(c2[1,0] & c2[1,8])
~(c2'[0,8] & c2'[0,10])
~(c2'[1,8] & c2'[1,10])
~(cm[0,1] & cm[0,5])
~(cm[0,1] & cm[0,8])
~(cm[0,5] & cm[0,8])
~(cm[1,1] & cm[1,5])
~(cm[1,1] & cm[1,8])
~(cm[1,5] & cm[1,8])
~(data0[0,2] & data0[0,3])
~(data1[1,2] & data1[1,3])
~(m1[0,0] & m1[0,4])
~(m1[1,0] & m1[1,4])
~(m1'[0,4] & m1'[0,10])
~(m1'[1,4] & m1'[1,10])
~(m2[0,0] & m2[0,7])
~(m2[1,0] & m2[1,7])
~(m2'[0,7] & m2'[0,10])
~(m2'[1,7] & m2'[1,10])
~(mm[0,1] & mm[0,4])
~(mm[0,1] & mm[0,7])
~(mm[0,4] & mm[0,7])
~(mm[1,1] & mm[1,4])
~(mm[1,1] & mm[1,7])
~(mm[1,4] & mm[1,7])
~(s[0,10] & m1'[0,10])
~(s[0,10] & s[0,11])
~(s[0,10] & s[0,12])
~(s[0,11] & s[0,12])
~(s[1,10] & m1'[1,10])
~(s[1,10] & s[1,11])
~(s[1,10] & s[1,12])
~(s[1,11] & s[1,12])
(~b1[0,2] & ~data0[0,2])
(~b2[1,2] & ~data1[1,2])
(b1[0,0] | (b1[0,2] | b1[0,6]))
(b1[1,0] | b1[1,6])
(b1'[0,6] | b1'[0,10])
(b1'[1,6] | b1'[1,10])
(b2[0,0] | b2[0,9])
(b2[1,0] | (b2[1,2] | b2[1,9]))
(b2'[0,9] | b2'[0,10])
(b2'[1,9] | b2'[1,10])
(c1[0,0] | c1[0,5])
(c1[1,0] | c1[1,5])
(c1'[0,5] | c1'[0,10])
(c1'[1,5] | c1'[1,10])
(c2[0,0] | c2[0,8])
(c2[1,0] | c2[1,8])
(c2'[0,8] | c2'[0,10])
(c2'[1,8] | c2'[1,10])
(cm[0,1] | (cm[0,5] | cm[0,8]))
(cm[1,1] | (cm[1,5] | cm[1,8]))
(data0[0,2] | data0[0,3])
(data1[1,2] | data1[1,3])
(m1[0,0] | m1[0,4])
(m1[1,0] | m1[1,4])
(m1'[0,4] | m1'[0,10])
(m1'[1,4] | m1'[1,10])
(m2[0,0] | m2[0,7])
(m2[1,0] | m2[1,7])
(m2'[0,7] | m2'[0,10])
(m2'[1,7] | m2'[1,10])
(mm[0,1] | (mm[0,4] | mm[0,7]))
(mm[1,1] | (mm[1,4] | mm[1,7]))
(s[0,10] | (s[0,11] | s[0,12]))
(s[1,10] | (s[1,11] | s[1,12]))
((b1[1,6] & ~b1'[1,6]) | ((~b1[1,6] & b1'[1,6]) | (~b1[1,6] & ~b1'[1,6])))
((b1'[0,6] & ~b1[0,6]) | ((~b1'[0,6] & b1[0,6]) | (~b1'[0,6] & ~b1[0,6])))
((b2[0,9] & ~b2'[0,9]) | ((~b2[0,9] & b2'[0,9]) | (~b2[0,9] & ~b2'[0,9])))
((b2'[1,9] & ~b2[1,9]) | ((~b2'[1,9] & b2[1,9]) | (~b2'[1,9] & ~b2[1,9])))
((cm[0,5] & (~c1'[0,5] & ~c1[0,5])) | ((~cm[0,5] & (c1'[0,5] & ~c1[0,5])) | ((~cm[0,5] & (~c1'[0,5] & c1[0,5])) | (~cm[0,5] & (~c1'[0,5] & ~c1[0,5])))))
((cm[0,8] & (~c2[0,8] & ~c2'[0,8])) | ((~cm[0,8] & (c2[0,8] & ~c2'[0,8])) | ((~cm[0,8] & (~c2[0,8] & c2'[0,8])) | (~cm[0,8] & (~c2[0,8] & ~c2'[0,8])))))
((cm[1,5] & (~c1[1,5] & ~c1'[1,5])) | ((~cm[1,5] & (c1[1,5] & ~c1'[1,5])) | ((~cm[1,5] & (~c1[1,5] & c1'[1,5])) | (~cm[1,5] & (~c1[1,5] & ~c1'[1,5])))))
((cm[1,8] & (~c2'[1,8] & ~c2[1,8])) | ((~cm[1,8] & (c2'[1,8] & ~c2[1,8])) | ((~cm[1,8] & (~c2'[1,8] & c2[1,8])) | (~cm[1,8] & (~c2'[1,8] & ~c2[1,8])))))
((mm[0,4] & (~m1'[0,4] & ~m1[0,4])) | ((~mm[0,4] & (m1'[0,4] & ~m1[0,4])) | ((~mm[0,4] & (~m1'[0,4] & m1[0,4])) | (~mm[0,4] & (~m1'[0,4] & ~m1[0,4])))))
((mm[0,7] & (~m2[0,7] & ~m2'[0,7])) | ((~mm[0,7] & (m2[0,7] & ~m2'[0,7])) | ((~mm[0,7] & (~m2[0,7] & m2'[0,7])) | (~mm[0,7] & (~m2[0,7] & ~m2'[0,7])))))
((mm[1,4] & (~m1[1,4] & ~m1'[1,4])) | ((~mm[1,4] & (m1[1,4] & ~m1'[1,4])) | ((~mm[1,4] & (~m1[1,4] & m1'[1,4])) | (~mm[1,4] & (~m1[1,4] & ~m1'[1,4])))))
((mm[1,7] & (~m2'[1,7] & ~m2[1,7])) | ((~mm[1,7] & (m2'[1,7] & ~m2[1,7])) | ((~mm[1,7] & (~m2'[1,7] & m2[1,7])) | (~mm[1,7] & (~m2'[1,7] & ~m2[1,7])))))
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg1[0] <-> arg1[0,0])
(arg1[1] <-> arg1[1,0])
(arg2[] <-> arg2[0])
(arg2[] <-> arg2[1])
(arg2[0] <-> arg2[0,1])
(arg2[1] <-> arg2[1,1])
(arg3[] <-> arg3[0])
(arg3[] <-> arg3[1])
(arg3[0] <-> arg3[0,12])
(arg3[1] <-> arg3[1,12])
(m1[0,0] <-> b1[0,0])
(m1[0,0] <-> b2[0,0])
(m1[0,0] <-> c1[0,0])
(m1[0,0] <-> c2[0,0])
(m1[0,0] <-> m2[0,0])
(m1[1,0] <-> b1[1,0])
(m1[1,0] <-> b2[1,0])
(m1[1,0] <-> c1[1,0])
(m1[1,0] <-> c2[1,0])
(m1[1,0] <-> m2[1,0])
(m1'[0,10] <-> b1'[0,10])
(m1'[0,10] <-> b2'[0,10])
(m1'[0,10] <-> c1'[0,10])
(m1'[0,10] <-> c2'[0,10])
(m1'[0,10] <-> m2'[0,10])
(m1'[1,10] <-> b1'[1,10])
(m1'[1,10] <-> b2'[1,10])
(m1'[1,10] <-> c1'[1,10])
(m1'[1,10] <-> c2'[1,10])
(m1'[1,10] <-> m2'[1,10])
(mm[0,1] <-> cm[0,1])
(mm[1,1] <-> cm[1,1])
1
-}

move = rget $ (procedure @'[ 'In, 'In, 'In ] moveIII) :& (procedure @'[ 'In, 'In, 'Out ] moveIIO) :& (procedure @'[ 'In, 'Out, 'In ] moveIOI) :& (procedure @'[ 'Out, 'In, 'In ] moveOII) :& RNil
  where
    moveIII = \arg1 arg2 arg3 -> Logic.once $ do
      -- solution: b1[0,0] b1[1,0] b1'[0,10] b1'[1,10] b2[0,0] b2[1,0] b2'[0,10] b2'[1,10] c1[0,0] c1[1,0] c1'[0,10] c1'[1,10] c2[0,0] c2[1,0] c2'[0,10] c2'[1,10] cm[0,1] cm[1,1] data0[0,3] data1[1,3] m1[0,0] m1[1,0] m1'[0,10] m1'[1,10] m2[0,0] m2[1,0] m2'[0,10] m2'[1,10] mm[0,1] mm[1,1] s[0,12] s[1,12]
      -- cost: 16
      () <- (do
        s <- pure arg3
        data0 <- pure 0
        (MoveFwd mm cm) <- pure arg2
        (State m1 c1 b1 m2 c2 b2) <- pure arg1
        (State m1' c1' b1' m2' c2' b2') <- pure s
        guard $ (>) b1 data0
        () <- runProcedure @'[ 'In ] check s
        () <- runProcedure @'[ 'In, 'In, 'In ] plus cm c1' c1
        () <- runProcedure @'[ 'In, 'In, 'In ] plus cm c2 c2'
        () <- runProcedure @'[ 'In, 'In, 'In ] plus mm m1' m1
        () <- runProcedure @'[ 'In, 'In, 'In ] plus mm m2 m2'
        () <- runProcedure @'[ 'In, 'In ] succ b1' b1
        () <- runProcedure @'[ 'In, 'In ] succ b2 b2'
        pure ()
       ) <|> (do
        s <- pure arg3
        data1 <- pure 0
        (MoveBwd mm cm) <- pure arg2
        (State m1 c1 b1 m2 c2 b2) <- pure arg1
        (State m1' c1' b1' m2' c2' b2') <- pure s
        guard $ (>) b2 data1
        () <- runProcedure @'[ 'In ] check s
        () <- runProcedure @'[ 'In, 'In, 'In ] plus cm c1 c1'
        () <- runProcedure @'[ 'In, 'In, 'In ] plus cm c2' c2
        () <- runProcedure @'[ 'In, 'In, 'In ] plus mm m1 m1'
        () <- runProcedure @'[ 'In, 'In, 'In ] plus mm m2' m2
        () <- runProcedure @'[ 'In, 'In ] succ b1 b1'
        () <- runProcedure @'[ 'In, 'In ] succ b2' b2
        pure ()
       )
      pure ()
    
    moveIIO = \arg1 arg2 -> do
      -- solution: arg3[] arg3[0] arg3[0,12] arg3[1] arg3[1,12] b1[0,0] b1[1,0] b1'[0,6] b1'[1,6] b2[0,0] b2[1,0] b2'[0,9] b2'[1,9] c1[0,0] c1[1,0] c1'[0,5] c1'[1,5] c2[0,0] c2[1,0] c2'[0,8] c2'[1,8] cm[0,1] cm[1,1] data0[0,3] data1[1,3] m1[0,0] m1[1,0] m1'[0,4] m1'[1,4] m2[0,0] m2[1,0] m2'[0,7] m2'[1,7] mm[0,1] mm[1,1] s[0,10] s[1,10]
      -- cost: 28
      (arg3) <- (do
        data0 <- pure 0
        (MoveFwd mm cm) <- pure arg2
        (State m1 c1 b1 m2 c2 b2) <- pure arg1
        guard $ (>) b1 data0
        (OneTuple (c1')) <- runProcedure @'[ 'In, 'Out, 'In ] plus cm c1
        (OneTuple (c2')) <- runProcedure @'[ 'In, 'In, 'Out ] plus cm c2
        (OneTuple (m1')) <- runProcedure @'[ 'In, 'Out, 'In ] plus mm m1
        (OneTuple (m2')) <- runProcedure @'[ 'In, 'In, 'Out ] plus mm m2
        (OneTuple (b1')) <- runProcedure @'[ 'Out, 'In ] succ b1
        (OneTuple (b2')) <- runProcedure @'[ 'In, 'Out ] succ b2
        s <- pure (State m1' c1' b1' m2' c2' b2')
        arg3 <- pure s
        () <- runProcedure @'[ 'In ] check s
        pure (arg3)
       ) <|> (do
        data1 <- pure 0
        (MoveBwd mm cm) <- pure arg2
        (State m1 c1 b1 m2 c2 b2) <- pure arg1
        guard $ (>) b2 data1
        (OneTuple (c1')) <- runProcedure @'[ 'In, 'In, 'Out ] plus cm c1
        (OneTuple (c2')) <- runProcedure @'[ 'In, 'Out, 'In ] plus cm c2
        (OneTuple (m1')) <- runProcedure @'[ 'In, 'In, 'Out ] plus mm m1
        (OneTuple (m2')) <- runProcedure @'[ 'In, 'Out, 'In ] plus mm m2
        (OneTuple (b1')) <- runProcedure @'[ 'In, 'Out ] succ b1
        (OneTuple (b2')) <- runProcedure @'[ 'Out, 'In ] succ b2
        s <- pure (State m1' c1' b1' m2' c2' b2')
        arg3 <- pure s
        () <- runProcedure @'[ 'In ] check s
        pure (arg3)
       )
      pure (OneTuple (arg3))
    
    moveIOI = \arg1 arg3 -> do
      -- solution: arg2[] arg2[0] arg2[0,1] arg2[1] arg2[1,1] b1[0,0] b1[1,0] b1'[0,10] b1'[1,10] b2[0,0] b2[1,0] b2'[0,10] b2'[1,10] c1[0,0] c1[1,0] c1'[0,10] c1'[1,10] c2[0,0] c2[1,0] c2'[0,10] c2'[1,10] cm[0,5] cm[1,5] data0[0,3] data1[1,3] m1[0,0] m1[1,0] m1'[0,10] m1'[1,10] m2[0,0] m2[1,0] m2'[0,10] m2'[1,10] mm[0,4] mm[1,4] s[0,12] s[1,12]
      -- cost: 20
      (arg2) <- (do
        s <- pure arg3
        data0 <- pure 0
        (State m1 c1 b1 m2 c2 b2) <- pure arg1
        (State m1' c1' b1' m2' c2' b2') <- pure s
        guard $ (>) b1 data0
        () <- runProcedure @'[ 'In ] check s
        () <- runProcedure @'[ 'In, 'In ] succ b1' b1
        () <- runProcedure @'[ 'In, 'In ] succ b2 b2'
        (OneTuple (cm)) <- runProcedure @'[ 'Out, 'In, 'In ] plus c1' c1
        () <- runProcedure @'[ 'In, 'In, 'In ] plus cm c2 c2'
        (OneTuple (mm)) <- runProcedure @'[ 'Out, 'In, 'In ] plus m1' m1
        arg2 <- pure (MoveFwd mm cm)
        () <- runProcedure @'[ 'In, 'In, 'In ] plus mm m2 m2'
        pure (arg2)
       ) <|> (do
        s <- pure arg3
        data1 <- pure 0
        (State m1 c1 b1 m2 c2 b2) <- pure arg1
        (State m1' c1' b1' m2' c2' b2') <- pure s
        guard $ (>) b2 data1
        () <- runProcedure @'[ 'In ] check s
        () <- runProcedure @'[ 'In, 'In ] succ b1 b1'
        () <- runProcedure @'[ 'In, 'In ] succ b2' b2
        (OneTuple (cm)) <- runProcedure @'[ 'Out, 'In, 'In ] plus c1 c1'
        () <- runProcedure @'[ 'In, 'In, 'In ] plus cm c2' c2
        (OneTuple (mm)) <- runProcedure @'[ 'Out, 'In, 'In ] plus m1 m1'
        arg2 <- pure (MoveBwd mm cm)
        () <- runProcedure @'[ 'In, 'In, 'In ] plus mm m2' m2
        pure (arg2)
       )
      pure (OneTuple (arg2))
    
    moveOII = \arg2 arg3 -> do
      -- solution: arg1[] arg1[0] arg1[0,0] arg1[1] arg1[1,0] b1[0,6] b1[1,6] b1'[0,10] b1'[1,10] b2[0,9] b2[1,9] b2'[0,10] b2'[1,10] c1[0,5] c1[1,5] c1'[0,10] c1'[1,10] c2[0,8] c2[1,8] c2'[0,10] c2'[1,10] cm[0,1] cm[1,1] data0[0,3] data1[1,3] m1[0,4] m1[1,4] m1'[0,10] m1'[1,10] m2[0,7] m2[1,7] m2'[0,10] m2'[1,10] mm[0,1] mm[1,1] s[0,12] s[1,12]
      -- cost: 28
      (arg1) <- (do
        s <- pure arg3
        data0 <- pure 0
        (MoveFwd mm cm) <- pure arg2
        (State m1' c1' b1' m2' c2' b2') <- pure s
        () <- runProcedure @'[ 'In ] check s
        (OneTuple (c1)) <- runProcedure @'[ 'In, 'In, 'Out ] plus cm c1'
        (OneTuple (c2)) <- runProcedure @'[ 'In, 'Out, 'In ] plus cm c2'
        (OneTuple (m1)) <- runProcedure @'[ 'In, 'In, 'Out ] plus mm m1'
        (OneTuple (m2)) <- runProcedure @'[ 'In, 'Out, 'In ] plus mm m2'
        (OneTuple (b1)) <- runProcedure @'[ 'In, 'Out ] succ b1'
        guard $ (>) b1 data0
        (OneTuple (b2)) <- runProcedure @'[ 'Out, 'In ] succ b2'
        arg1 <- pure (State m1 c1 b1 m2 c2 b2)
        pure (arg1)
       ) <|> (do
        s <- pure arg3
        data1 <- pure 0
        (MoveBwd mm cm) <- pure arg2
        (State m1' c1' b1' m2' c2' b2') <- pure s
        () <- runProcedure @'[ 'In ] check s
        (OneTuple (c1)) <- runProcedure @'[ 'In, 'Out, 'In ] plus cm c1'
        (OneTuple (c2)) <- runProcedure @'[ 'In, 'In, 'Out ] plus cm c2'
        (OneTuple (m1)) <- runProcedure @'[ 'In, 'Out, 'In ] plus mm m1'
        (OneTuple (m2)) <- runProcedure @'[ 'In, 'In, 'Out ] plus mm m2'
        (OneTuple (b1)) <- runProcedure @'[ 'Out, 'In ] succ b1'
        (OneTuple (b2)) <- runProcedure @'[ 'In, 'Out ] succ b2'
        arg1 <- pure (State m1 c1 b1 m2 c2 b2)
        guard $ (>) b2 data1
        pure (arg1)
       )
      pure (OneTuple (arg1))
    
{- appendShow/3
appendShow x carg2 carg3 :- ((append s carg2 carg3, show x s)).
constraints:
~append[0]
~show[0]
~(s[0,0] & s[0,1])
(s[0,0] | s[0,1])
((s[0,0] & (carg2[0,0] & ~carg3[0,0])) | ((s[0,0] & (~carg2[0,0] & ~carg3[0,0])) | ((~s[0,0] & (carg2[0,0] & ~carg3[0,0])) | ((~s[0,0] & (~carg2[0,0] & carg3[0,0])) | (~s[0,0] & (~carg2[0,0] & ~carg3[0,0]))))))
((x[0,1] & ~s[0,1]) | ((~x[0,1] & s[0,1]) | (~x[0,1] & ~s[0,1])))
(carg2[] <-> carg2[0])
(carg2[0] <-> carg2[0,0])
(carg3[] <-> carg3[0])
(carg3[0] <-> carg3[0,0])
(x[] <-> x[0])
(x[0] <-> x[0,1])
1
-}

appendShow = rget $ (procedure @'[ 'In, 'In, 'In ] appendShowIII) :& (procedure @'[ 'In, 'In, 'Out ] appendShowIIO) :& (procedure @'[ 'In, 'Out, 'In ] appendShowIOI) :& (procedure @'[ 'Out, 'In, 'In ] appendShowOII) :& (procedure @'[ 'Out, 'Out, 'In ] appendShowOOI) :& RNil
  where
    appendShowIII = \x carg2 carg3 -> Logic.once $ do
      -- solution: s[0,0]
      -- cost: 3
      () <- (do
        (OneTuple (s)) <- runProcedure @'[ 'Out, 'In, 'In ] append carg2 carg3
        () <- runProcedure @'[ 'In, 'In ] show x s
        pure ()
       )
      pure ()
    
    appendShowIIO = \x carg2 -> do
      -- solution: carg3[] carg3[0] carg3[0,0] s[0,1]
      -- cost: 4
      (carg3) <- (do
        (OneTuple (s)) <- runProcedure @'[ 'In, 'Out ] show x
        (OneTuple (carg3)) <- runProcedure @'[ 'In, 'In, 'Out ] append s carg2
        pure (carg3)
       )
      pure (OneTuple (carg3))
    
    appendShowIOI = \x carg3 -> do
      -- solution: carg2[] carg2[0] carg2[0,0] s[0,0]
      -- cost: 4
      (carg2) <- (do
        (s,carg2) <- runProcedure @'[ 'Out, 'Out, 'In ] append carg3
        () <- runProcedure @'[ 'In, 'In ] show x s
        pure (carg2)
       )
      pure (OneTuple (carg2))
    
    appendShowOII = \carg2 carg3 -> do
      -- solution: s[0,0] x[] x[0] x[0,1]
      -- cost: 4
      (x) <- (do
        (OneTuple (s)) <- runProcedure @'[ 'Out, 'In, 'In ] append carg2 carg3
        (OneTuple (x)) <- runProcedure @'[ 'Out, 'In ] show s
        pure (x)
       )
      pure (OneTuple (x))
    
    appendShowOOI = \carg3 -> do
      -- solution: carg2[] carg2[0] carg2[0,0] s[0,0] x[] x[0] x[0,1]
      -- cost: 5
      (carg2,x) <- (do
        (s,carg2) <- runProcedure @'[ 'Out, 'Out, 'In ] append carg3
        (OneTuple (x)) <- runProcedure @'[ 'Out, 'In ] show s
        pure (carg2,x)
       )
      pure (x,carg2)
    
{- showMove/5
showMove c a s carg3 carg4 :- ((appendShow s carg3 b_12, append data6_1_4_7_10_14 b_12 b_9, data6_1_4_7_10_14 = "-> ", appendShow a b_9 b_6, append data3_1_4_8 b_6 b_3, data3_1_4_8 = " -", appendShow c b_3 b_0, append data0_2 b_0 carg4, data0_2 = "Tentative move: ")).
constraints:
~append[0]
~appendShow[0]
~(b_0[0,6] & b_0[0,7])
~(b_12[0,0] & b_12[0,1])
~(b_3[0,4] & b_3[0,6])
~(b_6[0,3] & b_6[0,4])
~(b_9[0,1] & b_9[0,3])
~(data0_2[0,7] & data0_2[0,8])
~(data3_1_4_8[0,4] & data3_1_4_8[0,5])
~(data6_1_4_7_10_14[0,1] & data6_1_4_7_10_14[0,2])
(b_0[0,6] | b_0[0,7])
(b_12[0,0] | b_12[0,1])
(b_3[0,4] | b_3[0,6])
(b_6[0,3] | b_6[0,4])
(b_9[0,1] | b_9[0,3])
(data0_2[0,7] | data0_2[0,8])
(data3_1_4_8[0,4] | data3_1_4_8[0,5])
(data6_1_4_7_10_14[0,1] | data6_1_4_7_10_14[0,2])
((a[0,3] & (b_9[0,3] & ~b_6[0,3])) | ((a[0,3] & (~b_9[0,3] & ~b_6[0,3])) | ((~a[0,3] & (b_9[0,3] & ~b_6[0,3])) | ((~a[0,3] & (~b_9[0,3] & b_6[0,3])) | (~a[0,3] & (~b_9[0,3] & ~b_6[0,3]))))))
((c[0,6] & (b_3[0,6] & ~b_0[0,6])) | ((c[0,6] & (~b_3[0,6] & ~b_0[0,6])) | ((~c[0,6] & (b_3[0,6] & ~b_0[0,6])) | ((~c[0,6] & (~b_3[0,6] & b_0[0,6])) | (~c[0,6] & (~b_3[0,6] & ~b_0[0,6]))))))
((data0_2[0,7] & (b_0[0,7] & ~carg4[0,7])) | ((data0_2[0,7] & (~b_0[0,7] & ~carg4[0,7])) | ((~data0_2[0,7] & (b_0[0,7] & ~carg4[0,7])) | ((~data0_2[0,7] & (~b_0[0,7] & carg4[0,7])) | (~data0_2[0,7] & (~b_0[0,7] & ~carg4[0,7]))))))
((data3_1_4_8[0,4] & (b_6[0,4] & ~b_3[0,4])) | ((data3_1_4_8[0,4] & (~b_6[0,4] & ~b_3[0,4])) | ((~data3_1_4_8[0,4] & (b_6[0,4] & ~b_3[0,4])) | ((~data3_1_4_8[0,4] & (~b_6[0,4] & b_3[0,4])) | (~data3_1_4_8[0,4] & (~b_6[0,4] & ~b_3[0,4]))))))
((data6_1_4_7_10_14[0,1] & (b_12[0,1] & ~b_9[0,1])) | ((data6_1_4_7_10_14[0,1] & (~b_12[0,1] & ~b_9[0,1])) | ((~data6_1_4_7_10_14[0,1] & (b_12[0,1] & ~b_9[0,1])) | ((~data6_1_4_7_10_14[0,1] & (~b_12[0,1] & b_9[0,1])) | (~data6_1_4_7_10_14[0,1] & (~b_12[0,1] & ~b_9[0,1]))))))
((s[0,0] & (carg3[0,0] & ~b_12[0,0])) | ((s[0,0] & (~carg3[0,0] & ~b_12[0,0])) | ((~s[0,0] & (carg3[0,0] & ~b_12[0,0])) | ((~s[0,0] & (~carg3[0,0] & b_12[0,0])) | (~s[0,0] & (~carg3[0,0] & ~b_12[0,0]))))))
(a[] <-> a[0])
(a[0] <-> a[0,3])
(c[] <-> c[0])
(c[0] <-> c[0,6])
(carg3[] <-> carg3[0])
(carg3[0] <-> carg3[0,0])
(carg4[] <-> carg4[0])
(carg4[0] <-> carg4[0,7])
(s[] <-> s[0])
(s[0] <-> s[0,0])
1
-}

showMove = rget $ (procedure @'[ 'In, 'In, 'In, 'In, 'In ] showMoveIIIII) :& (procedure @'[ 'In, 'In, 'In, 'In, 'Out ] showMoveIIIIO) :& (procedure @'[ 'In, 'In, 'In, 'Out, 'In ] showMoveIIIOI) :& (procedure @'[ 'In, 'In, 'Out, 'In, 'In ] showMoveIIOII) :& (procedure @'[ 'In, 'In, 'Out, 'Out, 'In ] showMoveIIOOI) :& (procedure @'[ 'In, 'Out, 'In, 'In, 'In ] showMoveIOIII) :& (procedure @'[ 'In, 'Out, 'In, 'Out, 'In ] showMoveIOIOI) :& (procedure @'[ 'In, 'Out, 'Out, 'In, 'In ] showMoveIOOII) :& (procedure @'[ 'In, 'Out, 'Out, 'Out, 'In ] showMoveIOOOI) :& (procedure @'[ 'Out, 'In, 'In, 'In, 'In ] showMoveOIIII) :& (procedure @'[ 'Out, 'In, 'In, 'Out, 'In ] showMoveOIIOI) :& (procedure @'[ 'Out, 'In, 'Out, 'In, 'In ] showMoveOIOII) :& (procedure @'[ 'Out, 'In, 'Out, 'Out, 'In ] showMoveOIOOI) :& (procedure @'[ 'Out, 'Out, 'In, 'In, 'In ] showMoveOOIII) :& (procedure @'[ 'Out, 'Out, 'In, 'Out, 'In ] showMoveOOIOI) :& (procedure @'[ 'Out, 'Out, 'Out, 'In, 'In ] showMoveOOOII) :& (procedure @'[ 'Out, 'Out, 'Out, 'Out, 'In ] showMoveOOOOI) :& RNil
  where
    showMoveIIIII = \c a s carg3 carg4 -> Logic.once $ do
      -- solution: b_0[0,6] b_12[0,0] b_3[0,4] b_6[0,3] b_9[0,1] data0_2[0,8] data3_1_4_8[0,5] data6_1_4_7_10_14[0,2]
      -- cost: 11
      () <- (do
        data3_1_4_8 <- pure " -"
        data6_1_4_7_10_14 <- pure "-> "
        data0_2 <- pure "Tentative move: "
        (OneTuple (b_12)) <- runProcedure @'[ 'In, 'In, 'Out ] appendShow s carg3
        (OneTuple (b_9)) <- runProcedure @'[ 'In, 'In, 'Out ] append data6_1_4_7_10_14 b_12
        (OneTuple (b_6)) <- runProcedure @'[ 'In, 'In, 'Out ] appendShow a b_9
        (OneTuple (b_3)) <- runProcedure @'[ 'In, 'In, 'Out ] append data3_1_4_8 b_6
        (OneTuple (b_0)) <- runProcedure @'[ 'In, 'In, 'Out ] appendShow c b_3
        () <- runProcedure @'[ 'In, 'In, 'In ] append data0_2 b_0 carg4
        pure ()
       )
      pure ()
    
    showMoveIIIIO = \c a s carg3 -> do
      -- solution: b_0[0,6] b_12[0,0] b_3[0,4] b_6[0,3] b_9[0,1] carg4[] carg4[0] carg4[0,7] data0_2[0,8] data3_1_4_8[0,5] data6_1_4_7_10_14[0,2]
      -- cost: 12
      (carg4) <- (do
        data3_1_4_8 <- pure " -"
        data6_1_4_7_10_14 <- pure "-> "
        data0_2 <- pure "Tentative move: "
        (OneTuple (b_12)) <- runProcedure @'[ 'In, 'In, 'Out ] appendShow s carg3
        (OneTuple (b_9)) <- runProcedure @'[ 'In, 'In, 'Out ] append data6_1_4_7_10_14 b_12
        (OneTuple (b_6)) <- runProcedure @'[ 'In, 'In, 'Out ] appendShow a b_9
        (OneTuple (b_3)) <- runProcedure @'[ 'In, 'In, 'Out ] append data3_1_4_8 b_6
        (OneTuple (b_0)) <- runProcedure @'[ 'In, 'In, 'Out ] appendShow c b_3
        (OneTuple (carg4)) <- runProcedure @'[ 'In, 'In, 'Out ] append data0_2 b_0
        pure (carg4)
       )
      pure (OneTuple (carg4))
    
    showMoveIIIOI = \c a s carg4 -> do
      -- solution: b_0[0,7] b_12[0,1] b_3[0,6] b_6[0,4] b_9[0,3] carg3[] carg3[0] carg3[0,0] data0_2[0,8] data3_1_4_8[0,5] data6_1_4_7_10_14[0,2]
      -- cost: 12
      (carg3) <- (do
        data3_1_4_8 <- pure " -"
        data6_1_4_7_10_14 <- pure "-> "
        data0_2 <- pure "Tentative move: "
        (OneTuple (b_0)) <- runProcedure @'[ 'In, 'Out, 'In ] append data0_2 carg4
        (OneTuple (b_3)) <- runProcedure @'[ 'In, 'Out, 'In ] appendShow c b_0
        (OneTuple (b_6)) <- runProcedure @'[ 'In, 'Out, 'In ] append data3_1_4_8 b_3
        (OneTuple (b_9)) <- runProcedure @'[ 'In, 'Out, 'In ] appendShow a b_6
        (OneTuple (b_12)) <- runProcedure @'[ 'In, 'Out, 'In ] append data6_1_4_7_10_14 b_9
        (OneTuple (carg3)) <- runProcedure @'[ 'In, 'Out, 'In ] appendShow s b_12
        pure (carg3)
       )
      pure (OneTuple (carg3))
    
    showMoveIIOII = \c a carg3 carg4 -> do
      -- solution: b_0[0,7] b_12[0,1] b_3[0,6] b_6[0,4] b_9[0,3] data0_2[0,8] data3_1_4_8[0,5] data6_1_4_7_10_14[0,2] s[] s[0] s[0,0]
      -- cost: 12
      (s) <- (do
        data3_1_4_8 <- pure " -"
        data6_1_4_7_10_14 <- pure "-> "
        data0_2 <- pure "Tentative move: "
        (OneTuple (b_0)) <- runProcedure @'[ 'In, 'Out, 'In ] append data0_2 carg4
        (OneTuple (b_3)) <- runProcedure @'[ 'In, 'Out, 'In ] appendShow c b_0
        (OneTuple (b_6)) <- runProcedure @'[ 'In, 'Out, 'In ] append data3_1_4_8 b_3
        (OneTuple (b_9)) <- runProcedure @'[ 'In, 'Out, 'In ] appendShow a b_6
        (OneTuple (b_12)) <- runProcedure @'[ 'In, 'Out, 'In ] append data6_1_4_7_10_14 b_9
        (OneTuple (s)) <- runProcedure @'[ 'Out, 'In, 'In ] appendShow carg3 b_12
        pure (s)
       )
      pure (OneTuple (s))
    
    showMoveIIOOI = \c a carg4 -> do
      -- solution: b_0[0,7] b_12[0,1] b_3[0,6] b_6[0,4] b_9[0,3] carg3[] carg3[0] carg3[0,0] data0_2[0,8] data3_1_4_8[0,5] data6_1_4_7_10_14[0,2] s[] s[0] s[0,0]
      -- cost: 13
      (carg3,s) <- (do
        data3_1_4_8 <- pure " -"
        data6_1_4_7_10_14 <- pure "-> "
        data0_2 <- pure "Tentative move: "
        (OneTuple (b_0)) <- runProcedure @'[ 'In, 'Out, 'In ] append data0_2 carg4
        (OneTuple (b_3)) <- runProcedure @'[ 'In, 'Out, 'In ] appendShow c b_0
        (OneTuple (b_6)) <- runProcedure @'[ 'In, 'Out, 'In ] append data3_1_4_8 b_3
        (OneTuple (b_9)) <- runProcedure @'[ 'In, 'Out, 'In ] appendShow a b_6
        (OneTuple (b_12)) <- runProcedure @'[ 'In, 'Out, 'In ] append data6_1_4_7_10_14 b_9
        (s,carg3) <- runProcedure @'[ 'Out, 'Out, 'In ] appendShow b_12
        pure (carg3,s)
       )
      pure (s,carg3)
    
    showMoveIOIII = \c s carg3 carg4 -> do
      -- solution: a[] a[0] a[0,3] b_0[0,7] b_12[0,0] b_3[0,6] b_6[0,4] b_9[0,1] data0_2[0,8] data3_1_4_8[0,5] data6_1_4_7_10_14[0,2]
      -- cost: 12
      (a) <- (do
        data3_1_4_8 <- pure " -"
        data6_1_4_7_10_14 <- pure "-> "
        data0_2 <- pure "Tentative move: "
        (OneTuple (b_0)) <- runProcedure @'[ 'In, 'Out, 'In ] append data0_2 carg4
        (OneTuple (b_3)) <- runProcedure @'[ 'In, 'Out, 'In ] appendShow c b_0
        (OneTuple (b_6)) <- runProcedure @'[ 'In, 'Out, 'In ] append data3_1_4_8 b_3
        (OneTuple (b_12)) <- runProcedure @'[ 'In, 'In, 'Out ] appendShow s carg3
        (OneTuple (b_9)) <- runProcedure @'[ 'In, 'In, 'Out ] append data6_1_4_7_10_14 b_12
        (OneTuple (a)) <- runProcedure @'[ 'Out, 'In, 'In ] appendShow b_9 b_6
        pure (a)
       )
      pure (OneTuple (a))
    
    showMoveIOIOI = \c s carg4 -> do
      -- solution: a[] a[0] a[0,3] b_0[0,7] b_12[0,1] b_3[0,6] b_6[0,4] b_9[0,3] carg3[] carg3[0] carg3[0,0] data0_2[0,8] data3_1_4_8[0,5] data6_1_4_7_10_14[0,2]
      -- cost: 13
      (a,carg3) <- (do
        data3_1_4_8 <- pure " -"
        data6_1_4_7_10_14 <- pure "-> "
        data0_2 <- pure "Tentative move: "
        (OneTuple (b_0)) <- runProcedure @'[ 'In, 'Out, 'In ] append data0_2 carg4
        (OneTuple (b_3)) <- runProcedure @'[ 'In, 'Out, 'In ] appendShow c b_0
        (OneTuple (b_6)) <- runProcedure @'[ 'In, 'Out, 'In ] append data3_1_4_8 b_3
        (a,b_9) <- runProcedure @'[ 'Out, 'Out, 'In ] appendShow b_6
        (OneTuple (b_12)) <- runProcedure @'[ 'In, 'Out, 'In ] append data6_1_4_7_10_14 b_9
        (OneTuple (carg3)) <- runProcedure @'[ 'In, 'Out, 'In ] appendShow s b_12
        pure (a,carg3)
       )
      pure (a,carg3)
    
    showMoveIOOII = \c carg3 carg4 -> do
      -- solution: a[] a[0] a[0,3] b_0[0,7] b_12[0,1] b_3[0,6] b_6[0,4] b_9[0,3] data0_2[0,8] data3_1_4_8[0,5] data6_1_4_7_10_14[0,2] s[] s[0] s[0,0]
      -- cost: 13
      (a,s) <- (do
        data3_1_4_8 <- pure " -"
        data6_1_4_7_10_14 <- pure "-> "
        data0_2 <- pure "Tentative move: "
        (OneTuple (b_0)) <- runProcedure @'[ 'In, 'Out, 'In ] append data0_2 carg4
        (OneTuple (b_3)) <- runProcedure @'[ 'In, 'Out, 'In ] appendShow c b_0
        (OneTuple (b_6)) <- runProcedure @'[ 'In, 'Out, 'In ] append data3_1_4_8 b_3
        (a,b_9) <- runProcedure @'[ 'Out, 'Out, 'In ] appendShow b_6
        (OneTuple (b_12)) <- runProcedure @'[ 'In, 'Out, 'In ] append data6_1_4_7_10_14 b_9
        (OneTuple (s)) <- runProcedure @'[ 'Out, 'In, 'In ] appendShow carg3 b_12
        pure (a,s)
       )
      pure (a,s)
    
    showMoveIOOOI = \c carg4 -> do
      -- solution: a[] a[0] a[0,3] b_0[0,7] b_12[0,1] b_3[0,6] b_6[0,4] b_9[0,3] carg3[] carg3[0] carg3[0,0] data0_2[0,8] data3_1_4_8[0,5] data6_1_4_7_10_14[0,2] s[] s[0] s[0,0]
      -- cost: 14
      (a,carg3,s) <- (do
        data3_1_4_8 <- pure " -"
        data6_1_4_7_10_14 <- pure "-> "
        data0_2 <- pure "Tentative move: "
        (OneTuple (b_0)) <- runProcedure @'[ 'In, 'Out, 'In ] append data0_2 carg4
        (OneTuple (b_3)) <- runProcedure @'[ 'In, 'Out, 'In ] appendShow c b_0
        (OneTuple (b_6)) <- runProcedure @'[ 'In, 'Out, 'In ] append data3_1_4_8 b_3
        (a,b_9) <- runProcedure @'[ 'Out, 'Out, 'In ] appendShow b_6
        (OneTuple (b_12)) <- runProcedure @'[ 'In, 'Out, 'In ] append data6_1_4_7_10_14 b_9
        (s,carg3) <- runProcedure @'[ 'Out, 'Out, 'In ] appendShow b_12
        pure (a,carg3,s)
       )
      pure (a,s,carg3)
    
    showMoveOIIII = \a s carg3 carg4 -> do
      -- solution: b_0[0,7] b_12[0,0] b_3[0,4] b_6[0,3] b_9[0,1] c[] c[0] c[0,6] data0_2[0,8] data3_1_4_8[0,5] data6_1_4_7_10_14[0,2]
      -- cost: 12
      (c) <- (do
        data3_1_4_8 <- pure " -"
        data6_1_4_7_10_14 <- pure "-> "
        data0_2 <- pure "Tentative move: "
        (OneTuple (b_0)) <- runProcedure @'[ 'In, 'Out, 'In ] append data0_2 carg4
        (OneTuple (b_12)) <- runProcedure @'[ 'In, 'In, 'Out ] appendShow s carg3
        (OneTuple (b_9)) <- runProcedure @'[ 'In, 'In, 'Out ] append data6_1_4_7_10_14 b_12
        (OneTuple (b_6)) <- runProcedure @'[ 'In, 'In, 'Out ] appendShow a b_9
        (OneTuple (b_3)) <- runProcedure @'[ 'In, 'In, 'Out ] append data3_1_4_8 b_6
        (OneTuple (c)) <- runProcedure @'[ 'Out, 'In, 'In ] appendShow b_3 b_0
        pure (c)
       )
      pure (OneTuple (c))
    
    showMoveOIIOI = \a s carg4 -> do
      -- solution: b_0[0,7] b_12[0,1] b_3[0,6] b_6[0,4] b_9[0,3] c[] c[0] c[0,6] carg3[] carg3[0] carg3[0,0] data0_2[0,8] data3_1_4_8[0,5] data6_1_4_7_10_14[0,2]
      -- cost: 13
      (c,carg3) <- (do
        data3_1_4_8 <- pure " -"
        data6_1_4_7_10_14 <- pure "-> "
        data0_2 <- pure "Tentative move: "
        (OneTuple (b_0)) <- runProcedure @'[ 'In, 'Out, 'In ] append data0_2 carg4
        (c,b_3) <- runProcedure @'[ 'Out, 'Out, 'In ] appendShow b_0
        (OneTuple (b_6)) <- runProcedure @'[ 'In, 'Out, 'In ] append data3_1_4_8 b_3
        (OneTuple (b_9)) <- runProcedure @'[ 'In, 'Out, 'In ] appendShow a b_6
        (OneTuple (b_12)) <- runProcedure @'[ 'In, 'Out, 'In ] append data6_1_4_7_10_14 b_9
        (OneTuple (carg3)) <- runProcedure @'[ 'In, 'Out, 'In ] appendShow s b_12
        pure (c,carg3)
       )
      pure (c,carg3)
    
    showMoveOIOII = \a carg3 carg4 -> do
      -- solution: b_0[0,7] b_12[0,1] b_3[0,6] b_6[0,4] b_9[0,3] c[] c[0] c[0,6] data0_2[0,8] data3_1_4_8[0,5] data6_1_4_7_10_14[0,2] s[] s[0] s[0,0]
      -- cost: 13
      (c,s) <- (do
        data3_1_4_8 <- pure " -"
        data6_1_4_7_10_14 <- pure "-> "
        data0_2 <- pure "Tentative move: "
        (OneTuple (b_0)) <- runProcedure @'[ 'In, 'Out, 'In ] append data0_2 carg4
        (c,b_3) <- runProcedure @'[ 'Out, 'Out, 'In ] appendShow b_0
        (OneTuple (b_6)) <- runProcedure @'[ 'In, 'Out, 'In ] append data3_1_4_8 b_3
        (OneTuple (b_9)) <- runProcedure @'[ 'In, 'Out, 'In ] appendShow a b_6
        (OneTuple (b_12)) <- runProcedure @'[ 'In, 'Out, 'In ] append data6_1_4_7_10_14 b_9
        (OneTuple (s)) <- runProcedure @'[ 'Out, 'In, 'In ] appendShow carg3 b_12
        pure (c,s)
       )
      pure (c,s)
    
    showMoveOIOOI = \a carg4 -> do
      -- solution: b_0[0,7] b_12[0,1] b_3[0,6] b_6[0,4] b_9[0,3] c[] c[0] c[0,6] carg3[] carg3[0] carg3[0,0] data0_2[0,8] data3_1_4_8[0,5] data6_1_4_7_10_14[0,2] s[] s[0] s[0,0]
      -- cost: 14
      (c,carg3,s) <- (do
        data3_1_4_8 <- pure " -"
        data6_1_4_7_10_14 <- pure "-> "
        data0_2 <- pure "Tentative move: "
        (OneTuple (b_0)) <- runProcedure @'[ 'In, 'Out, 'In ] append data0_2 carg4
        (c,b_3) <- runProcedure @'[ 'Out, 'Out, 'In ] appendShow b_0
        (OneTuple (b_6)) <- runProcedure @'[ 'In, 'Out, 'In ] append data3_1_4_8 b_3
        (OneTuple (b_9)) <- runProcedure @'[ 'In, 'Out, 'In ] appendShow a b_6
        (OneTuple (b_12)) <- runProcedure @'[ 'In, 'Out, 'In ] append data6_1_4_7_10_14 b_9
        (s,carg3) <- runProcedure @'[ 'Out, 'Out, 'In ] appendShow b_12
        pure (c,carg3,s)
       )
      pure (c,s,carg3)
    
    showMoveOOIII = \s carg3 carg4 -> do
      -- solution: a[] a[0] a[0,3] b_0[0,7] b_12[0,0] b_3[0,6] b_6[0,4] b_9[0,1] c[] c[0] c[0,6] data0_2[0,8] data3_1_4_8[0,5] data6_1_4_7_10_14[0,2]
      -- cost: 13
      (a,c) <- (do
        data3_1_4_8 <- pure " -"
        data6_1_4_7_10_14 <- pure "-> "
        data0_2 <- pure "Tentative move: "
        (OneTuple (b_0)) <- runProcedure @'[ 'In, 'Out, 'In ] append data0_2 carg4
        (OneTuple (b_12)) <- runProcedure @'[ 'In, 'In, 'Out ] appendShow s carg3
        (OneTuple (b_9)) <- runProcedure @'[ 'In, 'In, 'Out ] append data6_1_4_7_10_14 b_12
        (c,b_3) <- runProcedure @'[ 'Out, 'Out, 'In ] appendShow b_0
        (OneTuple (b_6)) <- runProcedure @'[ 'In, 'Out, 'In ] append data3_1_4_8 b_3
        (OneTuple (a)) <- runProcedure @'[ 'Out, 'In, 'In ] appendShow b_9 b_6
        pure (a,c)
       )
      pure (c,a)
    
    showMoveOOIOI = \s carg4 -> do
      -- solution: a[] a[0] a[0,3] b_0[0,7] b_12[0,1] b_3[0,6] b_6[0,4] b_9[0,3] c[] c[0] c[0,6] carg3[] carg3[0] carg3[0,0] data0_2[0,8] data3_1_4_8[0,5] data6_1_4_7_10_14[0,2]
      -- cost: 14
      (a,c,carg3) <- (do
        data3_1_4_8 <- pure " -"
        data6_1_4_7_10_14 <- pure "-> "
        data0_2 <- pure "Tentative move: "
        (OneTuple (b_0)) <- runProcedure @'[ 'In, 'Out, 'In ] append data0_2 carg4
        (c,b_3) <- runProcedure @'[ 'Out, 'Out, 'In ] appendShow b_0
        (OneTuple (b_6)) <- runProcedure @'[ 'In, 'Out, 'In ] append data3_1_4_8 b_3
        (a,b_9) <- runProcedure @'[ 'Out, 'Out, 'In ] appendShow b_6
        (OneTuple (b_12)) <- runProcedure @'[ 'In, 'Out, 'In ] append data6_1_4_7_10_14 b_9
        (OneTuple (carg3)) <- runProcedure @'[ 'In, 'Out, 'In ] appendShow s b_12
        pure (a,c,carg3)
       )
      pure (c,a,carg3)
    
    showMoveOOOII = \carg3 carg4 -> do
      -- solution: a[] a[0] a[0,3] b_0[0,7] b_12[0,1] b_3[0,6] b_6[0,4] b_9[0,3] c[] c[0] c[0,6] data0_2[0,8] data3_1_4_8[0,5] data6_1_4_7_10_14[0,2] s[] s[0] s[0,0]
      -- cost: 14
      (a,c,s) <- (do
        data3_1_4_8 <- pure " -"
        data6_1_4_7_10_14 <- pure "-> "
        data0_2 <- pure "Tentative move: "
        (OneTuple (b_0)) <- runProcedure @'[ 'In, 'Out, 'In ] append data0_2 carg4
        (c,b_3) <- runProcedure @'[ 'Out, 'Out, 'In ] appendShow b_0
        (OneTuple (b_6)) <- runProcedure @'[ 'In, 'Out, 'In ] append data3_1_4_8 b_3
        (a,b_9) <- runProcedure @'[ 'Out, 'Out, 'In ] appendShow b_6
        (OneTuple (b_12)) <- runProcedure @'[ 'In, 'Out, 'In ] append data6_1_4_7_10_14 b_9
        (OneTuple (s)) <- runProcedure @'[ 'Out, 'In, 'In ] appendShow carg3 b_12
        pure (a,c,s)
       )
      pure (c,a,s)
    
    showMoveOOOOI = \carg4 -> do
      -- solution: a[] a[0] a[0,3] b_0[0,7] b_12[0,1] b_3[0,6] b_6[0,4] b_9[0,3] c[] c[0] c[0,6] carg3[] carg3[0] carg3[0,0] data0_2[0,8] data3_1_4_8[0,5] data6_1_4_7_10_14[0,2] s[] s[0] s[0,0]
      -- cost: 15
      (a,c,carg3,s) <- (do
        data3_1_4_8 <- pure " -"
        data6_1_4_7_10_14 <- pure "-> "
        data0_2 <- pure "Tentative move: "
        (OneTuple (b_0)) <- runProcedure @'[ 'In, 'Out, 'In ] append data0_2 carg4
        (c,b_3) <- runProcedure @'[ 'Out, 'Out, 'In ] appendShow b_0
        (OneTuple (b_6)) <- runProcedure @'[ 'In, 'Out, 'In ] append data3_1_4_8 b_3
        (a,b_9) <- runProcedure @'[ 'Out, 'Out, 'In ] appendShow b_6
        (OneTuple (b_12)) <- runProcedure @'[ 'In, 'Out, 'In ] append data6_1_4_7_10_14 b_9
        (s,carg3) <- runProcedure @'[ 'Out, 'Out, 'In ] appendShow b_12
        pure (a,c,carg3,s)
       )
      pure (c,a,s,carg3)
    
{- solve/2
solve arg1 arg2 :- ((arg1 = Search current seen0 actions1, seen0 = seen, actions1 = actions, action a, move current a s, showMove current a s data0 msg, data0 = [], print msg, news = Search s2 data1 data2, s2 = s, data1 = s3:seen4, s3 = s, seen4 = seen, data2 = a:actions5, actions5 = actions, if (elem s seen) then (empty) else (), if (final s) then (r = news) else (solve news r), arg2 = r)).
constraints:
~action[0]
~elem[0,15,0]
~empty[0,15,1]
~final[0,16,0]
~move[0]
~msg[0,7]
~print[0]
~s[0,15]
~s[0,15,0,0]
~s[0,16]
~s[0,16,0,0]
~seen[0,15]
~seen[0,15,0,0]
~showMove[0]
~solve[0,16,2]
~(a[0,3] & a[0,4])
~(a[0,3] & a[0,5])
~(a[0,3] & a[0,13])
~(a[0,4] & a[0,5])
~(a[0,4] & a[0,13])
~(a[0,5] & a[0,13])
~(actions[0,2] & actions[0,14])
~(actions1[0,0] & actions1[0,2])
~(actions1[0,2] & actions[0,2])
~(actions5[0,13] & actions5[0,14])
~(actions5[0,14] & actions[0,14])
~(arg1[0,0] & current[0,0])
~(arg2[0,17] & r[0,17])
~(current[0,0] & current[0,4])
~(current[0,0] & current[0,5])
~(current[0,4] & current[0,5])
~(data0[0,5] & data0[0,6])
~(data1[0,8] & data1[0,10])
~(data1[0,10] & s3[0,10])
~(data2[0,8] & data2[0,13])
~(data2[0,13] & a[0,13])
~(msg[0,5] & msg[0,7])
~(news[0,8] & news[0,16])
~(news[0,8] & s2[0,8])
~(r[0,16] & r[0,17])
~(r[0,16,1,0] & news[0,16,1,0])
~(s[0,4] & s[0,5])
~(s[0,4] & s[0,9])
~(s[0,4] & s[0,11])
~(s[0,4] & s[0,15])
~(s[0,4] & s[0,16])
~(s[0,5] & s[0,9])
~(s[0,5] & s[0,11])
~(s[0,5] & s[0,15])
~(s[0,5] & s[0,16])
~(s[0,9] & s[0,11])
~(s[0,9] & s[0,15])
~(s[0,9] & s[0,16])
~(s[0,11] & s[0,15])
~(s[0,11] & s[0,16])
~(s[0,15] & s[0,16])
~(s2[0,8] & s2[0,9])
~(s2[0,9] & s[0,9])
~(s3[0,10] & s3[0,11])
~(s3[0,11] & s[0,11])
~(seen[0,1] & seen[0,12])
~(seen[0,1] & seen[0,15])
~(seen[0,12] & seen[0,15])
~(seen0[0,0] & seen0[0,1])
~(seen0[0,1] & seen[0,1])
~(seen4[0,10] & seen4[0,12])
~(seen4[0,12] & seen[0,12])
(a[0,3] | ~a[0,3])
(a[0,3] | (a[0,4] | (a[0,5] | a[0,13])))
(actions[0,2] | actions[0,14])
(actions1[0,0] | actions1[0,2])
(actions5[0,13] | actions5[0,14])
(current[0,0] | (current[0,4] | current[0,5]))
(data0[0,5] | data0[0,6])
(data1[0,8] | data1[0,10])
(data2[0,8] | data2[0,13])
(msg[0,5] | msg[0,7])
(news[0,8] | news[0,16])
(r[0,16] | r[0,17])
(s[0,4] | (s[0,5] | (s[0,9] | (s[0,11] | (s[0,15] | s[0,16])))))
(s2[0,8] | s2[0,9])
(s3[0,10] | s3[0,11])
(seen[0,1] | (seen[0,12] | seen[0,15]))
(seen0[0,0] | seen0[0,1])
(seen4[0,10] | seen4[0,12])
((current[0,4] & (~a[0,4] & ~s[0,4])) | ((~current[0,4] & (a[0,4] & ~s[0,4])) | ((~current[0,4] & (~a[0,4] & s[0,4])) | (~current[0,4] & (~a[0,4] & ~s[0,4])))))
((current[0,5] & (a[0,5] & (s[0,5] & (data0[0,5] & ~msg[0,5])))) | ((current[0,5] & (a[0,5] & (s[0,5] & (~data0[0,5] & ~msg[0,5])))) | ((current[0,5] & (a[0,5] & (~s[0,5] & (data0[0,5] & ~msg[0,5])))) | ((current[0,5] & (a[0,5] & (~s[0,5] & (~data0[0,5] & ~msg[0,5])))) | ((current[0,5] & (~a[0,5] & (s[0,5] & (data0[0,5] & ~msg[0,5])))) | ((current[0,5] & (~a[0,5] & (s[0,5] & (~data0[0,5] & ~msg[0,5])))) | ((current[0,5] & (~a[0,5] & (~s[0,5] & (data0[0,5] & ~msg[0,5])))) | ((current[0,5] & (~a[0,5] & (~s[0,5] & (~data0[0,5] & ~msg[0,5])))) | ((~current[0,5] & (a[0,5] & (s[0,5] & (data0[0,5] & ~msg[0,5])))) | ((~current[0,5] & (a[0,5] & (s[0,5] & (~data0[0,5] & ~msg[0,5])))) | ((~current[0,5] & (a[0,5] & (~s[0,5] & (data0[0,5] & ~msg[0,5])))) | ((~current[0,5] & (a[0,5] & (~s[0,5] & (~data0[0,5] & ~msg[0,5])))) | ((~current[0,5] & (~a[0,5] & (s[0,5] & (data0[0,5] & ~msg[0,5])))) | ((~current[0,5] & (~a[0,5] & (s[0,5] & (~data0[0,5] & ~msg[0,5])))) | ((~current[0,5] & (~a[0,5] & (~s[0,5] & (data0[0,5] & ~msg[0,5])))) | ((~current[0,5] & (~a[0,5] & (~s[0,5] & (~data0[0,5] & msg[0,5])))) | (~current[0,5] & (~a[0,5] & (~s[0,5] & (~data0[0,5] & ~msg[0,5]))))))))))))))))))))
((s[0,15,0,0] & ~seen[0,15,0,0]) | (~s[0,15,0,0] & ~seen[0,15,0,0]))
(a[0,13] <-> actions5[0,13])
(arg1[] <-> arg1[0])
(arg1[0] <-> arg1[0,0])
(arg2[] <-> arg2[0])
(arg2[0] <-> arg2[0,17])
(current[0,0] <-> actions1[0,0])
(current[0,0] <-> seen0[0,0])
(elem[0] <-> elem[0,15])
(elem[0,15] <-> elem[0,15,0])
(empty[0] <-> empty[0,15])
(empty[0,15] <-> empty[0,15,1])
(final[0] <-> final[0,16])
(final[0,16] <-> final[0,16,0])
(news[0,16] <-> (news[0,16,1] | news[0,16,2]))
(news[0,16,1] <-> news[0,16,1,0])
(news[0,16,1] <-> news[0,16,2])
(news[0,16,2] <-> news[0,16,2,0])
(news[0,16,2,0] <-> arg1[])
(r[0,16] <-> (r[0,16,1] | r[0,16,2]))
(r[0,16,1] <-> r[0,16,1,0])
(r[0,16,1] <-> r[0,16,2])
(r[0,16,2] <-> r[0,16,2,0])
(r[0,16,2,0] <-> arg2[])
(s2[0,8] <-> data1[0,8])
(s2[0,8] <-> data2[0,8])
(s3[0,10] <-> seen4[0,10])
(solve[0] <-> solve[0,16])
(solve[0,16] <-> solve[0,16,2])
1
-}
--mode ordering failure, cyclic dependency: [16] if (final::I s::I) then (r::I = news::O) else (solve::I news::O r::I) -> [8] news::I = Search s2::O data1::O data2::O -> [9] s2::I = s::O
--mode ordering failure, cyclic dependency: [16] if (final::I s::I) then (r::I = news::O) else (solve::I news::O r::I) -> [8] news::I = Search s2::O data1::O data2::O -> [10] data1::I = s3::O:seen4::O -> [11] s3::I = s::O
solve = rget $ (procedure @'[ 'In, 'In ] solveII) :& (procedure @'[ 'In, 'Out ] solveIO) :& RNil
  where
    solveII = \arg1 arg2 -> Logic.once $ do
      -- solution: a[0,3] actions[0,2] actions1[0,0] actions5[0,14] current[0,0] data0[0,6] data1[0,10] data2[0,13] msg[0,5] news[0,8] r[0,17] s[0,4] s2[0,9] s3[0,11] seen[0,1] seen0[0,0] seen4[0,12]
      -- cost: 11
      () <- (do
        r <- pure arg2
        (Search current seen0 actions1) <- pure arg1
        actions <- pure actions1
        actions5 <- pure actions
        seen <- pure seen0
        seen4 <- pure seen
        data0 <- pure []
        (OneTuple (a)) <- runProcedure @'[ 'Out ] action 
        data2 <- pure (a:actions5)
        (OneTuple (s)) <- runProcedure @'[ 'In, 'In, 'Out ] move current a
        s2 <- pure s
        s3 <- pure s
        data1 <- pure (s3:seen4)
        news <- pure (Search s2 data1 data2)
        (OneTuple (msg)) <- runProcedure @'[ 'In, 'In, 'In, 'In, 'Out ] showMove current a s data0
        () <- runProcedure @'[ 'In ] print msg
        () <- Logic.ifte ((do
          () <- runProcedure @'[ 'In, 'In ] elem s seen
          pure ()
         )) (\() -> (do
          () <- empty 
          pure ()
         )) ((do
          
          pure ()
         ))
        () <- Logic.ifte ((do
          () <- runProcedure @'[ 'In ] final s
          pure ()
         )) (\() -> (do
          guard $ r == news
          pure ()
         )) ((do
          () <- solveII news r
          pure ()
         ))
        pure ()
       )
      pure ()
    
    solveIO = \arg1 -> do
      -- solution: a[0,3] actions[0,2] actions1[0,0] actions5[0,14] arg2[] arg2[0] arg2[0,17] current[0,0] data0[0,6] data1[0,10] data2[0,13] msg[0,5] news[0,8] r[0,16] r[0,16,1] r[0,16,1,0] r[0,16,2] r[0,16,2,0] s[0,4] s2[0,9] s3[0,11] seen[0,1] seen0[0,0] seen4[0,12]
      -- cost: 12
      (arg2) <- (do
        (Search current seen0 actions1) <- pure arg1
        actions <- pure actions1
        actions5 <- pure actions
        seen <- pure seen0
        seen4 <- pure seen
        data0 <- pure []
        (OneTuple (a)) <- runProcedure @'[ 'Out ] action 
        data2 <- pure (a:actions5)
        (OneTuple (s)) <- runProcedure @'[ 'In, 'In, 'Out ] move current a
        s2 <- pure s
        s3 <- pure s
        data1 <- pure (s3:seen4)
        news <- pure (Search s2 data1 data2)
        (OneTuple (msg)) <- runProcedure @'[ 'In, 'In, 'In, 'In, 'Out ] showMove current a s data0
        () <- runProcedure @'[ 'In ] print msg
        () <- Logic.ifte ((do
          () <- runProcedure @'[ 'In, 'In ] elem s seen
          pure ()
         )) (\() -> (do
          () <- empty 
          pure ()
         )) ((do
          
          pure ()
         ))
        (r) <- Logic.ifte ((do
          () <- runProcedure @'[ 'In ] final s
          pure ()
         )) (\() -> (do
          r <- pure news
          pure (r)
         )) ((do
          (OneTuple (r)) <- solveIO news
          pure (r)
         ))
        arg2 <- pure r
        pure (arg2)
       )
      pure (OneTuple (arg2))
    