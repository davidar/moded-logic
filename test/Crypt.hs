{-# LANGUAGE DataKinds, FlexibleContexts, NoImplicitPrelude, NoMonomorphismRestriction, TypeApplications #-}
module Crypt where

import qualified Control.Monad.Logic as Logic
import Control.Monad.Logic.Moded.Prelude

{- sumDigits/4
sumDigits arg1 arg2 arg3 arg4 :- ((arg1 = [], arg2 = [], if (carry = 0) then (cs = []) else (cs = carry0:[], carry0 = carry), arg3 = carry, arg4 = cs); (arg1 = [], arg2 = b1:bs2, b1 = b, bs2 = bs, arg4 = c:cs, if (carry = 0) then (c = b, cs = bs) else (plus b carry x, divMod x data0 carry' c, data0 = 10, sumDigits data1 bs carry' cs, data1 = []), arg3 = carry); (arg1 = a3:as4, a3 = a, as4 = as, arg2 = [], arg4 = c:cs, if (carry = 0) then (c = a, cs = as) else (plus a carry x, divMod x data2 carry' c, data2 = 10, sumDigits data3 as carry' cs, data3 = []), arg3 = carry); (arg1 = a5:as, a5 = a, arg2 = b6:bs, b6 = b, arg4 = c:cs, sum data5 x, data4 = [], data5 = a7:b8:carry9:data4, a7 = a, b8 = b, carry9 = carry, divMod x data6 carry' c, data6 = 10, sumDigits as bs carry' cs, arg3 = carry)).
constraints:
~carry[0,2,0,0]
~carry[0,2,2]
~carry[1,5,0,0]
~carry[1,5,2]
~carry[2,5,0,0]
~carry[2,5,2]
~divMod[1,5,2]
~divMod[2,5,2]
~divMod[3]
~plus[1,5,2]
~plus[2,5,2]
~sum[3]
~sumDigits[1,5,2]
~sumDigits[2,5,2]
~sumDigits[3]
~(a[2,1] & a[2,5])
~(a[3,1] & a[3,8])
~(a3[2,0] & a3[2,1])
~(a3[2,1] & a[2,1])
~(a5[3,0] & a5[3,1])
~(a5[3,1] & a[3,1])
~(a7[3,7] & a7[3,8])
~(a7[3,8] & a[3,8])
~(arg1[2,0] & a3[2,0])
~(arg1[3,0] & a5[3,0])
~(arg2[1,1] & b1[1,1])
~(arg2[3,2] & b6[3,2])
~(arg3[0,3] & carry[0,3])
~(arg3[1,6] & carry[1,6])
~(arg3[2,6] & carry[2,6])
~(arg3[3,14] & carry[3,14])
~(arg4[0,4] & cs[0,4])
~(arg4[1,4] & c[1,4])
~(arg4[2,4] & c[2,4])
~(arg4[3,4] & c[3,4])
~(as[2,2] & as[2,5])
~(as[3,0] & as[3,13])
~(as4[2,0] & as4[2,2])
~(as4[2,2] & as[2,2])
~(b[1,2] & b[1,5])
~(b[3,3] & b[3,9])
~(b1[1,1] & b1[1,2])
~(b1[1,2] & b[1,2])
~(b6[3,2] & b6[3,3])
~(b6[3,3] & b[3,3])
~(b8[3,7] & b8[3,9])
~(b8[3,9] & b[3,9])
~(bs[1,3] & bs[1,5])
~(bs[3,2] & bs[3,13])
~(bs2[1,1] & bs2[1,3])
~(bs2[1,3] & bs[1,3])
~(c[1,4] & c[1,5])
~(c[1,5,1,0] & b[1,5,1,0])
~(c[2,4] & c[2,5])
~(c[2,5,1,0] & a[2,5,1,0])
~(c[3,4] & c[3,11])
~(carry[0,2] & carry[0,3])
~(carry[1,5] & carry[1,6])
~(carry[2,5] & carry[2,6])
~(carry[3,10] & carry[3,14])
~(carry'[1,5,2,1] & carry'[1,5,2,3])
~(carry'[2,5,2,1] & carry'[2,5,2,3])
~(carry'[3,11] & carry'[3,13])
~(carry0[0,2,2,0] & carry0[0,2,2,1])
~(carry0[0,2,2,1] & carry[0,2,2,1])
~(carry9[3,7] & carry9[3,10])
~(carry9[3,10] & carry[3,10])
~(cs[0,2] & cs[0,4])
~(cs[0,2,2,0] & carry0[0,2,2,0])
~(cs[1,4] & cs[1,5])
~(cs[1,5,1,1] & bs[1,5,1,1])
~(cs[2,4] & cs[2,5])
~(cs[2,5,1,1] & as[2,5,1,1])
~(cs[3,4] & cs[3,13])
~(data0[1,5,2,1] & data0[1,5,2,2])
~(data1[1,5,2,3] & data1[1,5,2,4])
~(data2[2,5,2,1] & data2[2,5,2,2])
~(data3[2,5,2,3] & data3[2,5,2,4])
~(data4[3,6] & data4[3,7])
~(data5[3,5] & data5[3,7])
~(data5[3,7] & a7[3,7])
~(data6[3,11] & data6[3,12])
~(x[1,5,2,0] & x[1,5,2,1])
~(x[2,5,2,0] & x[2,5,2,1])
~(x[3,5] & x[3,11])
(a[2,1] | a[2,5])
(a[3,1] | a[3,8])
(a3[2,0] | a3[2,1])
(a5[3,0] | a5[3,1])
(a7[3,7] | a7[3,8])
(as[2,2] | as[2,5])
(as[3,0] | as[3,13])
(as4[2,0] | as4[2,2])
(b[1,2] | b[1,5])
(b[3,3] | b[3,9])
(b1[1,1] | b1[1,2])
(b6[3,2] | b6[3,3])
(b8[3,7] | b8[3,9])
(bs[1,3] | bs[1,5])
(bs[3,2] | bs[3,13])
(bs2[1,1] | bs2[1,3])
(c[1,4] | c[1,5])
(c[2,4] | c[2,5])
(c[3,4] | c[3,11])
(carry[0,2] | carry[0,3])
(carry[1,5] | carry[1,6])
(carry[2,5] | carry[2,6])
(carry[3,10] | carry[3,14])
(carry'[1,5,2,1] | carry'[1,5,2,3])
(carry'[2,5,2,1] | carry'[2,5,2,3])
(carry'[3,11] | carry'[3,13])
(carry0[0,2,2,0] | carry0[0,2,2,1])
(carry9[3,7] | carry9[3,10])
(cs[0,2] | cs[0,4])
(cs[1,4] | cs[1,5])
(cs[2,4] | cs[2,5])
(cs[3,4] | cs[3,13])
(data0[1,5,2,1] | data0[1,5,2,2])
(data1[1,5,2,3] | data1[1,5,2,4])
(data2[2,5,2,1] | data2[2,5,2,2])
(data3[2,5,2,3] | data3[2,5,2,4])
(data4[3,6] | data4[3,7])
(data5[3,5] | data5[3,7])
(data6[3,11] | data6[3,12])
(x[1,5,2,0] | x[1,5,2,1])
(x[2,5,2,0] | x[2,5,2,1])
(x[3,5] | x[3,11])
((a[2,5,2,0] & (~carry[2,5,2,0] & ~x[2,5,2,0])) | ((~a[2,5,2,0] & (carry[2,5,2,0] & ~x[2,5,2,0])) | ((~a[2,5,2,0] & (~carry[2,5,2,0] & x[2,5,2,0])) | (~a[2,5,2,0] & (~carry[2,5,2,0] & ~x[2,5,2,0])))))
((b[1,5,2,0] & (~carry[1,5,2,0] & ~x[1,5,2,0])) | ((~b[1,5,2,0] & (carry[1,5,2,0] & ~x[1,5,2,0])) | ((~b[1,5,2,0] & (~carry[1,5,2,0] & x[1,5,2,0])) | (~b[1,5,2,0] & (~carry[1,5,2,0] & ~x[1,5,2,0])))))
((~data5[3,5] & x[3,5]) | (~data5[3,5] & ~x[3,5]))
((~x[1,5,2,1] & (~data0[1,5,2,1] & (carry'[1,5,2,1] & c[1,5,2,1]))) | ((~x[1,5,2,1] & (~data0[1,5,2,1] & (carry'[1,5,2,1] & ~c[1,5,2,1]))) | ((~x[1,5,2,1] & (~data0[1,5,2,1] & (~carry'[1,5,2,1] & c[1,5,2,1]))) | (~x[1,5,2,1] & (~data0[1,5,2,1] & (~carry'[1,5,2,1] & ~c[1,5,2,1]))))))
((~x[2,5,2,1] & (~data2[2,5,2,1] & (carry'[2,5,2,1] & c[2,5,2,1]))) | ((~x[2,5,2,1] & (~data2[2,5,2,1] & (carry'[2,5,2,1] & ~c[2,5,2,1]))) | ((~x[2,5,2,1] & (~data2[2,5,2,1] & (~carry'[2,5,2,1] & c[2,5,2,1]))) | (~x[2,5,2,1] & (~data2[2,5,2,1] & (~carry'[2,5,2,1] & ~c[2,5,2,1]))))))
((~x[3,11] & (~data6[3,11] & (carry'[3,11] & c[3,11]))) | ((~x[3,11] & (~data6[3,11] & (carry'[3,11] & ~c[3,11]))) | ((~x[3,11] & (~data6[3,11] & (~carry'[3,11] & c[3,11]))) | (~x[3,11] & (~data6[3,11] & (~carry'[3,11] & ~c[3,11]))))))
(a[2,5] <-> (a[2,5,1] | a[2,5,2]))
(a[2,5,1] <-> a[2,5,1,0])
(a[2,5,1] <-> a[2,5,2])
(a[2,5,2] <-> a[2,5,2,0])
(a3[2,0] <-> as4[2,0])
(a5[3,0] <-> as[3,0])
(a7[3,7] <-> b8[3,7])
(a7[3,7] <-> carry9[3,7])
(a7[3,7] <-> data4[3,7])
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
(arg2[2] <-> arg2[2,3])
(arg2[3] <-> arg2[3,2])
(arg3[] <-> arg3[0])
(arg3[] <-> arg3[1])
(arg3[] <-> arg3[2])
(arg3[] <-> arg3[3])
(arg3[0] <-> arg3[0,3])
(arg3[1] <-> arg3[1,6])
(arg3[2] <-> arg3[2,6])
(arg3[3] <-> arg3[3,14])
(arg4[] <-> arg4[0])
(arg4[] <-> arg4[1])
(arg4[] <-> arg4[2])
(arg4[] <-> arg4[3])
(arg4[0] <-> arg4[0,4])
(arg4[1] <-> arg4[1,4])
(arg4[2] <-> arg4[2,4])
(arg4[3] <-> arg4[3,4])
(as[2,5] <-> (as[2,5,1] | as[2,5,2]))
(as[2,5,1] <-> as[2,5,1,1])
(as[2,5,1] <-> as[2,5,2])
(as[2,5,2] <-> as[2,5,2,3])
(as[2,5,2,3] <-> arg2[])
(as[3,13] <-> arg1[])
(b[1,5] <-> (b[1,5,1] | b[1,5,2]))
(b[1,5,1] <-> b[1,5,1,0])
(b[1,5,1] <-> b[1,5,2])
(b[1,5,2] <-> b[1,5,2,0])
(b1[1,1] <-> bs2[1,1])
(b6[3,2] <-> bs[3,2])
(bs[1,5] <-> (bs[1,5,1] | bs[1,5,2]))
(bs[1,5,1] <-> bs[1,5,1,1])
(bs[1,5,1] <-> bs[1,5,2])
(bs[1,5,2] <-> bs[1,5,2,3])
(bs[1,5,2,3] <-> arg2[])
(bs[3,13] <-> arg2[])
(c[1,4] <-> cs[1,4])
(c[1,5] <-> (c[1,5,1] | c[1,5,2]))
(c[1,5,1] <-> c[1,5,1,0])
(c[1,5,1] <-> c[1,5,2])
(c[1,5,2] <-> c[1,5,2,1])
(c[2,4] <-> cs[2,4])
(c[2,5] <-> (c[2,5,1] | c[2,5,2]))
(c[2,5,1] <-> c[2,5,1,0])
(c[2,5,1] <-> c[2,5,2])
(c[2,5,2] <-> c[2,5,2,1])
(c[3,4] <-> cs[3,4])
(carry[0,2] <-> carry[0,2,2])
(carry[0,2,2] <-> carry[0,2,2,1])
(carry[1,5] <-> carry[1,5,2])
(carry[1,5,2] <-> carry[1,5,2,0])
(carry[2,5] <-> carry[2,5,2])
(carry[2,5,2] <-> carry[2,5,2,0])
(carry'[1,5,2,3] <-> arg3[])
(carry'[2,5,2,3] <-> arg3[])
(carry'[3,13] <-> arg3[])
(cs[0,2] <-> (cs[0,2,1] | cs[0,2,2]))
(cs[0,2,1] <-> cs[0,2,1,0])
(cs[0,2,1] <-> cs[0,2,2])
(cs[0,2,2] <-> cs[0,2,2,0])
(cs[1,5] <-> (cs[1,5,1] | cs[1,5,2]))
(cs[1,5,1] <-> cs[1,5,1,1])
(cs[1,5,1] <-> cs[1,5,2])
(cs[1,5,2] <-> cs[1,5,2,3])
(cs[1,5,2,3] <-> arg4[])
(cs[2,5] <-> (cs[2,5,1] | cs[2,5,2]))
(cs[2,5,1] <-> cs[2,5,1,1])
(cs[2,5,1] <-> cs[2,5,2])
(cs[2,5,2] <-> cs[2,5,2,3])
(cs[2,5,2,3] <-> arg4[])
(cs[3,13] <-> arg4[])
(data1[1,5,2,3] <-> arg1[])
(data3[2,5,2,3] <-> arg1[])
(divMod[1] <-> divMod[1,5])
(divMod[1,5] <-> divMod[1,5,2])
(divMod[2] <-> divMod[2,5])
(divMod[2,5] <-> divMod[2,5,2])
(plus[1] <-> plus[1,5])
(plus[1,5] <-> plus[1,5,2])
(plus[2] <-> plus[2,5])
(plus[2,5] <-> plus[2,5,2])
(sumDigits[1] <-> sumDigits[1,5])
(sumDigits[1,5] <-> sumDigits[1,5,2])
(sumDigits[2] <-> sumDigits[2,5])
(sumDigits[2,5] <-> sumDigits[2,5,2])
1
-}

sumDigits = rget $ (procedure @'[ 'In, 'In, 'In, 'In ] sumDigitsIIII) :& (procedure @'[ 'In, 'In, 'In, 'Out ] sumDigitsIIIO) :& RNil
  where
    sumDigitsIIII = \arg1 arg2 arg3 arg4 -> Logic.once $ do
      -- solution: a[2,1] a[3,1] a3[2,0] a5[3,0] a7[3,8] as[2,2] as[3,0] as4[2,0] b[1,2] b[3,3] b1[1,1] b6[3,2] b8[3,9] bs[1,3] bs[3,2] bs2[1,1] c[1,4] c[2,4] c[3,4] carry[0,3] carry[1,6] carry[2,6] carry[3,14] carry'[1,5,2,1] carry'[2,5,2,1] carry'[3,11] carry0[0,2,2,0] carry9[3,10] cs[0,4] cs[1,4] cs[2,4] cs[3,4] data0[1,5,2,2] data1[1,5,2,4] data2[2,5,2,2] data3[2,5,2,4] data4[3,6] data5[3,7] data6[3,12] x[1,5,2,0] x[2,5,2,0] x[3,5]
      -- cost: 15
      () <- (do
        guard $ arg1 == []
        guard $ arg2 == []
        carry <- pure arg3
        cs <- pure arg4
        () <- Logic.ifte ((do
          guard $ carry == 0
          pure ()
         )) (\() -> (do
          guard $ cs == []
          pure ()
         )) ((do
          (carry0:[]) <- pure cs
          guard $ carry0 == carry
          pure ()
         ))
        pure ()
       ) <|> (do
        guard $ arg1 == []
        (b1:bs2) <- pure arg2
        carry <- pure arg3
        (c:cs) <- pure arg4
        b <- pure b1
        bs <- pure bs2
        () <- Logic.ifte ((do
          guard $ carry == 0
          pure ()
         )) (\() -> (do
          guard $ c == b
          guard $ cs == bs
          pure ()
         )) ((do
          data0 <- pure 10
          data1 <- pure []
          (OneTuple (x)) <- runProcedure @'[ 'In, 'In, 'Out ] plus b carry
          (OneTuple (carry')) <- runProcedure @'[ 'In, 'In, 'Out, 'In ] divMod x data0 c
          () <- sumDigitsIIII data1 bs carry' cs
          pure ()
         ))
        pure ()
       ) <|> (do
        (a3:as4) <- pure arg1
        a <- pure a3
        guard $ arg2 == []
        carry <- pure arg3
        (c:cs) <- pure arg4
        as <- pure as4
        () <- Logic.ifte ((do
          guard $ carry == 0
          pure ()
         )) (\() -> (do
          guard $ c == a
          guard $ cs == as
          pure ()
         )) ((do
          data2 <- pure 10
          data3 <- pure []
          (OneTuple (x)) <- runProcedure @'[ 'In, 'In, 'Out ] plus a carry
          (OneTuple (carry')) <- runProcedure @'[ 'In, 'In, 'Out, 'In ] divMod x data2 c
          () <- sumDigitsIIII data3 as carry' cs
          pure ()
         ))
        pure ()
       ) <|> (do
        (a5:as) <- pure arg1
        a <- pure a5
        a7 <- pure a
        (b6:bs) <- pure arg2
        carry <- pure arg3
        (c:cs) <- pure arg4
        b <- pure b6
        b8 <- pure b
        carry9 <- pure carry
        data4 <- pure []
        data5 <- pure (a7:b8:carry9:data4)
        data6 <- pure 10
        (OneTuple (x)) <- runProcedure @'[ 'In, 'Out ] sum data5
        (OneTuple (carry')) <- runProcedure @'[ 'In, 'In, 'Out, 'In ] divMod x data6 c
        () <- sumDigitsIIII as bs carry' cs
        pure ()
       )
      pure ()
    
    sumDigitsIIIO = \arg1 arg2 arg3 -> do
      -- solution: a[2,1] a[3,1] a3[2,0] a5[3,0] a7[3,8] arg4[] arg4[0] arg4[0,4] arg4[1] arg4[1,4] arg4[2] arg4[2,4] arg4[3] arg4[3,4] as[2,2] as[3,0] as4[2,0] b[1,2] b[3,3] b1[1,1] b6[3,2] b8[3,9] bs[1,3] bs[3,2] bs2[1,1] c[1,5] c[1,5,1] c[1,5,1,0] c[1,5,2] c[1,5,2,1] c[2,5] c[2,5,1] c[2,5,1,0] c[2,5,2] c[2,5,2,1] c[3,11] carry[0,3] carry[1,6] carry[2,6] carry[3,14] carry'[1,5,2,1] carry'[2,5,2,1] carry'[3,11] carry0[0,2,2,1] carry9[3,10] cs[0,2] cs[0,2,1] cs[0,2,1,0] cs[0,2,2] cs[0,2,2,0] cs[1,5] cs[1,5,1] cs[1,5,1,1] cs[1,5,2] cs[1,5,2,3] cs[2,5] cs[2,5,1] cs[2,5,1,1] cs[2,5,2] cs[2,5,2,3] cs[3,13] data0[1,5,2,2] data1[1,5,2,4] data2[2,5,2,2] data3[2,5,2,4] data4[3,6] data5[3,7] data6[3,12] x[1,5,2,0] x[2,5,2,0] x[3,5]
      -- cost: 21
      (arg4) <- (do
        guard $ arg1 == []
        guard $ arg2 == []
        carry <- pure arg3
        (cs) <- Logic.ifte ((do
          guard $ carry == 0
          pure ()
         )) (\() -> (do
          cs <- pure []
          pure (cs)
         )) ((do
          carry0 <- pure carry
          cs <- pure (carry0:[])
          pure (cs)
         ))
        arg4 <- pure cs
        pure (arg4)
       ) <|> (do
        guard $ arg1 == []
        (b1:bs2) <- pure arg2
        carry <- pure arg3
        b <- pure b1
        bs <- pure bs2
        (c,cs) <- Logic.ifte ((do
          guard $ carry == 0
          pure ()
         )) (\() -> (do
          c <- pure b
          cs <- pure bs
          pure (c,cs)
         )) ((do
          data0 <- pure 10
          data1 <- pure []
          (OneTuple (x)) <- runProcedure @'[ 'In, 'In, 'Out ] plus b carry
          (carry',c) <- runProcedure @'[ 'In, 'In, 'Out, 'Out ] divMod x data0
          (OneTuple (cs)) <- sumDigitsIIIO data1 bs carry'
          pure (c,cs)
         ))
        arg4 <- pure (c:cs)
        pure (arg4)
       ) <|> (do
        (a3:as4) <- pure arg1
        a <- pure a3
        guard $ arg2 == []
        carry <- pure arg3
        as <- pure as4
        (c,cs) <- Logic.ifte ((do
          guard $ carry == 0
          pure ()
         )) (\() -> (do
          c <- pure a
          cs <- pure as
          pure (c,cs)
         )) ((do
          data2 <- pure 10
          data3 <- pure []
          (OneTuple (x)) <- runProcedure @'[ 'In, 'In, 'Out ] plus a carry
          (carry',c) <- runProcedure @'[ 'In, 'In, 'Out, 'Out ] divMod x data2
          (OneTuple (cs)) <- sumDigitsIIIO data3 as carry'
          pure (c,cs)
         ))
        arg4 <- pure (c:cs)
        pure (arg4)
       ) <|> (do
        (a5:as) <- pure arg1
        a <- pure a5
        a7 <- pure a
        (b6:bs) <- pure arg2
        carry <- pure arg3
        b <- pure b6
        b8 <- pure b
        carry9 <- pure carry
        data4 <- pure []
        data5 <- pure (a7:b8:carry9:data4)
        data6 <- pure 10
        (OneTuple (x)) <- runProcedure @'[ 'In, 'Out ] sum data5
        (carry',c) <- runProcedure @'[ 'In, 'In, 'Out, 'Out ] divMod x data6
        (OneTuple (cs)) <- sumDigitsIIIO as bs carry'
        arg4 <- pure (c:cs)
        pure (arg4)
       )
      pure (OneTuple (arg4))
    
{- mulDigits/4
mulDigits arg1 arg2 arg3 arg4 :- ((arg1 = a:as, arg4 = b:bs, timesInt a d ad, plus ad carry x, divMod x data0 carry' b, data0 = 10, mulDigits as d carry' bs, arg2 = d, arg3 = carry); (arg1 = [], arg4 = c:c':[], divMod carry data1 c' c, data1 = 10, arg3 = carry)).
constraints:
~arg2[]
~divMod[0]
~divMod[1]
~mulDigits[0]
~plus[0]
~timesInt[0]
~(a[0,0] & a[0,2])
~(ad[0,2] & ad[0,3])
~(arg1[0,0] & a[0,0])
~(arg2[0,7] & d[0,7])
~(arg3[0,8] & carry[0,8])
~(arg3[1,4] & carry[1,4])
~(arg4[0,1] & b[0,1])
~(arg4[1,1] & c[1,1])
~(as[0,0] & as[0,6])
~(b[0,1] & b[0,4])
~(bs[0,1] & bs[0,6])
~(c[1,1] & c[1,2])
~(c'[1,1] & c'[1,2])
~(carry[0,3] & carry[0,8])
~(carry[1,2] & carry[1,4])
~(carry'[0,4] & carry'[0,6])
~(d[0,2] & d[0,6])
~(d[0,2] & d[0,7])
~(d[0,6] & d[0,7])
~(data0[0,4] & data0[0,5])
~(data1[1,2] & data1[1,3])
~(x[0,3] & x[0,4])
(a[0,0] | a[0,2])
(ad[0,2] | ad[0,3])
(as[0,0] | as[0,6])
(b[0,1] | b[0,4])
(bs[0,1] | bs[0,6])
(c[1,1] | c[1,2])
(c'[1,1] | c'[1,2])
(carry[0,3] | carry[0,8])
(carry[1,2] | carry[1,4])
(carry'[0,4] | carry'[0,6])
(d[0,2] | (d[0,6] | d[0,7]))
(data0[0,4] | data0[0,5])
(data1[1,2] | data1[1,3])
(x[0,3] | x[0,4])
((a[0,2] & (~d[0,2] & ~ad[0,2])) | ((~a[0,2] & (d[0,2] & ~ad[0,2])) | ((~a[0,2] & (~d[0,2] & ad[0,2])) | (~a[0,2] & (~d[0,2] & ~ad[0,2])))))
((ad[0,3] & (~carry[0,3] & ~x[0,3])) | ((~ad[0,3] & (carry[0,3] & ~x[0,3])) | ((~ad[0,3] & (~carry[0,3] & x[0,3])) | (~ad[0,3] & (~carry[0,3] & ~x[0,3])))))
((~carry[1,2] & (~data1[1,2] & (c'[1,2] & c[1,2]))) | ((~carry[1,2] & (~data1[1,2] & (c'[1,2] & ~c[1,2]))) | ((~carry[1,2] & (~data1[1,2] & (~c'[1,2] & c[1,2]))) | (~carry[1,2] & (~data1[1,2] & (~c'[1,2] & ~c[1,2]))))))
((~x[0,4] & (~data0[0,4] & (carry'[0,4] & b[0,4]))) | ((~x[0,4] & (~data0[0,4] & (carry'[0,4] & ~b[0,4]))) | ((~x[0,4] & (~data0[0,4] & (~carry'[0,4] & b[0,4]))) | (~x[0,4] & (~data0[0,4] & (~carry'[0,4] & ~b[0,4]))))))
(a[0,0] <-> as[0,0])
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg1[0] <-> arg1[0,0])
(arg1[1] <-> arg1[1,0])
(arg2[] <-> arg2[0])
(arg2[0] <-> arg2[0,7])
(arg3[] <-> arg3[0])
(arg3[] <-> arg3[1])
(arg3[0] <-> arg3[0,8])
(arg3[1] <-> arg3[1,4])
(arg4[] <-> arg4[0])
(arg4[] <-> arg4[1])
(arg4[0] <-> arg4[0,1])
(arg4[1] <-> arg4[1,1])
(as[0,6] <-> arg1[])
(b[0,1] <-> bs[0,1])
(bs[0,6] <-> arg4[])
(c[1,1] <-> c'[1,1])
(carry'[0,6] <-> arg3[])
(d[0,6] <-> arg2[])
1
-}

mulDigits = rget $ (procedure @'[ 'In, 'In, 'In, 'In ] mulDigitsIIII) :& (procedure @'[ 'In, 'In, 'In, 'Out ] mulDigitsIIIO) :& RNil
  where
    mulDigitsIIII = \arg1 arg2 arg3 arg4 -> Logic.once $ do
      -- solution: a[0,0] ad[0,2] as[0,0] b[0,1] bs[0,1] c[1,1] c'[1,1] carry[0,8] carry[1,4] carry'[0,4] d[0,7] data0[0,5] data1[1,3] x[0,3]
      -- cost: 8
      () <- (do
        (a:as) <- pure arg1
        d <- pure arg2
        carry <- pure arg3
        (b:bs) <- pure arg4
        data0 <- pure 10
        (OneTuple (ad)) <- runProcedure @'[ 'In, 'In, 'Out ] timesInt a d
        (OneTuple (x)) <- runProcedure @'[ 'In, 'In, 'Out ] plus ad carry
        (OneTuple (carry')) <- runProcedure @'[ 'In, 'In, 'Out, 'In ] divMod x data0 b
        () <- mulDigitsIIII as d carry' bs
        pure ()
       ) <|> (do
        guard $ arg1 == []
        carry <- pure arg3
        (c:c':[]) <- pure arg4
        data1 <- pure 10
        () <- runProcedure @'[ 'In, 'In, 'In, 'In ] divMod carry data1 c' c
        pure ()
       )
      pure ()
    
    mulDigitsIIIO = \arg1 arg2 arg3 -> do
      -- solution: a[0,0] ad[0,2] arg4[] arg4[0] arg4[0,1] arg4[1] arg4[1,1] as[0,0] b[0,4] bs[0,6] c[1,2] c'[1,2] carry[0,8] carry[1,4] carry'[0,4] d[0,7] data0[0,5] data1[1,3] x[0,3]
      -- cost: 12
      (arg4) <- (do
        (a:as) <- pure arg1
        d <- pure arg2
        carry <- pure arg3
        data0 <- pure 10
        (OneTuple (ad)) <- runProcedure @'[ 'In, 'In, 'Out ] timesInt a d
        (OneTuple (x)) <- runProcedure @'[ 'In, 'In, 'Out ] plus ad carry
        (carry',b) <- runProcedure @'[ 'In, 'In, 'Out, 'Out ] divMod x data0
        (OneTuple (bs)) <- mulDigitsIIIO as d carry'
        arg4 <- pure (b:bs)
        pure (arg4)
       ) <|> (do
        guard $ arg1 == []
        carry <- pure arg3
        data1 <- pure 10
        (c',c) <- runProcedure @'[ 'In, 'In, 'Out, 'Out ] divMod carry data1
        arg4 <- pure (c:c':[])
        pure (arg4)
       )
      pure (OneTuple (arg4))
    
{- zeros/1
zeros arg1 :- ((arg1 = []); (arg1 = z:zs, z = 0, zeros zs)).
constraints:
~zeros[1]
~(arg1[1,0] & z[1,0])
~(z[1,0] & z[1,1])
~(zs[1,0] & zs[1,2])
(z[1,0] | z[1,1])
(zs[1,0] | zs[1,2])
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg1[0] <-> arg1[0,0])
(arg1[1] <-> arg1[1,0])
(z[1,0] <-> zs[1,0])
(zs[1,2] <-> arg1[])
1
-}

zeros = rget $ (procedure @'[ 'In ] zerosI) :& (procedure @'[ 'Out ] zerosO) :& RNil
  where
    zerosI = \arg1 -> Logic.once $ do
      -- solution: z[1,0] zs[1,0]
      -- cost: 1
      () <- (do
        guard $ arg1 == []
        pure ()
       ) <|> (do
        (z:zs) <- pure arg1
        guard $ z == 0
        () <- zerosI zs
        pure ()
       )
      pure ()
    
    zerosO = do
      -- solution: arg1[] arg1[0] arg1[0,0] arg1[1] arg1[1,0] z[1,1] zs[1,2]
      -- cost: 2
      (arg1) <- (do
        arg1 <- pure []
        pure (arg1)
       ) <|> (do
        z <- pure 0
        (OneTuple (zs)) <- zerosO 
        arg1 <- pure (z:zs)
        pure (arg1)
       )
      pure (OneTuple (arg1))
    
{- oddDigit/1
oddDigit arg1 :- ((arg1 = 1); (arg1 = 3); (arg1 = 5); (arg1 = 7); (arg1 = 9)).
constraints:
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg1[] <-> arg1[2])
(arg1[] <-> arg1[3])
(arg1[] <-> arg1[4])
(arg1[0] <-> arg1[0,0])
(arg1[1] <-> arg1[1,0])
(arg1[2] <-> arg1[2,0])
(arg1[3] <-> arg1[3,0])
(arg1[4] <-> arg1[4,0])
-}

oddDigit = rget $ (procedure @'[ 'In ] oddDigitI) :& (procedure @'[ 'Out ] oddDigitO) :& RNil
  where
    oddDigitI = \arg1 -> Logic.once $ do
      -- solution: 
      -- cost: 0
      () <- (do
        guard $ arg1 == 1
        pure ()
       ) <|> (do
        guard $ arg1 == 3
        pure ()
       ) <|> (do
        guard $ arg1 == 5
        pure ()
       ) <|> (do
        guard $ arg1 == 7
        pure ()
       ) <|> (do
        guard $ arg1 == 9
        pure ()
       )
      pure ()
    
    oddDigitO = do
      -- solution: arg1[] arg1[0] arg1[0,0] arg1[1] arg1[1,0] arg1[2] arg1[2,0] arg1[3] arg1[3,0] arg1[4] arg1[4,0]
      -- cost: 0
      (arg1) <- (do
        arg1 <- pure 1
        pure (arg1)
       ) <|> (do
        arg1 <- pure 3
        pure (arg1)
       ) <|> (do
        arg1 <- pure 5
        pure (arg1)
       ) <|> (do
        arg1 <- pure 7
        pure (arg1)
       ) <|> (do
        arg1 <- pure 9
        pure (arg1)
       )
      pure (OneTuple (arg1))
    
{- evenDigit/1
evenDigit arg1 :- ((arg1 = 0); (arg1 = 2); (arg1 = 4); (arg1 = 6); (arg1 = 8)).
constraints:
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg1[] <-> arg1[2])
(arg1[] <-> arg1[3])
(arg1[] <-> arg1[4])
(arg1[0] <-> arg1[0,0])
(arg1[1] <-> arg1[1,0])
(arg1[2] <-> arg1[2,0])
(arg1[3] <-> arg1[3,0])
(arg1[4] <-> arg1[4,0])
-}

evenDigit = rget $ (procedure @'[ 'In ] evenDigitI) :& (procedure @'[ 'Out ] evenDigitO) :& RNil
  where
    evenDigitI = \arg1 -> Logic.once $ do
      -- solution: 
      -- cost: 0
      () <- (do
        guard $ arg1 == 0
        pure ()
       ) <|> (do
        guard $ arg1 == 2
        pure ()
       ) <|> (do
        guard $ arg1 == 4
        pure ()
       ) <|> (do
        guard $ arg1 == 6
        pure ()
       ) <|> (do
        guard $ arg1 == 8
        pure ()
       )
      pure ()
    
    evenDigitO = do
      -- solution: arg1[] arg1[0] arg1[0,0] arg1[1] arg1[1,0] arg1[2] arg1[2,0] arg1[3] arg1[3,0] arg1[4] arg1[4,0]
      -- cost: 0
      (arg1) <- (do
        arg1 <- pure 0
        pure (arg1)
       ) <|> (do
        arg1 <- pure 2
        pure (arg1)
       ) <|> (do
        arg1 <- pure 4
        pure (arg1)
       ) <|> (do
        arg1 <- pure 6
        pure (arg1)
       ) <|> (do
        arg1 <- pure 8
        pure (arg1)
       )
      pure (OneTuple (arg1))
    
{- crypt/1
crypt arg1 :- ((arg1 = a0:b1:c2:d:e:f3:g4:h5:i6:j7:k8:l9:m10:n11:o12:p13:[], a0 = a, b1 = b, c2 = c, f3 = f, g4 = g, h5 = h, i6 = i, j7 = j, k8 = k, l9 = l, m10 = m, n11 = n, o12 = o, p13 = p, oddDigit a, evenDigit b, evenDigit c, evenDigit d, (>) d data0, data0 = 0, evenDigit e, mulDigits data2 e data3 data4, data1 = [], data2 = c14:b15:a16:data1, c14 = c, b15 = b, a16 = a, data3 = 0, data4 = i17:h18:g19:f20:x, i17 = i, h18 = h, g19 = g, f20 = f, evenDigit f, (>) f data5, data5 = 0, oddDigit g, evenDigit h, evenDigit i, zeros x, mulDigits data7 d data8 data9, data6 = [], data7 = c21:b22:a23:data6, c21 = c, b22 = b, a23 = a, data8 = 0, data9 = l24:k25:j26:y, l24 = l, k25 = k, j26 = j, evenDigit j, (>) j data10, data10 = 0, oddDigit k, evenDigit l, zeros y, sumDigits data12 data15 data16 data17, data11 = [], data12 = i27:h28:g29:f30:data11, i27 = i, h28 = h, g29 = g, f30 = f, data13 = 0, data14 = [], data15 = data13:l31:k32:j33:data14, l31 = l, k32 = k, j33 = j, data16 = 0, data17 = p34:o35:n36:m37:z, p34 = p, o35 = o, n36 = n, m37 = m, oddDigit m, oddDigit n, evenDigit o, evenDigit p, zeros z)).
constraints:
~(>)[0]
~evenDigit[0]
~mulDigits[0]
~oddDigit[0]
~sumDigits[0]
~zeros[0]
~(a[0,1] & a[0,15])
~(a[0,1] & a[0,27])
~(a[0,1] & a[0,46])
~(a[0,15] & a[0,27])
~(a[0,15] & a[0,46])
~(a[0,27] & a[0,46])
~(a0[0,0] & a0[0,1])
~(a0[0,1] & a[0,1])
~(a16[0,24] & a16[0,27])
~(a16[0,27] & a[0,27])
~(a23[0,43] & a23[0,46])
~(a23[0,46] & a[0,46])
~(arg1[0,0] & a0[0,0])
~(b[0,2] & b[0,16])
~(b[0,2] & b[0,26])
~(b[0,2] & b[0,45])
~(b[0,16] & b[0,26])
~(b[0,16] & b[0,45])
~(b[0,26] & b[0,45])
~(b1[0,0] & b1[0,2])
~(b1[0,2] & b[0,2])
~(b15[0,24] & b15[0,26])
~(b15[0,26] & b[0,26])
~(b22[0,43] & b22[0,45])
~(b22[0,45] & b[0,45])
~(c[0,3] & c[0,17])
~(c[0,3] & c[0,25])
~(c[0,3] & c[0,44])
~(c[0,17] & c[0,25])
~(c[0,17] & c[0,44])
~(c[0,25] & c[0,44])
~(c14[0,24] & c14[0,25])
~(c14[0,25] & c[0,25])
~(c2[0,0] & c2[0,3])
~(c2[0,3] & c[0,3])
~(c21[0,43] & c21[0,44])
~(c21[0,44] & c[0,44])
~(d[0,0] & d[0,18])
~(d[0,0] & d[0,19])
~(d[0,0] & d[0,41])
~(d[0,18] & d[0,19])
~(d[0,18] & d[0,41])
~(d[0,19] & d[0,41])
~(data0[0,19] & data0[0,20])
~(data1[0,23] & data1[0,24])
~(data10[0,53] & data10[0,54])
~(data11[0,59] & data11[0,60])
~(data12[0,58] & data12[0,60])
~(data12[0,60] & i27[0,60])
~(data13[0,65] & data13[0,67])
~(data14[0,66] & data14[0,67])
~(data15[0,58] & data15[0,67])
~(data15[0,67] & data13[0,67])
~(data16[0,58] & data16[0,71])
~(data17[0,58] & data17[0,72])
~(data17[0,72] & p34[0,72])
~(data2[0,22] & data2[0,24])
~(data2[0,24] & c14[0,24])
~(data3[0,22] & data3[0,28])
~(data4[0,22] & data4[0,29])
~(data4[0,29] & i17[0,29])
~(data5[0,35] & data5[0,36])
~(data6[0,42] & data6[0,43])
~(data7[0,41] & data7[0,43])
~(data7[0,43] & c21[0,43])
~(data8[0,41] & data8[0,47])
~(data9[0,41] & data9[0,48])
~(data9[0,48] & l24[0,48])
~(e[0,0] & e[0,21])
~(e[0,0] & e[0,22])
~(e[0,21] & e[0,22])
~(f[0,4] & f[0,33])
~(f[0,4] & f[0,34])
~(f[0,4] & f[0,35])
~(f[0,4] & f[0,64])
~(f[0,33] & f[0,34])
~(f[0,33] & f[0,35])
~(f[0,33] & f[0,64])
~(f[0,34] & f[0,35])
~(f[0,34] & f[0,64])
~(f[0,35] & f[0,64])
~(f20[0,29] & f20[0,33])
~(f20[0,33] & f[0,33])
~(f3[0,0] & f3[0,4])
~(f3[0,4] & f[0,4])
~(f30[0,60] & f30[0,64])
~(f30[0,64] & f[0,64])
~(g[0,5] & g[0,32])
~(g[0,5] & g[0,37])
~(g[0,5] & g[0,63])
~(g[0,32] & g[0,37])
~(g[0,32] & g[0,63])
~(g[0,37] & g[0,63])
~(g19[0,29] & g19[0,32])
~(g19[0,32] & g[0,32])
~(g29[0,60] & g29[0,63])
~(g29[0,63] & g[0,63])
~(g4[0,0] & g4[0,5])
~(g4[0,5] & g[0,5])
~(h[0,6] & h[0,31])
~(h[0,6] & h[0,38])
~(h[0,6] & h[0,62])
~(h[0,31] & h[0,38])
~(h[0,31] & h[0,62])
~(h[0,38] & h[0,62])
~(h18[0,29] & h18[0,31])
~(h18[0,31] & h[0,31])
~(h28[0,60] & h28[0,62])
~(h28[0,62] & h[0,62])
~(h5[0,0] & h5[0,6])
~(h5[0,6] & h[0,6])
~(i[0,7] & i[0,30])
~(i[0,7] & i[0,39])
~(i[0,7] & i[0,61])
~(i[0,30] & i[0,39])
~(i[0,30] & i[0,61])
~(i[0,39] & i[0,61])
~(i17[0,29] & i17[0,30])
~(i17[0,30] & i[0,30])
~(i27[0,60] & i27[0,61])
~(i27[0,61] & i[0,61])
~(i6[0,0] & i6[0,7])
~(i6[0,7] & i[0,7])
~(j[0,8] & j[0,51])
~(j[0,8] & j[0,52])
~(j[0,8] & j[0,53])
~(j[0,8] & j[0,70])
~(j[0,51] & j[0,52])
~(j[0,51] & j[0,53])
~(j[0,51] & j[0,70])
~(j[0,52] & j[0,53])
~(j[0,52] & j[0,70])
~(j[0,53] & j[0,70])
~(j26[0,48] & j26[0,51])
~(j26[0,51] & j[0,51])
~(j33[0,67] & j33[0,70])
~(j33[0,70] & j[0,70])
~(j7[0,0] & j7[0,8])
~(j7[0,8] & j[0,8])
~(k[0,9] & k[0,50])
~(k[0,9] & k[0,55])
~(k[0,9] & k[0,69])
~(k[0,50] & k[0,55])
~(k[0,50] & k[0,69])
~(k[0,55] & k[0,69])
~(k25[0,48] & k25[0,50])
~(k25[0,50] & k[0,50])
~(k32[0,67] & k32[0,69])
~(k32[0,69] & k[0,69])
~(k8[0,0] & k8[0,9])
~(k8[0,9] & k[0,9])
~(l[0,10] & l[0,49])
~(l[0,10] & l[0,56])
~(l[0,10] & l[0,68])
~(l[0,49] & l[0,56])
~(l[0,49] & l[0,68])
~(l[0,56] & l[0,68])
~(l24[0,48] & l24[0,49])
~(l24[0,49] & l[0,49])
~(l31[0,67] & l31[0,68])
~(l31[0,68] & l[0,68])
~(l9[0,0] & l9[0,10])
~(l9[0,10] & l[0,10])
~(m[0,11] & m[0,76])
~(m[0,11] & m[0,77])
~(m[0,76] & m[0,77])
~(m10[0,0] & m10[0,11])
~(m10[0,11] & m[0,11])
~(m37[0,72] & m37[0,76])
~(m37[0,76] & m[0,76])
~(n[0,12] & n[0,75])
~(n[0,12] & n[0,78])
~(n[0,75] & n[0,78])
~(n11[0,0] & n11[0,12])
~(n11[0,12] & n[0,12])
~(n36[0,72] & n36[0,75])
~(n36[0,75] & n[0,75])
~(o[0,13] & o[0,74])
~(o[0,13] & o[0,79])
~(o[0,74] & o[0,79])
~(o12[0,0] & o12[0,13])
~(o12[0,13] & o[0,13])
~(o35[0,72] & o35[0,74])
~(o35[0,74] & o[0,74])
~(p[0,14] & p[0,73])
~(p[0,14] & p[0,80])
~(p[0,73] & p[0,80])
~(p13[0,0] & p13[0,14])
~(p13[0,14] & p[0,14])
~(p34[0,72] & p34[0,73])
~(p34[0,73] & p[0,73])
~(x[0,29] & x[0,40])
~(y[0,48] & y[0,57])
~(z[0,72] & z[0,81])
(~d[0,19] & ~data0[0,19])
(~f[0,35] & ~data5[0,35])
(~j[0,53] & ~data10[0,53])
(a[0,1] | (a[0,15] | (a[0,27] | a[0,46])))
(a[0,15] | ~a[0,15])
(a0[0,0] | a0[0,1])
(a16[0,24] | a16[0,27])
(a23[0,43] | a23[0,46])
(b[0,2] | (b[0,16] | (b[0,26] | b[0,45])))
(b[0,16] | ~b[0,16])
(b1[0,0] | b1[0,2])
(b15[0,24] | b15[0,26])
(b22[0,43] | b22[0,45])
(c[0,3] | (c[0,17] | (c[0,25] | c[0,44])))
(c[0,17] | ~c[0,17])
(c14[0,24] | c14[0,25])
(c2[0,0] | c2[0,3])
(c21[0,43] | c21[0,44])
(d[0,0] | (d[0,18] | (d[0,19] | d[0,41])))
(d[0,18] | ~d[0,18])
(data0[0,19] | data0[0,20])
(data1[0,23] | data1[0,24])
(data10[0,53] | data10[0,54])
(data11[0,59] | data11[0,60])
(data12[0,58] | data12[0,60])
(data13[0,65] | data13[0,67])
(data14[0,66] | data14[0,67])
(data15[0,58] | data15[0,67])
(data16[0,58] | data16[0,71])
(data17[0,58] | data17[0,72])
(data2[0,22] | data2[0,24])
(data3[0,22] | data3[0,28])
(data4[0,22] | data4[0,29])
(data5[0,35] | data5[0,36])
(data6[0,42] | data6[0,43])
(data7[0,41] | data7[0,43])
(data8[0,41] | data8[0,47])
(data9[0,41] | data9[0,48])
(e[0,0] | (e[0,21] | e[0,22]))
(e[0,21] | ~e[0,21])
(f[0,4] | (f[0,33] | (f[0,34] | (f[0,35] | f[0,64]))))
(f[0,34] | ~f[0,34])
(f20[0,29] | f20[0,33])
(f3[0,0] | f3[0,4])
(f30[0,60] | f30[0,64])
(g[0,5] | (g[0,32] | (g[0,37] | g[0,63])))
(g[0,37] | ~g[0,37])
(g19[0,29] | g19[0,32])
(g29[0,60] | g29[0,63])
(g4[0,0] | g4[0,5])
(h[0,6] | (h[0,31] | (h[0,38] | h[0,62])))
(h[0,38] | ~h[0,38])
(h18[0,29] | h18[0,31])
(h28[0,60] | h28[0,62])
(h5[0,0] | h5[0,6])
(i[0,7] | (i[0,30] | (i[0,39] | i[0,61])))
(i[0,39] | ~i[0,39])
(i17[0,29] | i17[0,30])
(i27[0,60] | i27[0,61])
(i6[0,0] | i6[0,7])
(j[0,8] | (j[0,51] | (j[0,52] | (j[0,53] | j[0,70]))))
(j[0,52] | ~j[0,52])
(j26[0,48] | j26[0,51])
(j33[0,67] | j33[0,70])
(j7[0,0] | j7[0,8])
(k[0,9] | (k[0,50] | (k[0,55] | k[0,69])))
(k[0,55] | ~k[0,55])
(k25[0,48] | k25[0,50])
(k32[0,67] | k32[0,69])
(k8[0,0] | k8[0,9])
(l[0,10] | (l[0,49] | (l[0,56] | l[0,68])))
(l[0,56] | ~l[0,56])
(l24[0,48] | l24[0,49])
(l31[0,67] | l31[0,68])
(l9[0,0] | l9[0,10])
(m[0,11] | (m[0,76] | m[0,77]))
(m[0,77] | ~m[0,77])
(m10[0,0] | m10[0,11])
(m37[0,72] | m37[0,76])
(n[0,12] | (n[0,75] | n[0,78]))
(n[0,78] | ~n[0,78])
(n11[0,0] | n11[0,12])
(n36[0,72] | n36[0,75])
(o[0,13] | (o[0,74] | o[0,79]))
(o[0,79] | ~o[0,79])
(o12[0,0] | o12[0,13])
(o35[0,72] | o35[0,74])
(p[0,14] | (p[0,73] | p[0,80]))
(p[0,80] | ~p[0,80])
(p13[0,0] | p13[0,14])
(p34[0,72] | p34[0,73])
(x[0,29] | x[0,40])
(x[0,40] | ~x[0,40])
(y[0,48] | y[0,57])
(y[0,57] | ~y[0,57])
(z[0,72] | z[0,81])
(z[0,81] | ~z[0,81])
((~data12[0,58] & (~data15[0,58] & (~data16[0,58] & data17[0,58]))) | (~data12[0,58] & (~data15[0,58] & (~data16[0,58] & ~data17[0,58]))))
((~data2[0,22] & (~e[0,22] & (~data3[0,22] & data4[0,22]))) | (~data2[0,22] & (~e[0,22] & (~data3[0,22] & ~data4[0,22]))))
((~data7[0,41] & (~d[0,41] & (~data8[0,41] & data9[0,41]))) | (~data7[0,41] & (~d[0,41] & (~data8[0,41] & ~data9[0,41]))))
(a0[0,0] <-> b1[0,0])
(a0[0,0] <-> c2[0,0])
(a0[0,0] <-> d[0,0])
(a0[0,0] <-> e[0,0])
(a0[0,0] <-> f3[0,0])
(a0[0,0] <-> g4[0,0])
(a0[0,0] <-> h5[0,0])
(a0[0,0] <-> i6[0,0])
(a0[0,0] <-> j7[0,0])
(a0[0,0] <-> k8[0,0])
(a0[0,0] <-> l9[0,0])
(a0[0,0] <-> m10[0,0])
(a0[0,0] <-> n11[0,0])
(a0[0,0] <-> o12[0,0])
(a0[0,0] <-> p13[0,0])
(arg1[] <-> arg1[0])
(arg1[0] <-> arg1[0,0])
(c14[0,24] <-> a16[0,24])
(c14[0,24] <-> b15[0,24])
(c14[0,24] <-> data1[0,24])
(c21[0,43] <-> a23[0,43])
(c21[0,43] <-> b22[0,43])
(c21[0,43] <-> data6[0,43])
(data13[0,67] <-> data14[0,67])
(data13[0,67] <-> j33[0,67])
(data13[0,67] <-> k32[0,67])
(data13[0,67] <-> l31[0,67])
(i17[0,29] <-> f20[0,29])
(i17[0,29] <-> g19[0,29])
(i17[0,29] <-> h18[0,29])
(i17[0,29] <-> x[0,29])
(i27[0,60] <-> data11[0,60])
(i27[0,60] <-> f30[0,60])
(i27[0,60] <-> g29[0,60])
(i27[0,60] <-> h28[0,60])
(l24[0,48] <-> j26[0,48])
(l24[0,48] <-> k25[0,48])
(l24[0,48] <-> y[0,48])
(p34[0,72] <-> m37[0,72])
(p34[0,72] <-> n36[0,72])
(p34[0,72] <-> o35[0,72])
(p34[0,72] <-> z[0,72])
1
-}

crypt = rget $ (procedure @'[ 'In ] cryptI) :& (procedure @'[ 'Out ] cryptO) :& RNil
  where
    cryptI = \arg1 -> Logic.once $ do
      -- solution: a[0,1] a0[0,0] a16[0,27] a23[0,46] b[0,2] b1[0,0] b15[0,26] b22[0,45] c[0,3] c14[0,25] c2[0,0] c21[0,44] d[0,0] data0[0,20] data1[0,23] data10[0,54] data11[0,59] data12[0,60] data13[0,65] data14[0,66] data15[0,67] data16[0,71] data17[0,72] data2[0,24] data3[0,28] data4[0,29] data5[0,36] data6[0,42] data7[0,43] data8[0,47] data9[0,48] e[0,0] f[0,4] f20[0,33] f3[0,0] f30[0,64] g[0,5] g19[0,32] g29[0,63] g4[0,0] h[0,6] h18[0,31] h28[0,62] h5[0,0] i[0,7] i17[0,30] i27[0,61] i6[0,0] j[0,8] j26[0,51] j33[0,70] j7[0,0] k[0,9] k25[0,50] k32[0,69] k8[0,0] l[0,10] l24[0,49] l31[0,68] l9[0,0] m[0,11] m10[0,0] m37[0,76] n[0,12] n11[0,0] n36[0,75] o[0,13] o12[0,0] o35[0,74] p[0,14] p13[0,0] p34[0,73] x[0,40] y[0,57] z[0,81]
      -- cost: 28
      () <- (do
        (a0:b1:c2:d:e:f3:g4:h5:i6:j7:k8:l9:m10:n11:o12:p13:[]) <- pure arg1
        a <- pure a0
        a16 <- pure a
        a23 <- pure a
        b <- pure b1
        b15 <- pure b
        b22 <- pure b
        c <- pure c2
        c14 <- pure c
        c21 <- pure c
        data0 <- pure 0
        data1 <- pure []
        data10 <- pure 0
        data11 <- pure []
        data13 <- pure 0
        data14 <- pure []
        data16 <- pure 0
        data2 <- pure (c14:b15:a16:data1)
        data3 <- pure 0
        data5 <- pure 0
        data6 <- pure []
        data7 <- pure (c21:b22:a23:data6)
        data8 <- pure 0
        f <- pure f3
        f20 <- pure f
        f30 <- pure f
        g <- pure g4
        g19 <- pure g
        g29 <- pure g
        h <- pure h5
        h18 <- pure h
        h28 <- pure h
        i <- pure i6
        i17 <- pure i
        i27 <- pure i
        data12 <- pure (i27:h28:g29:f30:data11)
        j <- pure j7
        j26 <- pure j
        j33 <- pure j
        k <- pure k8
        k25 <- pure k
        k32 <- pure k
        l <- pure l9
        l24 <- pure l
        l31 <- pure l
        data15 <- pure (data13:l31:k32:j33:data14)
        m <- pure m10
        m37 <- pure m
        n <- pure n11
        n36 <- pure n
        o <- pure o12
        o35 <- pure o
        p <- pure p13
        p34 <- pure p
        guard $ (>) d data0
        guard $ (>) f data5
        guard $ (>) j data10
        () <- runProcedure @'[ 'In ] evenDigit b
        () <- runProcedure @'[ 'In ] evenDigit c
        () <- runProcedure @'[ 'In ] evenDigit d
        () <- runProcedure @'[ 'In ] evenDigit e
        () <- runProcedure @'[ 'In ] evenDigit f
        () <- runProcedure @'[ 'In ] evenDigit h
        () <- runProcedure @'[ 'In ] evenDigit i
        () <- runProcedure @'[ 'In ] evenDigit j
        () <- runProcedure @'[ 'In ] evenDigit l
        () <- runProcedure @'[ 'In ] evenDigit o
        () <- runProcedure @'[ 'In ] evenDigit p
        () <- runProcedure @'[ 'In ] oddDigit a
        () <- runProcedure @'[ 'In ] oddDigit g
        () <- runProcedure @'[ 'In ] oddDigit k
        () <- runProcedure @'[ 'In ] oddDigit m
        () <- runProcedure @'[ 'In ] oddDigit n
        (OneTuple (x)) <- runProcedure @'[ 'Out ] zeros 
        data4 <- pure (i17:h18:g19:f20:x)
        () <- runProcedure @'[ 'In, 'In, 'In, 'In ] mulDigits data2 e data3 data4
        (OneTuple (y)) <- runProcedure @'[ 'Out ] zeros 
        data9 <- pure (l24:k25:j26:y)
        () <- runProcedure @'[ 'In, 'In, 'In, 'In ] mulDigits data7 d data8 data9
        (OneTuple (z)) <- runProcedure @'[ 'Out ] zeros 
        data17 <- pure (p34:o35:n36:m37:z)
        () <- runProcedure @'[ 'In, 'In, 'In, 'In ] sumDigits data12 data15 data16 data17
        pure ()
       )
      pure ()
    
    cryptO = do
      -- solution: a[0,15] a0[0,1] a16[0,27] a23[0,46] arg1[] arg1[0] arg1[0,0] b[0,16] b1[0,2] b15[0,26] b22[0,45] c[0,17] c14[0,25] c2[0,3] c21[0,44] d[0,18] data0[0,20] data1[0,23] data10[0,54] data11[0,59] data12[0,60] data13[0,65] data14[0,66] data15[0,67] data16[0,71] data17[0,58] data2[0,24] data3[0,28] data4[0,22] data5[0,36] data6[0,42] data7[0,43] data8[0,47] data9[0,41] e[0,21] f[0,33] f20[0,29] f3[0,4] f30[0,64] g[0,32] g19[0,29] g29[0,63] g4[0,5] h[0,31] h18[0,29] h28[0,62] h5[0,6] i[0,30] i17[0,29] i27[0,61] i6[0,7] j[0,51] j26[0,48] j33[0,70] j7[0,8] k[0,50] k25[0,48] k32[0,69] k8[0,9] l[0,49] l24[0,48] l31[0,68] l9[0,10] m[0,76] m10[0,11] m37[0,72] n[0,75] n11[0,12] n36[0,72] o[0,74] o12[0,13] o35[0,72] p[0,73] p13[0,14] p34[0,72] x[0,29] y[0,48] z[0,72]
      -- cost: 33
      (arg1) <- (do
        data0 <- pure 0
        data1 <- pure []
        data10 <- pure 0
        data11 <- pure []
        data13 <- pure 0
        data14 <- pure []
        data16 <- pure 0
        data3 <- pure 0
        data5 <- pure 0
        data6 <- pure []
        data8 <- pure 0
        (OneTuple (b)) <- runProcedure @'[ 'Out ] evenDigit 
        b1 <- pure b
        b15 <- pure b
        b22 <- pure b
        (OneTuple (c)) <- runProcedure @'[ 'Out ] evenDigit 
        c14 <- pure c
        c2 <- pure c
        c21 <- pure c
        (OneTuple (d)) <- runProcedure @'[ 'Out ] evenDigit 
        guard $ (>) d data0
        (OneTuple (e)) <- runProcedure @'[ 'Out ] evenDigit 
        (OneTuple (a)) <- runProcedure @'[ 'Out ] oddDigit 
        a0 <- pure a
        a16 <- pure a
        data2 <- pure (c14:b15:a16:data1)
        (OneTuple (data4)) <- runProcedure @'[ 'In, 'In, 'In, 'Out ] mulDigits data2 e data3
        (i17:h18:g19:f20:x) <- pure data4
        f <- pure f20
        f3 <- pure f
        f30 <- pure f
        guard $ (>) f data5
        () <- runProcedure @'[ 'In ] evenDigit f
        g <- pure g19
        g29 <- pure g
        g4 <- pure g
        () <- runProcedure @'[ 'In ] oddDigit g
        h <- pure h18
        h28 <- pure h
        h5 <- pure h
        () <- runProcedure @'[ 'In ] evenDigit h
        i <- pure i17
        i27 <- pure i
        data12 <- pure (i27:h28:g29:f30:data11)
        i6 <- pure i
        () <- runProcedure @'[ 'In ] evenDigit i
        () <- runProcedure @'[ 'In ] zeros x
        a23 <- pure a
        data7 <- pure (c21:b22:a23:data6)
        (OneTuple (data9)) <- runProcedure @'[ 'In, 'In, 'In, 'Out ] mulDigits data7 d data8
        (l24:k25:j26:y) <- pure data9
        j <- pure j26
        j33 <- pure j
        j7 <- pure j
        guard $ (>) j data10
        () <- runProcedure @'[ 'In ] evenDigit j
        k <- pure k25
        k32 <- pure k
        k8 <- pure k
        () <- runProcedure @'[ 'In ] oddDigit k
        l <- pure l24
        l31 <- pure l
        data15 <- pure (data13:l31:k32:j33:data14)
        l9 <- pure l
        () <- runProcedure @'[ 'In ] evenDigit l
        () <- runProcedure @'[ 'In ] zeros y
        (OneTuple (data17)) <- runProcedure @'[ 'In, 'In, 'In, 'Out ] sumDigits data12 data15 data16
        (p34:o35:n36:m37:z) <- pure data17
        m <- pure m37
        m10 <- pure m
        () <- runProcedure @'[ 'In ] oddDigit m
        n <- pure n36
        n11 <- pure n
        () <- runProcedure @'[ 'In ] oddDigit n
        o <- pure o35
        o12 <- pure o
        () <- runProcedure @'[ 'In ] evenDigit o
        p <- pure p34
        p13 <- pure p
        arg1 <- pure (a0:b1:c2:d:e:f3:g4:h5:i6:j7:k8:l9:m10:n11:o12:p13:[])
        () <- runProcedure @'[ 'In ] evenDigit p
        () <- runProcedure @'[ 'In ] zeros z
        pure (arg1)
       )
      pure (OneTuple (arg1))
    