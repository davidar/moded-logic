{-# LANGUAGE DataKinds, FlexibleContexts, NoImplicitPrelude, NoMonomorphismRestriction, TypeApplications #-}
module Append where

import qualified Control.Monad.Logic as Logic
import Control.Monad.Logic.Moded.Prelude

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
      -- solution: b[0,1] b[1,5] h0[1,0] h1[1,2] h[1,3] t[1,0] tb[1,2]
      -- cost: 1
      () <- (do
        b <- pure arg2
        guard $ arg3 == b
        guard $ arg1 == []
        pure ()
       ) <|> (do
        b <- pure arg2
        (h0:t) <- pure arg1
        (h1:tb) <- pure arg3
        h <- pure h1
        guard $ h0 == h
        () <- appendIII t b tb
        pure ()
       )
      pure ()
    
    appendIIO = \arg1 arg2 -> do
      -- solution: arg3[0,2] arg3[0] arg3[1,2] arg3[1] arg3[] b[0,1] b[1,5] h0[1,0] h1[1,3] h[1,1] t[1,0] tb[1,4]
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
      -- solution: arg2[0,1] arg2[0] arg2[1,5] arg2[1] arg2[] b[0,2] b[1,4] h0[1,0] h1[1,2] h[1,1] t[1,0] tb[1,2]
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
      -- solution: arg1[0,0] arg1[0] arg1[1,0] arg1[1] arg1[] b[0,1] b[1,5] h0[1,1] h1[1,2] h[1,3] t[1,4] tb[1,2]
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
      -- solution: arg1[0,0] arg1[0] arg1[1,0] arg1[1] arg1[] arg2[0,1] arg2[0] arg2[1,5] arg2[1] arg2[] b[0,2] b[1,4] h0[1,1] h1[1,2] h[1,3] t[1,4] tb[1,2]
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
    
{- append3/4
append3 a b c abc :- ((append a b ab, append ab c abc)).
constraints:
~append[0]
~(ab[0,0] & ab[0,1])
(ab[0,0] | ab[0,1])
((a[0,0] & (b[0,0] & ~ab[0,0])) | ((a[0,0] & (~b[0,0] & ~ab[0,0])) | ((~a[0,0] & (b[0,0] & ~ab[0,0])) | ((~a[0,0] & (~b[0,0] & ab[0,0])) | (~a[0,0] & (~b[0,0] & ~ab[0,0]))))))
((ab[0,1] & (c[0,1] & ~abc[0,1])) | ((ab[0,1] & (~c[0,1] & ~abc[0,1])) | ((~ab[0,1] & (c[0,1] & ~abc[0,1])) | ((~ab[0,1] & (~c[0,1] & abc[0,1])) | (~ab[0,1] & (~c[0,1] & ~abc[0,1]))))))
(a[] <-> a[0])
(a[0] <-> a[0,0])
(abc[] <-> abc[0])
(abc[0] <-> abc[0,1])
(b[] <-> b[0])
(b[0] <-> b[0,0])
(c[] <-> c[0])
(c[0] <-> c[0,1])
1
-}

append3 = rget $ (procedure @'[ 'In, 'In, 'In, 'In ] append3IIII) :& (procedure @'[ 'In, 'In, 'In, 'Out ] append3IIIO) :& (procedure @'[ 'In, 'In, 'Out, 'In ] append3IIOI) :& (procedure @'[ 'In, 'Out, 'In, 'In ] append3IOII) :& (procedure @'[ 'In, 'Out, 'Out, 'In ] append3IOOI) :& (procedure @'[ 'Out, 'In, 'In, 'In ] append3OIII) :& (procedure @'[ 'Out, 'In, 'Out, 'In ] append3OIOI) :& (procedure @'[ 'Out, 'Out, 'In, 'In ] append3OOII) :& (procedure @'[ 'Out, 'Out, 'Out, 'In ] append3OOOI) :& RNil
  where
    append3IIII = \a b c abc -> Logic.once $ do
      -- solution: ab[0,1]
      -- cost: 3
      () <- (do
        (OneTuple (ab)) <- runProcedure @'[ 'Out, 'In, 'In ] append c abc
        () <- runProcedure @'[ 'In, 'In, 'In ] append a b ab
        pure ()
       )
      pure ()
    
    append3IIIO = \a b c -> do
      -- solution: ab[0,0] abc[0,1] abc[0] abc[]
      -- cost: 4
      (abc) <- (do
        (OneTuple (ab)) <- runProcedure @'[ 'In, 'In, 'Out ] append a b
        (OneTuple (abc)) <- runProcedure @'[ 'In, 'In, 'Out ] append ab c
        pure (abc)
       )
      pure (OneTuple (abc))
    
    append3IIOI = \a b abc -> do
      -- solution: ab[0,0] c[0,1] c[0] c[]
      -- cost: 4
      (c) <- (do
        (OneTuple (ab)) <- runProcedure @'[ 'In, 'In, 'Out ] append a b
        (OneTuple (c)) <- runProcedure @'[ 'In, 'Out, 'In ] append ab abc
        pure (c)
       )
      pure (OneTuple (c))
    
    append3IOII = \a c abc -> do
      -- solution: ab[0,1] b[0,0] b[0] b[]
      -- cost: 4
      (b) <- (do
        (OneTuple (ab)) <- runProcedure @'[ 'Out, 'In, 'In ] append c abc
        (OneTuple (b)) <- runProcedure @'[ 'In, 'Out, 'In ] append a ab
        pure (b)
       )
      pure (OneTuple (b))
    
    append3IOOI = \a abc -> do
      -- solution: ab[0,1] b[0,0] b[0] b[] c[0,1] c[0] c[]
      -- cost: 5
      (b,c) <- (do
        (ab,c) <- runProcedure @'[ 'Out, 'Out, 'In ] append abc
        (OneTuple (b)) <- runProcedure @'[ 'In, 'Out, 'In ] append a ab
        pure (b,c)
       )
      pure (b,c)
    
    append3OIII = \b c abc -> do
      -- solution: a[0,0] a[0] a[] ab[0,1]
      -- cost: 4
      (a) <- (do
        (OneTuple (ab)) <- runProcedure @'[ 'Out, 'In, 'In ] append c abc
        (OneTuple (a)) <- runProcedure @'[ 'Out, 'In, 'In ] append b ab
        pure (a)
       )
      pure (OneTuple (a))
    
    append3OIOI = \b abc -> do
      -- solution: a[0,0] a[0] a[] ab[0,1] c[0,1] c[0] c[]
      -- cost: 5
      (a,c) <- (do
        (ab,c) <- runProcedure @'[ 'Out, 'Out, 'In ] append abc
        (OneTuple (a)) <- runProcedure @'[ 'Out, 'In, 'In ] append b ab
        pure (a,c)
       )
      pure (a,c)
    
    append3OOII = \c abc -> do
      -- solution: a[0,0] a[0] a[] ab[0,1] b[0,0] b[0] b[]
      -- cost: 5
      (a,b) <- (do
        (OneTuple (ab)) <- runProcedure @'[ 'Out, 'In, 'In ] append c abc
        (a,b) <- runProcedure @'[ 'Out, 'Out, 'In ] append ab
        pure (a,b)
       )
      pure (a,b)
    
    append3OOOI = \abc -> do
      -- solution: a[0,0] a[0] a[] ab[0,1] b[0,0] b[0] b[] c[0,1] c[0] c[]
      -- cost: 6
      (a,b,c) <- (do
        (ab,c) <- runProcedure @'[ 'Out, 'Out, 'In ] append abc
        (a,b) <- runProcedure @'[ 'Out, 'Out, 'In ] append ab
        pure (a,b,c)
       )
      pure (a,b,c)
    
{- reverse/2
reverse arg1 arg2 :- ((arg1 = [], arg2 = []); (arg1 = h0:t, h0 = h, reverse t r, append r data1 l, data0 = [], data1 = h1:data0, h1 = h, arg2 = l)).
constraints:
~append[1]
~reverse[1]
~(arg1[1,0] & h0[1,0])
~(arg2[1,7] & l[1,7])
~(data0[1,4] & data0[1,5])
~(data1[1,3] & data1[1,5])
~(data1[1,5] & h1[1,5])
~(h[1,1] & h[1,6])
~(h0[1,0] & h0[1,1])
~(h0[1,1] & h[1,1])
~(h1[1,5] & h1[1,6])
~(h1[1,6] & h[1,6])
~(l[1,3] & l[1,7])
~(r[1,2] & r[1,3])
~(t[1,0] & t[1,2])
(data0[1,4] | data0[1,5])
(data1[1,3] | data1[1,5])
(h[1,1] | h[1,6])
(h0[1,0] | h0[1,1])
(h1[1,5] | h1[1,6])
(l[1,3] | l[1,7])
(r[1,2] | r[1,3])
(t[1,0] | t[1,2])
((r[1,3] & (data1[1,3] & ~l[1,3])) | ((r[1,3] & (~data1[1,3] & ~l[1,3])) | ((~r[1,3] & (data1[1,3] & ~l[1,3])) | ((~r[1,3] & (~data1[1,3] & l[1,3])) | (~r[1,3] & (~data1[1,3] & ~l[1,3]))))))
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg1[0] <-> arg1[0,0])
(arg1[1] <-> arg1[1,0])
(arg2[] <-> arg2[0])
(arg2[] <-> arg2[1])
(arg2[0] <-> arg2[0,1])
(arg2[1] <-> arg2[1,7])
(h0[1,0] <-> t[1,0])
(h1[1,5] <-> data0[1,5])
(r[1,2] <-> arg2[])
(t[1,2] <-> arg1[])
1
-}

reverse = rget $ (procedure @'[ 'In, 'In ] reverseII) :& (procedure @'[ 'In, 'Out ] reverseIO) :& (procedure @'[ 'Out, 'In ] reverseOI) :& RNil
  where
    reverseII = \arg1 arg2 -> Logic.once $ do
      -- solution: data0[1,4] data1[1,5] h0[1,0] h1[1,6] h[1,1] l[1,7] r[1,3] t[1,0]
      -- cost: 3
      () <- (do
        guard $ arg1 == []
        guard $ arg2 == []
        pure ()
       ) <|> (do
        l <- pure arg2
        (h0:t) <- pure arg1
        h <- pure h0
        h1 <- pure h
        data0 <- pure []
        data1 <- pure (h1:data0)
        (OneTuple (r)) <- runProcedure @'[ 'Out, 'In, 'In ] append data1 l
        () <- reverseII t r
        pure ()
       )
      pure ()
    
    reverseIO = \arg1 -> do
      -- solution: arg2[0,1] arg2[0] arg2[1,7] arg2[1] arg2[] data0[1,4] data1[1,5] h0[1,0] h1[1,6] h[1,1] l[1,3] r[1,2] t[1,0]
      -- cost: 4
      (arg2) <- (do
        guard $ arg1 == []
        arg2 <- pure []
        pure (arg2)
       ) <|> (do
        (h0:t) <- pure arg1
        h <- pure h0
        h1 <- pure h
        data0 <- pure []
        data1 <- pure (h1:data0)
        (OneTuple (r)) <- reverseIO t
        (OneTuple (l)) <- runProcedure @'[ 'In, 'In, 'Out ] append r data1
        arg2 <- pure l
        pure (arg2)
       )
      pure (OneTuple (arg2))
    
    reverseOI = \arg2 -> do
      -- solution: arg1[0,0] arg1[0] arg1[1,0] arg1[1] arg1[] data0[1,5] data1[1,3] h0[1,1] h1[1,5] h[1,6] l[1,7] r[1,3] t[1,2]
      -- cost: 5
      (arg1) <- (do
        arg1 <- pure []
        guard $ arg2 == []
        pure (arg1)
       ) <|> (do
        l <- pure arg2
        (r,data1) <- runProcedure @'[ 'Out, 'Out, 'In ] append l
        (h1:data0) <- pure data1
        h <- pure h1
        h0 <- pure h
        guard $ data0 == []
        (OneTuple (t)) <- reverseOI r
        arg1 <- pure (h0:t)
        pure (arg1)
       )
      pure (OneTuple (arg1))
    
{- palindrome/1
palindrome a :- ((reverse a0 a1, a0 = a, a1 = a)).
constraints:
~reverse[0]
~(a[0,1] & a[0,2])
~(a0[0,0] & a0[0,1])
~(a0[0,1] & a[0,1])
~(a1[0,0] & a1[0,2])
~(a1[0,2] & a[0,2])
(a0[0,0] | a0[0,1])
(a1[0,0] | a1[0,2])
((a0[0,0] & ~a1[0,0]) | ((~a0[0,0] & a1[0,0]) | (~a0[0,0] & ~a1[0,0])))
(a[] <-> a[0])
(a[0] <-> (a[0,1] | a[0,2]))
1
-}
--mode ordering failure, cyclic dependency: [0] reverse::I a0::I a1::O -> [2] a1::I = a::O -> [1] a0::O = a::I
--mode ordering failure, cyclic dependency: [0] reverse::I a0::O a1::I -> [1] a0::I = a::O -> [2] a1::O = a::I
palindrome = rget $ (procedure @'[ 'In ] palindromeI) :& RNil
  where
    palindromeI = \a -> Logic.once $ do
      -- solution: a0[0,1] a1[0,2]
      -- cost: 1
      () <- (do
        a0 <- pure a
        a1 <- pure a
        () <- runProcedure @'[ 'In, 'In ] reverse a0 a1
        pure ()
       )
      pure ()
    
{- duplicate/2
duplicate a b :- ((append a0 a1 b, a0 = a, a1 = a)).
constraints:
~append[0]
~(a[0,1] & a[0,2])
~(a0[0,0] & a0[0,1])
~(a0[0,1] & a[0,1])
~(a1[0,0] & a1[0,2])
~(a1[0,2] & a[0,2])
(a0[0,0] | a0[0,1])
(a1[0,0] | a1[0,2])
((a0[0,0] & (a1[0,0] & ~b[0,0])) | ((a0[0,0] & (~a1[0,0] & ~b[0,0])) | ((~a0[0,0] & (a1[0,0] & ~b[0,0])) | ((~a0[0,0] & (~a1[0,0] & b[0,0])) | (~a0[0,0] & (~a1[0,0] & ~b[0,0]))))))
(a[] <-> a[0])
(a[0] <-> (a[0,1] | a[0,2]))
(b[] <-> b[0])
(b[0] <-> b[0,0])
1
-}
--mode ordering failure, cyclic dependency: [0] append::I a0::O a1::I b::I -> [1] a0::I = a::O -> [2] a1::O = a::I
--mode ordering failure, cyclic dependency: [0] append::I a0::I a1::O b::I -> [2] a1::I = a::O -> [1] a0::O = a::I
duplicate = rget $ (procedure @'[ 'In, 'In ] duplicateII) :& (procedure @'[ 'In, 'Out ] duplicateIO) :& (procedure @'[ 'Out, 'In ] duplicateOI) :& RNil
  where
    duplicateII = \a b -> Logic.once $ do
      -- solution: a0[0,1] a1[0,2]
      -- cost: 1
      () <- (do
        a0 <- pure a
        a1 <- pure a
        () <- runProcedure @'[ 'In, 'In, 'In ] append a0 a1 b
        pure ()
       )
      pure ()
    
    duplicateIO = \a -> do
      -- solution: a0[0,1] a1[0,2] b[0,0] b[0] b[]
      -- cost: 2
      (b) <- (do
        a0 <- pure a
        a1 <- pure a
        (OneTuple (b)) <- runProcedure @'[ 'In, 'In, 'Out ] append a0 a1
        pure (b)
       )
      pure (OneTuple (b))
    
    duplicateOI = \b -> do
      -- solution: a0[0,0] a1[0,0] a[0,2] a[0] a[]
      -- cost: 3
      (a) <- (do
        (a0,a1) <- runProcedure @'[ 'Out, 'Out, 'In ] append b
        a <- pure a1
        guard $ a0 == a
        pure (a)
       )
      pure (OneTuple (a))
    
{- classify/2
classify xs r :- ((if (palindrome xs) then (r = Just data0, data0 = []) else (if (duplicate h xs) then (r = Just h) else (r = Nothing)))).
constraints:
h[0,0,2,0,0]
~duplicate[0,0,2,0,0]
~h[0,0,2,0,1,0]
~palindrome[0,0,0]
~xs[0,0,0,0]
~xs[0,0,2]
~xs[0,0,2,0]
~xs[0,0,2,0,0,0]
~(data0[0,0,1,0] & data0[0,0,1,1])
~(r[0,0,1,0] & data0[0,0,1,0])
~(r[0,0,2,0,1,0] & h[0,0,2,0,1,0])
(data0[0,0,1,0] | data0[0,0,1,1])
((h[0,0,2,0,0,0] & ~xs[0,0,2,0,0,0]) | ((~h[0,0,2,0,0,0] & xs[0,0,2,0,0,0]) | (~h[0,0,2,0,0,0] & ~xs[0,0,2,0,0,0])))
(duplicate[0] <-> duplicate[0,0])
(duplicate[0,0] <-> duplicate[0,0,2])
(duplicate[0,0,2] <-> duplicate[0,0,2,0])
(duplicate[0,0,2,0] <-> duplicate[0,0,2,0,0])
(h[0,0,2,0,0] <-> h[0,0,2,0,0,0])
(palindrome[0] <-> palindrome[0,0])
(palindrome[0,0] <-> palindrome[0,0,0])
(r[] <-> r[0])
(r[0] <-> r[0,0])
(r[0,0] <-> (r[0,0,1] | r[0,0,2]))
(r[0,0,1] <-> r[0,0,1,0])
(r[0,0,1] <-> r[0,0,2])
(r[0,0,2] <-> r[0,0,2,0])
(r[0,0,2,0] <-> (r[0,0,2,0,1] | r[0,0,2,0,2]))
(r[0,0,2,0,1] <-> r[0,0,2,0,1,0])
(r[0,0,2,0,1] <-> r[0,0,2,0,2])
(r[0,0,2,0,2] <-> r[0,0,2,0,2,0])
(xs[] <-> xs[0])
(xs[0] <-> xs[0,0])
(xs[0,0] <-> xs[0,0,2])
(xs[0,0,2] <-> xs[0,0,2,0])
1
-}

classify = rget $ (procedure @'[ 'In, 'In ] classifyII) :& (procedure @'[ 'In, 'Out ] classifyIO) :& RNil
  where
    classifyII = \xs r -> Logic.once $ do
      -- solution: data0[0,0,1,1] h[0,0,2,0,0,0] h[0,0,2,0,0]
      -- cost: 3
      () <- (do
        () <- Logic.ifte ((do
          () <- runProcedure @'[ 'In ] palindrome xs
          pure ()
         )) (\() -> (do
          data0 <- pure []
          guard $ r == (Just data0)
          pure ()
         )) ((do
          () <- Logic.ifte ((do
            (OneTuple (h)) <- runProcedure @'[ 'Out, 'In ] duplicate xs
            pure (h)
           )) (\(h) -> (do
            guard $ r == (Just h)
            pure ()
           )) ((do
            guard $ r == Nothing
            pure ()
           ))
          pure ()
         ))
        pure ()
       )
      pure ()
    
    classifyIO = \xs -> do
      -- solution: data0[0,0,1,1] h[0,0,2,0,0,0] h[0,0,2,0,0] r[0,0,1,0] r[0,0,1] r[0,0,2,0,1,0] r[0,0,2,0,1] r[0,0,2,0,2,0] r[0,0,2,0,2] r[0,0,2,0] r[0,0,2] r[0,0] r[0] r[]
      -- cost: 3
      (r) <- (do
        (r) <- Logic.ifte ((do
          () <- runProcedure @'[ 'In ] palindrome xs
          pure ()
         )) (\() -> (do
          data0 <- pure []
          r <- pure (Just data0)
          pure (r)
         )) ((do
          (r) <- Logic.ifte ((do
            (OneTuple (h)) <- runProcedure @'[ 'Out, 'In ] duplicate xs
            pure (h)
           )) (\(h) -> (do
            r <- pure (Just h)
            pure (r)
           )) ((do
            r <- pure Nothing
            pure (r)
           ))
          pure (r)
         ))
        pure (r)
       )
      pure (OneTuple (r))
    
{- delete/3
delete arg1 arg2 arg3 :- ((arg2 = h:t, arg1 = h, arg3 = t); (arg2 = h0:t, h0 = h, arg3 = h1:r, h1 = h, delete x t r, arg1 = x)).
constraints:
~delete[1]
~(arg1[0,1] & h[0,1])
~(arg1[1,5] & x[1,5])
~(arg2[0,0] & h[0,0])
~(arg2[1,0] & h0[1,0])
~(arg3[0,2] & t[0,2])
~(arg3[1,2] & h1[1,2])
~(h[0,0] & h[0,1])
~(h[1,1] & h[1,3])
~(h0[1,0] & h0[1,1])
~(h0[1,1] & h[1,1])
~(h1[1,2] & h1[1,3])
~(h1[1,3] & h[1,3])
~(r[1,2] & r[1,4])
~(t[0,0] & t[0,2])
~(t[1,0] & t[1,4])
~(x[1,4] & x[1,5])
(h[0,0] | h[0,1])
(h[1,1] | h[1,3])
(h0[1,0] | h0[1,1])
(h1[1,2] | h1[1,3])
(r[1,2] | r[1,4])
(t[0,0] | t[0,2])
(t[1,0] | t[1,4])
(x[1,4] | x[1,5])
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg1[0] <-> arg1[0,1])
(arg1[1] <-> arg1[1,5])
(arg2[] <-> arg2[0])
(arg2[] <-> arg2[1])
(arg2[0] <-> arg2[0,0])
(arg2[1] <-> arg2[1,0])
(arg3[] <-> arg3[0])
(arg3[] <-> arg3[1])
(arg3[0] <-> arg3[0,2])
(arg3[1] <-> arg3[1,2])
(h[0,0] <-> t[0,0])
(h0[1,0] <-> t[1,0])
(h1[1,2] <-> r[1,2])
(r[1,4] <-> arg3[])
(t[1,4] <-> arg2[])
(x[1,4] <-> arg1[])
1
-}

delete = rget $ (procedure @'[ 'In, 'In, 'In ] deleteIII) :& (procedure @'[ 'In, 'In, 'Out ] deleteIIO) :& (procedure @'[ 'In, 'Out, 'In ] deleteIOI) :& (procedure @'[ 'Out, 'In, 'In ] deleteOII) :& (procedure @'[ 'Out, 'In, 'Out ] deleteOIO) :& RNil
  where
    deleteIII = \arg1 arg2 arg3 -> Logic.once $ do
      -- solution: h0[1,0] h1[1,2] h[0,1] h[1,3] r[1,2] t[0,2] t[1,0] x[1,5]
      -- cost: 1
      () <- (do
        h <- pure arg1
        t <- pure arg3
        guard $ arg2 == (h:t)
        pure ()
       ) <|> (do
        x <- pure arg1
        (h0:t) <- pure arg2
        (h1:r) <- pure arg3
        h <- pure h1
        guard $ h0 == h
        () <- deleteIII x t r
        pure ()
       )
      pure ()
    
    deleteIIO = \arg1 arg2 -> do
      -- solution: arg3[0,2] arg3[0] arg3[1,2] arg3[1] arg3[] h0[1,0] h1[1,3] h[0,0] h[1,1] r[1,4] t[0,0] t[1,0] x[1,5]
      -- cost: 2
      (arg3) <- (do
        (h:t) <- pure arg2
        guard $ arg1 == h
        arg3 <- pure t
        pure (arg3)
       ) <|> (do
        x <- pure arg1
        (h0:t) <- pure arg2
        h <- pure h0
        h1 <- pure h
        (OneTuple (r)) <- deleteIIO x t
        arg3 <- pure (h1:r)
        pure (arg3)
       )
      pure (OneTuple (arg3))
    
    deleteIOI = \arg1 arg3 -> do
      -- solution: arg2[0,0] arg2[0] arg2[1,0] arg2[1] arg2[] h0[1,1] h1[1,2] h[0,1] h[1,3] r[1,2] t[0,2] t[1,4] x[1,5]
      -- cost: 2
      (arg2) <- (do
        h <- pure arg1
        t <- pure arg3
        arg2 <- pure (h:t)
        pure (arg2)
       ) <|> (do
        x <- pure arg1
        (h1:r) <- pure arg3
        h <- pure h1
        h0 <- pure h
        (OneTuple (t)) <- deleteIOI x r
        arg2 <- pure (h0:t)
        pure (arg2)
       )
      pure (OneTuple (arg2))
    
    deleteOII = \arg2 arg3 -> do
      -- solution: arg1[0,1] arg1[0] arg1[1,5] arg1[1] arg1[] h0[1,0] h1[1,2] h[0,0] h[1,3] r[1,2] t[0,0] t[1,0] x[1,4]
      -- cost: 2
      (arg1) <- (do
        (h:t) <- pure arg2
        arg1 <- pure h
        guard $ arg3 == t
        pure (arg1)
       ) <|> (do
        (h0:t) <- pure arg2
        (h1:r) <- pure arg3
        h <- pure h1
        guard $ h0 == h
        (OneTuple (x)) <- deleteOII t r
        arg1 <- pure x
        pure (arg1)
       )
      pure (OneTuple (arg1))
    
    deleteOIO = \arg2 -> do
      -- solution: arg1[0,1] arg1[0] arg1[1,5] arg1[1] arg1[] arg3[0,2] arg3[0] arg3[1,2] arg3[1] arg3[] h0[1,0] h1[1,3] h[0,0] h[1,1] r[1,4] t[0,0] t[1,0] x[1,4]
      -- cost: 3
      (arg1,arg3) <- (do
        (h:t) <- pure arg2
        arg1 <- pure h
        arg3 <- pure t
        pure (arg1,arg3)
       ) <|> (do
        (h0:t) <- pure arg2
        h <- pure h0
        h1 <- pure h
        (x,r) <- deleteOIO t
        arg1 <- pure x
        arg3 <- pure (h1:r)
        pure (arg1,arg3)
       )
      pure (arg1,arg3)
    
{- perm/2
perm arg1 arg2 :- ((arg1 = [], arg2 = []); (arg2 = h:t, delete h xs ys, perm ys t, arg1 = xs)).
constraints:
~delete[1]
~perm[1]
~(arg1[1,3] & xs[1,3])
~(arg2[1,0] & h[1,0])
~(h[1,0] & h[1,1])
~(t[1,0] & t[1,2])
~(xs[1,1] & xs[1,3])
~(ys[1,1] & ys[1,2])
(h[1,0] | h[1,1])
(t[1,0] | t[1,2])
(xs[1,1] | xs[1,3])
(ys[1,1] | ys[1,2])
((h[1,1] & (~xs[1,1] & ys[1,1])) | ((h[1,1] & (~xs[1,1] & ~ys[1,1])) | ((~h[1,1] & (xs[1,1] & ~ys[1,1])) | ((~h[1,1] & (~xs[1,1] & ys[1,1])) | (~h[1,1] & (~xs[1,1] & ~ys[1,1]))))))
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg1[0] <-> arg1[0,0])
(arg1[1] <-> arg1[1,3])
(arg2[] <-> arg2[0])
(arg2[] <-> arg2[1])
(arg2[0] <-> arg2[0,1])
(arg2[1] <-> arg2[1,0])
(h[1,0] <-> t[1,0])
(t[1,2] <-> arg2[])
(ys[1,2] <-> arg1[])
1
-}

perm = rget $ (procedure @'[ 'In, 'In ] permII) :& (procedure @'[ 'In, 'Out ] permIO) :& (procedure @'[ 'Out, 'In ] permOI) :& RNil
  where
    permII = \arg1 arg2 -> Logic.once $ do
      -- solution: h[1,0] t[1,0] xs[1,3] ys[1,1]
      -- cost: 3
      () <- (do
        guard $ arg1 == []
        guard $ arg2 == []
        pure ()
       ) <|> (do
        xs <- pure arg1
        (h:t) <- pure arg2
        (OneTuple (ys)) <- runProcedure @'[ 'In, 'In, 'Out ] delete h xs
        () <- permII ys t
        pure ()
       )
      pure ()
    
    permIO = \arg1 -> do
      -- solution: arg2[0,1] arg2[0] arg2[1,0] arg2[1] arg2[] h[1,1] t[1,2] xs[1,3] ys[1,1]
      -- cost: 5
      (arg2) <- (do
        guard $ arg1 == []
        arg2 <- pure []
        pure (arg2)
       ) <|> (do
        xs <- pure arg1
        (h,ys) <- runProcedure @'[ 'Out, 'In, 'Out ] delete xs
        (OneTuple (t)) <- permIO ys
        arg2 <- pure (h:t)
        pure (arg2)
       )
      pure (OneTuple (arg2))
    
    permOI = \arg2 -> do
      -- solution: arg1[0,0] arg1[0] arg1[1,3] arg1[1] arg1[] h[1,0] t[1,0] xs[1,1] ys[1,2]
      -- cost: 4
      (arg1) <- (do
        arg1 <- pure []
        guard $ arg2 == []
        pure (arg1)
       ) <|> (do
        (h:t) <- pure arg2
        (OneTuple (ys)) <- permOI t
        (OneTuple (xs)) <- runProcedure @'[ 'In, 'Out, 'In ] delete h ys
        arg1 <- pure xs
        pure (arg1)
       )
      pure (OneTuple (arg1))
    
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
      -- solution: x[0,1]
      -- cost: 0
      () <- (do
        x <- pure arg2
        guard $ arg1 == x
        pure ()
       )
      pure ()
    
    idIO = \arg1 -> do
      -- solution: arg2[0,1] arg2[0] arg2[] x[0,0]
      -- cost: 0
      (arg2) <- (do
        x <- pure arg1
        arg2 <- pure x
        pure (arg2)
       )
      pure (OneTuple (arg2))
    
    idOI = \arg2 -> do
      -- solution: arg1[0,0] arg1[0] arg1[] x[0,1]
      -- cost: 0
      (arg1) <- (do
        x <- pure arg2
        arg1 <- pure x
        pure (arg1)
       )
      pure (OneTuple (arg1))
    