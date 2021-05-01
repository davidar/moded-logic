{-# LANGUAGE DataKinds, FlexibleContexts, NoImplicitPrelude, NoMonomorphismRestriction, TypeApplications #-}
module DCG where

import qualified Control.Monad.Logic as Logic
import Control.Monad.Logic.Moded.Prelude

data Tree = S Tree Tree | NP String String | VP String Tree deriving (Eq, Ord, Show)
{- append/3
append arg1 b arg3 :- ((arg1 = [], arg3 = b); (arg1 = h0:t, h0 = h, arg3 = h1:tb, h1 = h, append t b tb)).
constraints:
~(arg1[1,0] & h0[1,0])
~(arg3[0,1] & b[0,1])
~(arg3[1,2] & h1[1,2])
~(h[1,1] & h[1,3])
~(h0[1,0] & h0[1,1])
~(h0[1,1] & h[1,1])
~(h1[1,2] & h1[1,3])
~(h1[1,3] & h[1,3])
~(t[1,0] & t[1,4])
~(tb[1,2] & tb[1,4])
(h[1,1] | h[1,3])
(h0[1,0] | h0[1,1])
(h1[1,2] | h1[1,3])
(t[1,0] | t[1,4])
(tb[1,2] | tb[1,4])
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg1[0] <-> arg1[0,0])
(arg1[1] <-> arg1[1,0])
(arg3[] <-> arg3[0])
(arg3[] <-> arg3[1])
(arg3[0] <-> arg3[0,1])
(arg3[1] <-> arg3[1,2])
(b[] <-> b[0])
(b[] <-> b[1])
(b[0] <-> b[0,1])
(b[1] <-> b[1,4])
(b[1,4] <-> b[])
(h0[1,0] <-> t[1,0])
(h1[1,2] <-> tb[1,2])
(t[1,4] <-> arg1[])
(tb[1,4] <-> arg3[])
1
-}

append = rget $ (procedure @'[ 'In, 'In, 'In ] appendIII) :& (procedure @'[ 'In, 'In, 'Out ] appendIIO) :& (procedure @'[ 'In, 'Out, 'In ] appendIOI) :& (procedure @'[ 'Out, 'In, 'In ] appendOII) :& (procedure @'[ 'Out, 'Out, 'In ] appendOOI) :& RNil
  where
    appendIII = \arg1 b arg3 -> Logic.once $ do
      -- solution: h[1,1] h0[1,0] h1[1,2] t[1,0] tb[1,2] ~arg1[] ~arg1[0] ~arg1[0,0] ~arg1[1] ~arg1[1,0] ~arg3[] ~arg3[0] ~arg3[0,1] ~arg3[1] ~arg3[1,2] ~b[] ~b[0] ~b[0,1] ~b[1] ~b[1,4] ~h[1,3] ~h0[1,1] ~h1[1,3] ~t[1,4] ~tb[1,4]
      -- cost: 1
      () <- (do
        guard $ arg3 == b
        guard $ arg1 == []
        pure ()
       ) <|> (do
        (h0:t) <- pure arg1
        h <- pure h0
        (h1:tb) <- pure arg3
        guard $ h1 == h
        () <- appendIII t b tb
        pure ()
       )
      pure ()
    
    appendIIO = \arg1 b -> do
      -- solution: arg3[] arg3[0] arg3[0,1] arg3[1] arg3[1,2] h[1,1] h0[1,0] h1[1,3] t[1,0] tb[1,4] ~arg1[] ~arg1[0] ~arg1[0,0] ~arg1[1] ~arg1[1,0] ~b[] ~b[0] ~b[0,1] ~b[1] ~b[1,4] ~h[1,3] ~h0[1,1] ~h1[1,2] ~t[1,4] ~tb[1,2]
      -- cost: 2
      (arg3) <- (do
        arg3 <- pure b
        guard $ arg1 == []
        pure (arg3)
       ) <|> (do
        (h0:t) <- pure arg1
        h <- pure h0
        h1 <- pure h
        (OneTuple (tb)) <- appendIIO t b
        arg3 <- pure (h1:tb)
        pure (arg3)
       )
      pure (OneTuple (arg3))
    
    appendIOI = \arg1 arg3 -> do
      -- solution: b[] b[0] b[0,1] b[1] b[1,4] h[1,1] h0[1,0] h1[1,2] t[1,0] tb[1,2] ~arg1[] ~arg1[0] ~arg1[0,0] ~arg1[1] ~arg1[1,0] ~arg3[] ~arg3[0] ~arg3[0,1] ~arg3[1] ~arg3[1,2] ~h[1,3] ~h0[1,1] ~h1[1,3] ~t[1,4] ~tb[1,4]
      -- cost: 2
      (b) <- (do
        b <- pure arg3
        guard $ arg1 == []
        pure (b)
       ) <|> (do
        (h0:t) <- pure arg1
        h <- pure h0
        (h1:tb) <- pure arg3
        guard $ h1 == h
        (OneTuple (b)) <- appendIOI t tb
        pure (b)
       )
      pure (OneTuple (b))
    
    appendOII = \b arg3 -> do
      -- solution: arg1[] arg1[0] arg1[0,0] arg1[1] arg1[1,0] h[1,3] h0[1,1] h1[1,2] t[1,4] tb[1,2] ~arg3[] ~arg3[0] ~arg3[0,1] ~arg3[1] ~arg3[1,2] ~b[] ~b[0] ~b[0,1] ~b[1] ~b[1,4] ~h[1,1] ~h0[1,0] ~h1[1,3] ~t[1,0] ~tb[1,4]
      -- cost: 2
      (arg1) <- (do
        guard $ arg3 == b
        arg1 <- pure []
        pure (arg1)
       ) <|> (do
        (h1:tb) <- pure arg3
        h <- pure h1
        h0 <- pure h
        (OneTuple (t)) <- appendOII b tb
        arg1 <- pure (h0:t)
        pure (arg1)
       )
      pure (OneTuple (arg1))
    
    appendOOI = \arg3 -> do
      -- solution: arg1[] arg1[0] arg1[0,0] arg1[1] arg1[1,0] b[] b[0] b[0,1] b[1] b[1,4] h[1,3] h0[1,1] h1[1,2] t[1,4] tb[1,2] ~arg3[] ~arg3[0] ~arg3[0,1] ~arg3[1] ~arg3[1,2] ~h[1,1] ~h0[1,0] ~h1[1,3] ~t[1,0] ~tb[1,4]
      -- cost: 3
      (arg1,b) <- (do
        b <- pure arg3
        arg1 <- pure []
        pure (arg1,b)
       ) <|> (do
        (h1:tb) <- pure arg3
        h <- pure h1
        h0 <- pure h
        (t,b) <- appendOOI tb
        arg1 <- pure (h0:t)
        pure (arg1,b)
       )
      pure (arg1,b)
    
{- compose'/6
compose' f x g y a z :- ((g y a b, f x b z)).
constraints:
~(b[0,0] & b[0,1])
(b[0,0] | b[0,1])
(a[] <-> a[0])
(a[0] <-> a[0,0])
(a[0,0] <-> g(2))
(b[0,0] <-> g(3))
(b[0,1] <-> f(2))
(x[] <-> x[0])
(x[0] <-> x[0,1])
(x[0,1] <-> f(1))
(y[] <-> y[0])
(y[0] <-> y[0,0])
(y[0,0] <-> g(1))
(z[] <-> z[0])
(z[0] <-> z[0,1])
(z[0,1] <-> f(3))
1
-}

compose' = rget $ (procedure @'[ 'PredMode '[ 'In, 'In, 'In ], 'In, 'PredMode '[ 'In, 'In, 'Out ], 'In, 'In, 'In ] compose'P3IIIIP3IIOIII) :& (procedure @'[ 'PredMode '[ 'In, 'In, 'In ], 'In, 'PredMode '[ 'In, 'Out, 'Out ], 'In, 'Out, 'In ] compose'P3IIIIP3IOOIOI) :& (procedure @'[ 'PredMode '[ 'In, 'In, 'In ], 'In, 'PredMode '[ 'Out, 'In, 'Out ], 'Out, 'In, 'In ] compose'P3IIIIP3OIOOII) :& (procedure @'[ 'PredMode '[ 'In, 'In, 'In ], 'In, 'PredMode '[ 'Out, 'Out, 'Out ], 'Out, 'Out, 'In ] compose'P3IIIIP3OOOOOI) :& (procedure @'[ 'PredMode '[ 'In, 'In, 'Out ], 'In, 'PredMode '[ 'In, 'In, 'Out ], 'In, 'In, 'Out ] compose'P3IIOIP3IIOIIO) :& (procedure @'[ 'PredMode '[ 'In, 'In, 'Out ], 'In, 'PredMode '[ 'In, 'Out, 'Out ], 'In, 'Out, 'Out ] compose'P3IIOIP3IOOIOO) :& (procedure @'[ 'PredMode '[ 'In, 'In, 'Out ], 'In, 'PredMode '[ 'Out, 'In, 'Out ], 'Out, 'In, 'Out ] compose'P3IIOIP3OIOOIO) :& (procedure @'[ 'PredMode '[ 'In, 'In, 'Out ], 'In, 'PredMode '[ 'Out, 'Out, 'Out ], 'Out, 'Out, 'Out ] compose'P3IIOIP3OOOOOO) :& (procedure @'[ 'PredMode '[ 'In, 'Out, 'In ], 'In, 'PredMode '[ 'In, 'In, 'In ], 'In, 'In, 'In ] compose'P3IOIIP3IIIIII) :& (procedure @'[ 'PredMode '[ 'In, 'Out, 'In ], 'In, 'PredMode '[ 'In, 'Out, 'In ], 'In, 'Out, 'In ] compose'P3IOIIP3IOIIOI) :& (procedure @'[ 'PredMode '[ 'In, 'Out, 'In ], 'In, 'PredMode '[ 'Out, 'In, 'In ], 'Out, 'In, 'In ] compose'P3IOIIP3OIIOII) :& (procedure @'[ 'PredMode '[ 'In, 'Out, 'In ], 'In, 'PredMode '[ 'Out, 'Out, 'In ], 'Out, 'Out, 'In ] compose'P3IOIIP3OOIOOI) :& (procedure @'[ 'PredMode '[ 'In, 'Out, 'Out ], 'In, 'PredMode '[ 'In, 'In, 'In ], 'In, 'In, 'Out ] compose'P3IOOIP3IIIIIO) :& (procedure @'[ 'PredMode '[ 'In, 'Out, 'Out ], 'In, 'PredMode '[ 'In, 'Out, 'In ], 'In, 'Out, 'Out ] compose'P3IOOIP3IOIIOO) :& (procedure @'[ 'PredMode '[ 'In, 'Out, 'Out ], 'In, 'PredMode '[ 'Out, 'In, 'In ], 'Out, 'In, 'Out ] compose'P3IOOIP3OIIOIO) :& (procedure @'[ 'PredMode '[ 'In, 'Out, 'Out ], 'In, 'PredMode '[ 'Out, 'Out, 'In ], 'Out, 'Out, 'Out ] compose'P3IOOIP3OOIOOO) :& (procedure @'[ 'PredMode '[ 'Out, 'In, 'In ], 'Out, 'PredMode '[ 'In, 'In, 'Out ], 'In, 'In, 'In ] compose'P3OIIOP3IIOIII) :& (procedure @'[ 'PredMode '[ 'Out, 'In, 'In ], 'Out, 'PredMode '[ 'In, 'Out, 'Out ], 'In, 'Out, 'In ] compose'P3OIIOP3IOOIOI) :& (procedure @'[ 'PredMode '[ 'Out, 'In, 'In ], 'Out, 'PredMode '[ 'Out, 'In, 'Out ], 'Out, 'In, 'In ] compose'P3OIIOP3OIOOII) :& (procedure @'[ 'PredMode '[ 'Out, 'In, 'In ], 'Out, 'PredMode '[ 'Out, 'Out, 'Out ], 'Out, 'Out, 'In ] compose'P3OIIOP3OOOOOI) :& (procedure @'[ 'PredMode '[ 'Out, 'In, 'Out ], 'Out, 'PredMode '[ 'In, 'In, 'Out ], 'In, 'In, 'Out ] compose'P3OIOOP3IIOIIO) :& (procedure @'[ 'PredMode '[ 'Out, 'In, 'Out ], 'Out, 'PredMode '[ 'In, 'Out, 'Out ], 'In, 'Out, 'Out ] compose'P3OIOOP3IOOIOO) :& (procedure @'[ 'PredMode '[ 'Out, 'In, 'Out ], 'Out, 'PredMode '[ 'Out, 'In, 'Out ], 'Out, 'In, 'Out ] compose'P3OIOOP3OIOOIO) :& (procedure @'[ 'PredMode '[ 'Out, 'In, 'Out ], 'Out, 'PredMode '[ 'Out, 'Out, 'Out ], 'Out, 'Out, 'Out ] compose'P3OIOOP3OOOOOO) :& (procedure @'[ 'PredMode '[ 'Out, 'Out, 'In ], 'Out, 'PredMode '[ 'In, 'In, 'In ], 'In, 'In, 'In ] compose'P3OOIOP3IIIIII) :& (procedure @'[ 'PredMode '[ 'Out, 'Out, 'In ], 'Out, 'PredMode '[ 'In, 'Out, 'In ], 'In, 'Out, 'In ] compose'P3OOIOP3IOIIOI) :& (procedure @'[ 'PredMode '[ 'Out, 'Out, 'In ], 'Out, 'PredMode '[ 'Out, 'In, 'In ], 'Out, 'In, 'In ] compose'P3OOIOP3OIIOII) :& (procedure @'[ 'PredMode '[ 'Out, 'Out, 'In ], 'Out, 'PredMode '[ 'Out, 'Out, 'In ], 'Out, 'Out, 'In ] compose'P3OOIOP3OOIOOI) :& (procedure @'[ 'PredMode '[ 'Out, 'Out, 'Out ], 'Out, 'PredMode '[ 'In, 'In, 'In ], 'In, 'In, 'Out ] compose'P3OOOOP3IIIIIO) :& (procedure @'[ 'PredMode '[ 'Out, 'Out, 'Out ], 'Out, 'PredMode '[ 'In, 'Out, 'In ], 'In, 'Out, 'Out ] compose'P3OOOOP3IOIIOO) :& (procedure @'[ 'PredMode '[ 'Out, 'Out, 'Out ], 'Out, 'PredMode '[ 'Out, 'In, 'In ], 'Out, 'In, 'Out ] compose'P3OOOOP3OIIOIO) :& (procedure @'[ 'PredMode '[ 'Out, 'Out, 'Out ], 'Out, 'PredMode '[ 'Out, 'Out, 'In ], 'Out, 'Out, 'Out ] compose'P3OOOOP3OOIOOO) :& RNil
  where
    compose'P3IIIIP3IIOIII = \f x g y a z -> Logic.once $ do
      -- solution: b[0,0] g(3) ~a[] ~a[0] ~a[0,0] ~b[0,1] ~x[] ~x[0] ~x[0,1] ~y[] ~y[0] ~y[0,0] ~z[] ~z[0] ~z[0,1] ~f(1) ~f(2) ~f(3) ~g(1) ~g(2)
      -- cost: 3
      () <- (do
        (OneTuple (b)) <- runProcedure g y a
        () <- runProcedure f x b z
        pure ()
       )
      pure ()
    
    compose'P3IIIIP3IOOIOI = \f x g y z -> do
      -- solution: a[] a[0] a[0,0] b[0,0] g(2) g(3) ~b[0,1] ~x[] ~x[0] ~x[0,1] ~y[] ~y[0] ~y[0,0] ~z[] ~z[0] ~z[0,1] ~f(1) ~f(2) ~f(3) ~g(1)
      -- cost: 4
      (a) <- (do
        (a,b) <- runProcedure g y
        () <- runProcedure f x b z
        pure (a)
       )
      pure (OneTuple (a))
    
    compose'P3IIIIP3OIOOII = \f x g a z -> do
      -- solution: b[0,0] y[] y[0] y[0,0] g(1) g(3) ~a[] ~a[0] ~a[0,0] ~b[0,1] ~x[] ~x[0] ~x[0,1] ~z[] ~z[0] ~z[0,1] ~f(1) ~f(2) ~f(3) ~g(2)
      -- cost: 4
      (y) <- (do
        (y,b) <- runProcedure g a
        () <- runProcedure f x b z
        pure (y)
       )
      pure (OneTuple (y))
    
    compose'P3IIIIP3OOOOOI = \f x g z -> do
      -- solution: a[] a[0] a[0,0] b[0,0] y[] y[0] y[0,0] g(1) g(2) g(3) ~b[0,1] ~x[] ~x[0] ~x[0,1] ~z[] ~z[0] ~z[0,1] ~f(1) ~f(2) ~f(3)
      -- cost: 5
      (a,y) <- (do
        (y,a,b) <- runProcedure g 
        () <- runProcedure f x b z
        pure (a,y)
       )
      pure (y,a)
    
    compose'P3IIOIP3IIOIIO = \f x g y a -> do
      -- solution: b[0,0] z[] z[0] z[0,1] f(3) g(3) ~a[] ~a[0] ~a[0,0] ~b[0,1] ~x[] ~x[0] ~x[0,1] ~y[] ~y[0] ~y[0,0] ~f(1) ~f(2) ~g(1) ~g(2)
      -- cost: 4
      (z) <- (do
        (OneTuple (b)) <- runProcedure g y a
        (OneTuple (z)) <- runProcedure f x b
        pure (z)
       )
      pure (OneTuple (z))
    
    compose'P3IIOIP3IOOIOO = \f x g y -> do
      -- solution: a[] a[0] a[0,0] b[0,0] z[] z[0] z[0,1] f(3) g(2) g(3) ~b[0,1] ~x[] ~x[0] ~x[0,1] ~y[] ~y[0] ~y[0,0] ~f(1) ~f(2) ~g(1)
      -- cost: 5
      (a,z) <- (do
        (a,b) <- runProcedure g y
        (OneTuple (z)) <- runProcedure f x b
        pure (a,z)
       )
      pure (a,z)
    
    compose'P3IIOIP3OIOOIO = \f x g a -> do
      -- solution: b[0,0] y[] y[0] y[0,0] z[] z[0] z[0,1] f(3) g(1) g(3) ~a[] ~a[0] ~a[0,0] ~b[0,1] ~x[] ~x[0] ~x[0,1] ~f(1) ~f(2) ~g(2)
      -- cost: 5
      (y,z) <- (do
        (y,b) <- runProcedure g a
        (OneTuple (z)) <- runProcedure f x b
        pure (y,z)
       )
      pure (y,z)
    
    compose'P3IIOIP3OOOOOO = \f x g -> do
      -- solution: a[] a[0] a[0,0] b[0,0] y[] y[0] y[0,0] z[] z[0] z[0,1] f(3) g(1) g(2) g(3) ~b[0,1] ~x[] ~x[0] ~x[0,1] ~f(1) ~f(2)
      -- cost: 6
      (a,y,z) <- (do
        (y,a,b) <- runProcedure g 
        (OneTuple (z)) <- runProcedure f x b
        pure (a,y,z)
       )
      pure (y,a,z)
    
    compose'P3IOIIP3IIIIII = \f x g y a z -> Logic.once $ do
      -- solution: b[0,1] f(2) ~a[] ~a[0] ~a[0,0] ~b[0,0] ~x[] ~x[0] ~x[0,1] ~y[] ~y[0] ~y[0,0] ~z[] ~z[0] ~z[0,1] ~f(1) ~f(3) ~g(1) ~g(2) ~g(3)
      -- cost: 3
      () <- (do
        (OneTuple (b)) <- runProcedure f x z
        () <- runProcedure g y a b
        pure ()
       )
      pure ()
    
    compose'P3IOIIP3IOIIOI = \f x g y z -> do
      -- solution: a[] a[0] a[0,0] b[0,1] f(2) g(2) ~b[0,0] ~x[] ~x[0] ~x[0,1] ~y[] ~y[0] ~y[0,0] ~z[] ~z[0] ~z[0,1] ~f(1) ~f(3) ~g(1) ~g(3)
      -- cost: 4
      (a) <- (do
        (OneTuple (b)) <- runProcedure f x z
        (OneTuple (a)) <- runProcedure g y b
        pure (a)
       )
      pure (OneTuple (a))
    
    compose'P3IOIIP3OIIOII = \f x g a z -> do
      -- solution: b[0,1] y[] y[0] y[0,0] f(2) g(1) ~a[] ~a[0] ~a[0,0] ~b[0,0] ~x[] ~x[0] ~x[0,1] ~z[] ~z[0] ~z[0,1] ~f(1) ~f(3) ~g(2) ~g(3)
      -- cost: 4
      (y) <- (do
        (OneTuple (b)) <- runProcedure f x z
        (OneTuple (y)) <- runProcedure g a b
        pure (y)
       )
      pure (OneTuple (y))
    
    compose'P3IOIIP3OOIOOI = \f x g z -> do
      -- solution: a[] a[0] a[0,0] b[0,1] y[] y[0] y[0,0] f(2) g(1) g(2) ~b[0,0] ~x[] ~x[0] ~x[0,1] ~z[] ~z[0] ~z[0,1] ~f(1) ~f(3) ~g(3)
      -- cost: 5
      (a,y) <- (do
        (OneTuple (b)) <- runProcedure f x z
        (y,a) <- runProcedure g b
        pure (a,y)
       )
      pure (y,a)
    
    compose'P3IOOIP3IIIIIO = \f x g y a -> do
      -- solution: b[0,1] z[] z[0] z[0,1] f(2) f(3) ~a[] ~a[0] ~a[0,0] ~b[0,0] ~x[] ~x[0] ~x[0,1] ~y[] ~y[0] ~y[0,0] ~f(1) ~g(1) ~g(2) ~g(3)
      -- cost: 4
      (z) <- (do
        (b,z) <- runProcedure f x
        () <- runProcedure g y a b
        pure (z)
       )
      pure (OneTuple (z))
    
    compose'P3IOOIP3IOIIOO = \f x g y -> do
      -- solution: a[] a[0] a[0,0] b[0,1] z[] z[0] z[0,1] f(2) f(3) g(2) ~b[0,0] ~x[] ~x[0] ~x[0,1] ~y[] ~y[0] ~y[0,0] ~f(1) ~g(1) ~g(3)
      -- cost: 5
      (a,z) <- (do
        (b,z) <- runProcedure f x
        (OneTuple (a)) <- runProcedure g y b
        pure (a,z)
       )
      pure (a,z)
    
    compose'P3IOOIP3OIIOIO = \f x g a -> do
      -- solution: b[0,1] y[] y[0] y[0,0] z[] z[0] z[0,1] f(2) f(3) g(1) ~a[] ~a[0] ~a[0,0] ~b[0,0] ~x[] ~x[0] ~x[0,1] ~f(1) ~g(2) ~g(3)
      -- cost: 5
      (y,z) <- (do
        (b,z) <- runProcedure f x
        (OneTuple (y)) <- runProcedure g a b
        pure (y,z)
       )
      pure (y,z)
    
    compose'P3IOOIP3OOIOOO = \f x g -> do
      -- solution: a[] a[0] a[0,0] b[0,1] y[] y[0] y[0,0] z[] z[0] z[0,1] f(2) f(3) g(1) g(2) ~b[0,0] ~x[] ~x[0] ~x[0,1] ~f(1) ~g(3)
      -- cost: 6
      (a,y,z) <- (do
        (b,z) <- runProcedure f x
        (y,a) <- runProcedure g b
        pure (a,y,z)
       )
      pure (y,a,z)
    
    compose'P3OIIOP3IIOIII = \f g y a z -> do
      -- solution: b[0,0] x[] x[0] x[0,1] f(1) g(3) ~a[] ~a[0] ~a[0,0] ~b[0,1] ~y[] ~y[0] ~y[0,0] ~z[] ~z[0] ~z[0,1] ~f(2) ~f(3) ~g(1) ~g(2)
      -- cost: 4
      (x) <- (do
        (OneTuple (b)) <- runProcedure g y a
        (OneTuple (x)) <- runProcedure f b z
        pure (x)
       )
      pure (OneTuple (x))
    
    compose'P3OIIOP3IOOIOI = \f g y z -> do
      -- solution: a[] a[0] a[0,0] b[0,0] x[] x[0] x[0,1] f(1) g(2) g(3) ~b[0,1] ~y[] ~y[0] ~y[0,0] ~z[] ~z[0] ~z[0,1] ~f(2) ~f(3) ~g(1)
      -- cost: 5
      (a,x) <- (do
        (a,b) <- runProcedure g y
        (OneTuple (x)) <- runProcedure f b z
        pure (a,x)
       )
      pure (x,a)
    
    compose'P3OIIOP3OIOOII = \f g a z -> do
      -- solution: b[0,0] x[] x[0] x[0,1] y[] y[0] y[0,0] f(1) g(1) g(3) ~a[] ~a[0] ~a[0,0] ~b[0,1] ~z[] ~z[0] ~z[0,1] ~f(2) ~f(3) ~g(2)
      -- cost: 5
      (x,y) <- (do
        (y,b) <- runProcedure g a
        (OneTuple (x)) <- runProcedure f b z
        pure (x,y)
       )
      pure (x,y)
    
    compose'P3OIIOP3OOOOOI = \f g z -> do
      -- solution: a[] a[0] a[0,0] b[0,0] x[] x[0] x[0,1] y[] y[0] y[0,0] f(1) g(1) g(2) g(3) ~b[0,1] ~z[] ~z[0] ~z[0,1] ~f(2) ~f(3)
      -- cost: 6
      (a,x,y) <- (do
        (y,a,b) <- runProcedure g 
        (OneTuple (x)) <- runProcedure f b z
        pure (a,x,y)
       )
      pure (x,y,a)
    
    compose'P3OIOOP3IIOIIO = \f g y a -> do
      -- solution: b[0,0] x[] x[0] x[0,1] z[] z[0] z[0,1] f(1) f(3) g(3) ~a[] ~a[0] ~a[0,0] ~b[0,1] ~y[] ~y[0] ~y[0,0] ~f(2) ~g(1) ~g(2)
      -- cost: 5
      (x,z) <- (do
        (OneTuple (b)) <- runProcedure g y a
        (x,z) <- runProcedure f b
        pure (x,z)
       )
      pure (x,z)
    
    compose'P3OIOOP3IOOIOO = \f g y -> do
      -- solution: a[] a[0] a[0,0] b[0,0] x[] x[0] x[0,1] z[] z[0] z[0,1] f(1) f(3) g(2) g(3) ~b[0,1] ~y[] ~y[0] ~y[0,0] ~f(2) ~g(1)
      -- cost: 6
      (a,x,z) <- (do
        (a,b) <- runProcedure g y
        (x,z) <- runProcedure f b
        pure (a,x,z)
       )
      pure (x,a,z)
    
    compose'P3OIOOP3OIOOIO = \f g a -> do
      -- solution: b[0,0] x[] x[0] x[0,1] y[] y[0] y[0,0] z[] z[0] z[0,1] f(1) f(3) g(1) g(3) ~a[] ~a[0] ~a[0,0] ~b[0,1] ~f(2) ~g(2)
      -- cost: 6
      (x,y,z) <- (do
        (y,b) <- runProcedure g a
        (x,z) <- runProcedure f b
        pure (x,y,z)
       )
      pure (x,y,z)
    
    compose'P3OIOOP3OOOOOO = \f g -> do
      -- solution: a[] a[0] a[0,0] b[0,0] x[] x[0] x[0,1] y[] y[0] y[0,0] z[] z[0] z[0,1] f(1) f(3) g(1) g(2) g(3) ~b[0,1] ~f(2)
      -- cost: 7
      (a,x,y,z) <- (do
        (y,a,b) <- runProcedure g 
        (x,z) <- runProcedure f b
        pure (a,x,y,z)
       )
      pure (x,y,a,z)
    
    compose'P3OOIOP3IIIIII = \f g y a z -> do
      -- solution: b[0,1] x[] x[0] x[0,1] f(1) f(2) ~a[] ~a[0] ~a[0,0] ~b[0,0] ~y[] ~y[0] ~y[0,0] ~z[] ~z[0] ~z[0,1] ~f(3) ~g(1) ~g(2) ~g(3)
      -- cost: 4
      (x) <- (do
        (x,b) <- runProcedure f z
        () <- runProcedure g y a b
        pure (x)
       )
      pure (OneTuple (x))
    
    compose'P3OOIOP3IOIIOI = \f g y z -> do
      -- solution: a[] a[0] a[0,0] b[0,1] x[] x[0] x[0,1] f(1) f(2) g(2) ~b[0,0] ~y[] ~y[0] ~y[0,0] ~z[] ~z[0] ~z[0,1] ~f(3) ~g(1) ~g(3)
      -- cost: 5
      (a,x) <- (do
        (x,b) <- runProcedure f z
        (OneTuple (a)) <- runProcedure g y b
        pure (a,x)
       )
      pure (x,a)
    
    compose'P3OOIOP3OIIOII = \f g a z -> do
      -- solution: b[0,1] x[] x[0] x[0,1] y[] y[0] y[0,0] f(1) f(2) g(1) ~a[] ~a[0] ~a[0,0] ~b[0,0] ~z[] ~z[0] ~z[0,1] ~f(3) ~g(2) ~g(3)
      -- cost: 5
      (x,y) <- (do
        (x,b) <- runProcedure f z
        (OneTuple (y)) <- runProcedure g a b
        pure (x,y)
       )
      pure (x,y)
    
    compose'P3OOIOP3OOIOOI = \f g z -> do
      -- solution: a[] a[0] a[0,0] b[0,1] x[] x[0] x[0,1] y[] y[0] y[0,0] f(1) f(2) g(1) g(2) ~b[0,0] ~z[] ~z[0] ~z[0,1] ~f(3) ~g(3)
      -- cost: 6
      (a,x,y) <- (do
        (x,b) <- runProcedure f z
        (y,a) <- runProcedure g b
        pure (a,x,y)
       )
      pure (x,y,a)
    
    compose'P3OOOOP3IIIIIO = \f g y a -> do
      -- solution: b[0,1] x[] x[0] x[0,1] z[] z[0] z[0,1] f(1) f(2) f(3) ~a[] ~a[0] ~a[0,0] ~b[0,0] ~y[] ~y[0] ~y[0,0] ~g(1) ~g(2) ~g(3)
      -- cost: 5
      (x,z) <- (do
        (x,b,z) <- runProcedure f 
        () <- runProcedure g y a b
        pure (x,z)
       )
      pure (x,z)
    
    compose'P3OOOOP3IOIIOO = \f g y -> do
      -- solution: a[] a[0] a[0,0] b[0,1] x[] x[0] x[0,1] z[] z[0] z[0,1] f(1) f(2) f(3) g(2) ~b[0,0] ~y[] ~y[0] ~y[0,0] ~g(1) ~g(3)
      -- cost: 6
      (a,x,z) <- (do
        (x,b,z) <- runProcedure f 
        (OneTuple (a)) <- runProcedure g y b
        pure (a,x,z)
       )
      pure (x,a,z)
    
    compose'P3OOOOP3OIIOIO = \f g a -> do
      -- solution: b[0,1] x[] x[0] x[0,1] y[] y[0] y[0,0] z[] z[0] z[0,1] f(1) f(2) f(3) g(1) ~a[] ~a[0] ~a[0,0] ~b[0,0] ~g(2) ~g(3)
      -- cost: 6
      (x,y,z) <- (do
        (x,b,z) <- runProcedure f 
        (OneTuple (y)) <- runProcedure g a b
        pure (x,y,z)
       )
      pure (x,y,z)
    
    compose'P3OOOOP3OOIOOO = \f g -> do
      -- solution: a[] a[0] a[0,0] b[0,1] x[] x[0] x[0,1] y[] y[0] y[0,0] z[] z[0] z[0,1] f(1) f(2) f(3) g(1) g(2) ~b[0,0] ~g(3)
      -- cost: 7
      (a,x,y,z) <- (do
        (x,b,z) <- runProcedure f 
        (y,a) <- runProcedure g b
        pure (a,x,y,z)
       )
      pure (x,y,a,z)
    
{- det/1
det arg1 :- ((arg1 = "the"); (arg1 = "a")).
constraints:
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg1[0] <-> arg1[0,0])
(arg1[1] <-> arg1[1,0])
-}

det = rget $ (procedure @'[ 'In ] detI) :& (procedure @'[ 'Out ] detO) :& RNil
  where
    detI = \arg1 -> Logic.once $ do
      -- solution: ~arg1[] ~arg1[0] ~arg1[0,0] ~arg1[1] ~arg1[1,0]
      -- cost: 0
      () <- (do
        guard $ arg1 == "the"
        pure ()
       ) <|> (do
        guard $ arg1 == "a"
        pure ()
       )
      pure ()
    
    detO = do
      -- solution: arg1[] arg1[0] arg1[0,0] arg1[1] arg1[1,0]
      -- cost: 0
      (arg1) <- (do
        arg1 <- pure "the"
        pure (arg1)
       ) <|> (do
        arg1 <- pure "a"
        pure (arg1)
       )
      pure (OneTuple (arg1))
    
{- noun/1
noun arg1 :- ((arg1 = "cat"); (arg1 = "bat")).
constraints:
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg1[0] <-> arg1[0,0])
(arg1[1] <-> arg1[1,0])
-}

noun = rget $ (procedure @'[ 'In ] nounI) :& (procedure @'[ 'Out ] nounO) :& RNil
  where
    nounI = \arg1 -> Logic.once $ do
      -- solution: ~arg1[] ~arg1[0] ~arg1[0,0] ~arg1[1] ~arg1[1,0]
      -- cost: 0
      () <- (do
        guard $ arg1 == "cat"
        pure ()
       ) <|> (do
        guard $ arg1 == "bat"
        pure ()
       )
      pure ()
    
    nounO = do
      -- solution: arg1[] arg1[0] arg1[0,0] arg1[1] arg1[1,0]
      -- cost: 0
      (arg1) <- (do
        arg1 <- pure "cat"
        pure (arg1)
       ) <|> (do
        arg1 <- pure "bat"
        pure (arg1)
       )
      pure (OneTuple (arg1))
    
{- verb/1
verb arg1 :- ((arg1 = "eats")).
constraints:
(arg1[] <-> arg1[0])
(arg1[0] <-> arg1[0,0])
-}

verb = rget $ (procedure @'[ 'In ] verbI) :& (procedure @'[ 'Out ] verbO) :& RNil
  where
    verbI = \arg1 -> Logic.once $ do
      -- solution: ~arg1[] ~arg1[0] ~arg1[0,0]
      -- cost: 0
      () <- (do
        guard $ arg1 == "eats"
        pure ()
       )
      pure ()
    
    verbO = do
      -- solution: arg1[] arg1[0] arg1[0,0]
      -- cost: 0
      (arg1) <- (do
        arg1 <- pure "eats"
        pure (arg1)
       )
      pure (OneTuple (arg1))
    
{- np/3
np arg1 z a :- ((arg1 = NP d0 n1, d0 = d, n1 = n, append data1 z a, data0 = [], data1 = d2:n3:data0, d2 = d, n3 = n, det d, noun n)).
constraints:
~(arg1[0,0] & d0[0,0])
~(d[0,1] & d[0,6])
~(d[0,1] & d[0,8])
~(d[0,6] & d[0,8])
~(d0[0,0] & d0[0,1])
~(d0[0,1] & d[0,1])
~(d2[0,5] & d2[0,6])
~(d2[0,6] & d[0,6])
~(data0[0,4] & data0[0,5])
~(data1[0,3] & data1[0,5])
~(data1[0,5] & d2[0,5])
~(n[0,2] & n[0,7])
~(n[0,2] & n[0,9])
~(n[0,7] & n[0,9])
~(n1[0,0] & n1[0,2])
~(n1[0,2] & n[0,2])
~(n3[0,5] & n3[0,7])
~(n3[0,7] & n[0,7])
(d[0,1] | (d[0,6] | d[0,8]))
(d[0,8] | ~d[0,8])
(d0[0,0] | d0[0,1])
(d2[0,5] | d2[0,6])
(data0[0,4] | data0[0,5])
(data1[0,3] | data1[0,5])
(n[0,2] | (n[0,7] | n[0,9]))
(n[0,9] | ~n[0,9])
(n1[0,0] | n1[0,2])
(n3[0,5] | n3[0,7])
((data1[0,3] & (z[0,3] & ~a[0,3])) | ((data1[0,3] & (~z[0,3] & ~a[0,3])) | ((~data1[0,3] & (z[0,3] & ~a[0,3])) | ((~data1[0,3] & (~z[0,3] & a[0,3])) | (~data1[0,3] & (~z[0,3] & ~a[0,3]))))))
(a[] <-> a[0])
(a[0] <-> a[0,3])
(arg1[] <-> arg1[0])
(arg1[0] <-> arg1[0,0])
(d0[0,0] <-> n1[0,0])
(d2[0,5] <-> data0[0,5])
(d2[0,5] <-> n3[0,5])
(z[] <-> z[0])
(z[0] <-> z[0,3])
1
-}

np = rget $ (procedure @'[ 'In, 'In, 'In ] npIII) :& (procedure @'[ 'In, 'In, 'Out ] npIIO) :& (procedure @'[ 'In, 'Out, 'In ] npIOI) :& (procedure @'[ 'Out, 'In, 'In ] npOII) :& (procedure @'[ 'Out, 'In, 'Out ] npOIO) :& (procedure @'[ 'Out, 'Out, 'In ] npOOI) :& RNil
  where
    npIII = \arg1 z a -> Logic.once $ do
      -- solution: d[0,1] d0[0,0] d2[0,6] data0[0,4] data1[0,5] n[0,2] n1[0,0] n3[0,7] ~a[] ~a[0] ~a[0,3] ~arg1[] ~arg1[0] ~arg1[0,0] ~d[0,6] ~d[0,8] ~d0[0,1] ~d2[0,5] ~data0[0,5] ~data1[0,3] ~n[0,7] ~n[0,9] ~n1[0,2] ~n3[0,5] ~z[] ~z[0] ~z[0,3]
      -- cost: 3
      () <- (do
        (NP d0 n1) <- pure arg1
        d <- pure d0
        d2 <- pure d
        n <- pure n1
        n3 <- pure n
        data0 <- pure []
        data1 <- pure (d2:n3:data0)
        () <- runProcedure @'[ 'In, 'In, 'In ] append data1 z a
        () <- runProcedure @'[ 'In ] det d
        () <- runProcedure @'[ 'In ] noun n
        pure ()
       )
      pure ()
    
    npIIO = \arg1 z -> do
      -- solution: a[] a[0] a[0,3] d[0,1] d0[0,0] d2[0,6] data0[0,4] data1[0,5] n[0,2] n1[0,0] n3[0,7] ~arg1[] ~arg1[0] ~arg1[0,0] ~d[0,6] ~d[0,8] ~d0[0,1] ~d2[0,5] ~data0[0,5] ~data1[0,3] ~n[0,7] ~n[0,9] ~n1[0,2] ~n3[0,5] ~z[] ~z[0] ~z[0,3]
      -- cost: 4
      (a) <- (do
        (NP d0 n1) <- pure arg1
        d <- pure d0
        d2 <- pure d
        n <- pure n1
        n3 <- pure n
        data0 <- pure []
        data1 <- pure (d2:n3:data0)
        () <- runProcedure @'[ 'In ] det d
        () <- runProcedure @'[ 'In ] noun n
        (OneTuple (a)) <- runProcedure @'[ 'In, 'In, 'Out ] append data1 z
        pure (a)
       )
      pure (OneTuple (a))
    
    npIOI = \arg1 a -> do
      -- solution: d[0,1] d0[0,0] d2[0,6] data0[0,4] data1[0,5] n[0,2] n1[0,0] n3[0,7] z[] z[0] z[0,3] ~a[] ~a[0] ~a[0,3] ~arg1[] ~arg1[0] ~arg1[0,0] ~d[0,6] ~d[0,8] ~d0[0,1] ~d2[0,5] ~data0[0,5] ~data1[0,3] ~n[0,7] ~n[0,9] ~n1[0,2] ~n3[0,5]
      -- cost: 4
      (z) <- (do
        (NP d0 n1) <- pure arg1
        d <- pure d0
        d2 <- pure d
        n <- pure n1
        n3 <- pure n
        data0 <- pure []
        data1 <- pure (d2:n3:data0)
        () <- runProcedure @'[ 'In ] det d
        () <- runProcedure @'[ 'In ] noun n
        (OneTuple (z)) <- runProcedure @'[ 'In, 'Out, 'In ] append data1 a
        pure (z)
       )
      pure (OneTuple (z))
    
    npOII = \z a -> do
      -- solution: arg1[] arg1[0] arg1[0,0] d[0,6] d0[0,1] d2[0,5] data0[0,5] data1[0,3] n[0,7] n1[0,2] n3[0,5] ~a[] ~a[0] ~a[0,3] ~d[0,1] ~d[0,8] ~d0[0,0] ~d2[0,6] ~data0[0,4] ~data1[0,5] ~n[0,2] ~n[0,9] ~n1[0,0] ~n3[0,7] ~z[] ~z[0] ~z[0,3]
      -- cost: 4
      (arg1) <- (do
        (OneTuple (data1)) <- runProcedure @'[ 'Out, 'In, 'In ] append z a
        (d2:n3:data0) <- pure data1
        d <- pure d2
        d0 <- pure d
        () <- runProcedure @'[ 'In ] det d
        n <- pure n3
        n1 <- pure n
        arg1 <- pure (NP d0 n1)
        () <- runProcedure @'[ 'In ] noun n
        guard $ data0 == []
        pure (arg1)
       )
      pure (OneTuple (arg1))
    
    npOIO = \z -> do
      -- solution: a[] a[0] a[0,3] arg1[] arg1[0] arg1[0,0] d[0,8] d0[0,1] d2[0,6] data0[0,4] data1[0,5] n[0,9] n1[0,2] n3[0,7] ~d[0,1] ~d[0,6] ~d0[0,0] ~d2[0,5] ~data0[0,5] ~data1[0,3] ~n[0,2] ~n[0,7] ~n1[0,0] ~n3[0,5] ~z[] ~z[0] ~z[0,3]
      -- cost: 6
      (a,arg1) <- (do
        data0 <- pure []
        (OneTuple (d)) <- runProcedure @'[ 'Out ] det 
        d0 <- pure d
        d2 <- pure d
        (OneTuple (n)) <- runProcedure @'[ 'Out ] noun 
        n1 <- pure n
        arg1 <- pure (NP d0 n1)
        n3 <- pure n
        data1 <- pure (d2:n3:data0)
        (OneTuple (a)) <- runProcedure @'[ 'In, 'In, 'Out ] append data1 z
        pure (a,arg1)
       )
      pure (arg1,a)
    
    npOOI = \a -> do
      -- solution: arg1[] arg1[0] arg1[0,0] d[0,6] d0[0,1] d2[0,5] data0[0,5] data1[0,3] n[0,7] n1[0,2] n3[0,5] z[] z[0] z[0,3] ~a[] ~a[0] ~a[0,3] ~d[0,1] ~d[0,8] ~d0[0,0] ~d2[0,6] ~data0[0,4] ~data1[0,5] ~n[0,2] ~n[0,9] ~n1[0,0] ~n3[0,7]
      -- cost: 5
      (arg1,z) <- (do
        (data1,z) <- runProcedure @'[ 'Out, 'Out, 'In ] append a
        (d2:n3:data0) <- pure data1
        d <- pure d2
        d0 <- pure d
        () <- runProcedure @'[ 'In ] det d
        n <- pure n3
        n1 <- pure n
        arg1 <- pure (NP d0 n1)
        () <- runProcedure @'[ 'In ] noun n
        guard $ data0 == []
        pure (arg1,z)
       )
      pure (arg1,z)
    
{- vp/3
vp arg1 z a :- ((arg1 = VP v0 n, v0 = v, compose' pred0 data2 pred3 n z a, data1 = [], data2 = v1:data1, v1 = v, (pred0 curry1 curry2 curry3 :- (append curry1 curry2 curry3)), (pred3 curry1 curry2 curry3 :- (np curry1 curry2 curry3)), verb v)).
constraints:
~curry1[0]
~curry2[0]
~curry3[0]
~pred0[0,2]
~pred3[0,2]
~(arg1[0,0] & v0[0,0])
~(data1[0,3] & data1[0,4])
~(data2[0,2] & data2[0,4])
~(data2[0,4] & v1[0,4])
~(n[0,0] & n[0,2])
~(v[0,1] & v[0,5])
~(v[0,1] & v[0,8])
~(v[0,5] & v[0,8])
~(v0[0,0] & v0[0,1])
~(v0[0,1] & v[0,1])
~(v1[0,4] & v1[0,5])
~(v1[0,5] & v[0,5])
(data1[0,3] | data1[0,4])
(data2[0,2] | data2[0,4])
(n[0,0] | n[0,2])
(v[0,1] | (v[0,5] | v[0,8]))
(v[0,8] | ~v[0,8])
(v0[0,0] | v0[0,1])
(v1[0,4] | v1[0,5])
((curry1[0,6,0,0] & (curry2[0,6,0,0] & ~curry3[0,6,0,0])) | ((curry1[0,6,0,0] & (~curry2[0,6,0,0] & ~curry3[0,6,0,0])) | ((~curry1[0,6,0,0] & (curry2[0,6,0,0] & ~curry3[0,6,0,0])) | ((~curry1[0,6,0,0] & (~curry2[0,6,0,0] & curry3[0,6,0,0])) | (~curry1[0,6,0,0] & (~curry2[0,6,0,0] & ~curry3[0,6,0,0]))))))
((curry1[0,7,0,0] & (curry2[0,7,0,0] & ~curry3[0,7,0,0])) | ((curry1[0,7,0,0] & (~curry2[0,7,0,0] & curry3[0,7,0,0])) | ((curry1[0,7,0,0] & (~curry2[0,7,0,0] & ~curry3[0,7,0,0])) | ((~curry1[0,7,0,0] & (curry2[0,7,0,0] & ~curry3[0,7,0,0])) | ((~curry1[0,7,0,0] & (~curry2[0,7,0,0] & curry3[0,7,0,0])) | (~curry1[0,7,0,0] & (~curry2[0,7,0,0] & ~curry3[0,7,0,0])))))))
((~pred0[0,2] & (pred0(1) & (pred0(2) & (pred0(3) & (data2[0,2] & (~pred3[0,2] & (pred3(1) & (pred3(2) & (~pred3(3) & (n[0,2] & (z[0,2] & a[0,2]))))))))))) | ((~pred0[0,2] & (pred0(1) & (pred0(2) & (pred0(3) & (data2[0,2] & (~pred3[0,2] & (pred3(1) & (~pred3(2) & (~pred3(3) & (n[0,2] & (~z[0,2] & a[0,2]))))))))))) | ((~pred0[0,2] & (pred0(1) & (pred0(2) & (pred0(3) & (data2[0,2] & (~pred3[0,2] & (~pred3(1) & (pred3(2) & (~pred3(3) & (~n[0,2] & (z[0,2] & a[0,2]))))))))))) | ((~pred0[0,2] & (pred0(1) & (pred0(2) & (pred0(3) & (data2[0,2] & (~pred3[0,2] & (~pred3(1) & (~pred3(2) & (~pred3(3) & (~n[0,2] & (~z[0,2] & a[0,2]))))))))))) | ((~pred0[0,2] & (pred0(1) & (pred0(2) & (~pred0(3) & (data2[0,2] & (~pred3[0,2] & (pred3(1) & (pred3(2) & (~pred3(3) & (n[0,2] & (z[0,2] & ~a[0,2]))))))))))) | ((~pred0[0,2] & (pred0(1) & (pred0(2) & (~pred0(3) & (data2[0,2] & (~pred3[0,2] & (pred3(1) & (~pred3(2) & (~pred3(3) & (n[0,2] & (~z[0,2] & ~a[0,2]))))))))))) | ((~pred0[0,2] & (pred0(1) & (pred0(2) & (~pred0(3) & (data2[0,2] & (~pred3[0,2] & (~pred3(1) & (pred3(2) & (~pred3(3) & (~n[0,2] & (z[0,2] & ~a[0,2]))))))))))) | ((~pred0[0,2] & (pred0(1) & (pred0(2) & (~pred0(3) & (data2[0,2] & (~pred3[0,2] & (~pred3(1) & (~pred3(2) & (~pred3(3) & (~n[0,2] & (~z[0,2] & ~a[0,2]))))))))))) | ((~pred0[0,2] & (pred0(1) & (~pred0(2) & (pred0(3) & (data2[0,2] & (~pred3[0,2] & (pred3(1) & (pred3(2) & (pred3(3) & (n[0,2] & (z[0,2] & a[0,2]))))))))))) | ((~pred0[0,2] & (pred0(1) & (~pred0(2) & (pred0(3) & (data2[0,2] & (~pred3[0,2] & (pred3(1) & (~pred3(2) & (pred3(3) & (n[0,2] & (~z[0,2] & a[0,2]))))))))))) | ((~pred0[0,2] & (pred0(1) & (~pred0(2) & (pred0(3) & (data2[0,2] & (~pred3[0,2] & (~pred3(1) & (pred3(2) & (pred3(3) & (~n[0,2] & (z[0,2] & a[0,2]))))))))))) | ((~pred0[0,2] & (pred0(1) & (~pred0(2) & (pred0(3) & (data2[0,2] & (~pred3[0,2] & (~pred3(1) & (~pred3(2) & (pred3(3) & (~n[0,2] & (~z[0,2] & a[0,2]))))))))))) | ((~pred0[0,2] & (pred0(1) & (~pred0(2) & (~pred0(3) & (data2[0,2] & (~pred3[0,2] & (pred3(1) & (pred3(2) & (pred3(3) & (n[0,2] & (z[0,2] & ~a[0,2]))))))))))) | ((~pred0[0,2] & (pred0(1) & (~pred0(2) & (~pred0(3) & (data2[0,2] & (~pred3[0,2] & (pred3(1) & (~pred3(2) & (pred3(3) & (n[0,2] & (~z[0,2] & ~a[0,2]))))))))))) | ((~pred0[0,2] & (pred0(1) & (~pred0(2) & (~pred0(3) & (data2[0,2] & (~pred3[0,2] & (~pred3(1) & (pred3(2) & (pred3(3) & (~n[0,2] & (z[0,2] & ~a[0,2]))))))))))) | ((~pred0[0,2] & (pred0(1) & (~pred0(2) & (~pred0(3) & (data2[0,2] & (~pred3[0,2] & (~pred3(1) & (~pred3(2) & (pred3(3) & (~n[0,2] & (~z[0,2] & ~a[0,2]))))))))))) | ((~pred0[0,2] & (~pred0(1) & (pred0(2) & (pred0(3) & (~data2[0,2] & (~pred3[0,2] & (pred3(1) & (pred3(2) & (~pred3(3) & (n[0,2] & (z[0,2] & a[0,2]))))))))))) | ((~pred0[0,2] & (~pred0(1) & (pred0(2) & (pred0(3) & (~data2[0,2] & (~pred3[0,2] & (pred3(1) & (~pred3(2) & (~pred3(3) & (n[0,2] & (~z[0,2] & a[0,2]))))))))))) | ((~pred0[0,2] & (~pred0(1) & (pred0(2) & (pred0(3) & (~data2[0,2] & (~pred3[0,2] & (~pred3(1) & (pred3(2) & (~pred3(3) & (~n[0,2] & (z[0,2] & a[0,2]))))))))))) | ((~pred0[0,2] & (~pred0(1) & (pred0(2) & (pred0(3) & (~data2[0,2] & (~pred3[0,2] & (~pred3(1) & (~pred3(2) & (~pred3(3) & (~n[0,2] & (~z[0,2] & a[0,2]))))))))))) | ((~pred0[0,2] & (~pred0(1) & (pred0(2) & (~pred0(3) & (~data2[0,2] & (~pred3[0,2] & (pred3(1) & (pred3(2) & (~pred3(3) & (n[0,2] & (z[0,2] & ~a[0,2]))))))))))) | ((~pred0[0,2] & (~pred0(1) & (pred0(2) & (~pred0(3) & (~data2[0,2] & (~pred3[0,2] & (pred3(1) & (~pred3(2) & (~pred3(3) & (n[0,2] & (~z[0,2] & ~a[0,2]))))))))))) | ((~pred0[0,2] & (~pred0(1) & (pred0(2) & (~pred0(3) & (~data2[0,2] & (~pred3[0,2] & (~pred3(1) & (pred3(2) & (~pred3(3) & (~n[0,2] & (z[0,2] & ~a[0,2]))))))))))) | ((~pred0[0,2] & (~pred0(1) & (pred0(2) & (~pred0(3) & (~data2[0,2] & (~pred3[0,2] & (~pred3(1) & (~pred3(2) & (~pred3(3) & (~n[0,2] & (~z[0,2] & ~a[0,2]))))))))))) | ((~pred0[0,2] & (~pred0(1) & (~pred0(2) & (pred0(3) & (~data2[0,2] & (~pred3[0,2] & (pred3(1) & (pred3(2) & (pred3(3) & (n[0,2] & (z[0,2] & a[0,2]))))))))))) | ((~pred0[0,2] & (~pred0(1) & (~pred0(2) & (pred0(3) & (~data2[0,2] & (~pred3[0,2] & (pred3(1) & (~pred3(2) & (pred3(3) & (n[0,2] & (~z[0,2] & a[0,2]))))))))))) | ((~pred0[0,2] & (~pred0(1) & (~pred0(2) & (pred0(3) & (~data2[0,2] & (~pred3[0,2] & (~pred3(1) & (pred3(2) & (pred3(3) & (~n[0,2] & (z[0,2] & a[0,2]))))))))))) | ((~pred0[0,2] & (~pred0(1) & (~pred0(2) & (pred0(3) & (~data2[0,2] & (~pred3[0,2] & (~pred3(1) & (~pred3(2) & (pred3(3) & (~n[0,2] & (~z[0,2] & a[0,2]))))))))))) | ((~pred0[0,2] & (~pred0(1) & (~pred0(2) & (~pred0(3) & (~data2[0,2] & (~pred3[0,2] & (pred3(1) & (pred3(2) & (pred3(3) & (n[0,2] & (z[0,2] & ~a[0,2]))))))))))) | ((~pred0[0,2] & (~pred0(1) & (~pred0(2) & (~pred0(3) & (~data2[0,2] & (~pred3[0,2] & (pred3(1) & (~pred3(2) & (pred3(3) & (n[0,2] & (~z[0,2] & ~a[0,2]))))))))))) | ((~pred0[0,2] & (~pred0(1) & (~pred0(2) & (~pred0(3) & (~data2[0,2] & (~pred3[0,2] & (~pred3(1) & (pred3(2) & (pred3(3) & (~n[0,2] & (z[0,2] & ~a[0,2]))))))))))) | (~pred0[0,2] & (~pred0(1) & (~pred0(2) & (~pred0(3) & (~data2[0,2] & (~pred3[0,2] & (~pred3(1) & (~pred3(2) & (pred3(3) & (~n[0,2] & (~z[0,2] & ~a[0,2]))))))))))))))))))))))))))))))))))))))))))
(a[] <-> a[0])
(a[0] <-> a[0,2])
(arg1[] <-> arg1[0])
(arg1[0] <-> arg1[0,0])
(curry1[0,6,0] <-> curry1[0,6,0,0])
(curry1[0,7,0] <-> curry1[0,7,0,0])
(curry2[0,6,0] <-> curry2[0,6,0,0])
(curry2[0,7,0] <-> curry2[0,7,0,0])
(curry3[0,6,0] <-> curry3[0,6,0,0])
(curry3[0,7,0] <-> curry3[0,7,0,0])
(v0[0,0] <-> n[0,0])
(v1[0,4] <-> data1[0,4])
(z[] <-> z[0])
(z[0] <-> z[0,2])
(pred0(1) <-> curry1[0,6,0])
(pred0(2) <-> curry2[0,6,0])
(pred0(3) <-> curry3[0,6,0])
(pred3(1) <-> curry1[0,7,0])
(pred3(2) <-> curry2[0,7,0])
(pred3(3) <-> curry3[0,7,0])
1
-}
--mode ordering failure, cyclic dependency: [7] (pred3::O curry1::O curry2::I curry3::I :- (np curry1::O curry2::I curry3::I)) -> [6] (pred0::O curry1::I curry2::O curry3::I :- (append curry1::I curry2::O curry3::I))
--mode ordering failure, cyclic dependency: [7] (pred3::O curry1::I curry2::I curry3::O :- (np curry1::I curry2::I curry3::O)) -> [6] (pred0::O curry1::O curry2::I curry3::I :- (append curry1::O curry2::I curry3::I))
--mode ordering failure, cyclic dependency: [7] (pred3::O curry1::I curry2::I curry3::O :- (np curry1::I curry2::I curry3::O)) -> [6] (pred0::O curry1::O curry2::I curry3::I :- (append curry1::O curry2::I curry3::I))
--mode ordering failure, cyclic dependency: [7] (pred3::O curry1::I curry2::I curry3::O :- (np curry1::I curry2::I curry3::O)) -> [6] (pred0::O curry1::O curry2::I curry3::I :- (append curry1::O curry2::I curry3::I))
--mode ordering failure, cyclic dependency: [7] (pred3::O curry1::I curry2::I curry3::O :- (np curry1::I curry2::I curry3::O)) -> [6] (pred0::O curry1::O curry2::I curry3::I :- (append curry1::O curry2::I curry3::I))
--mode ordering failure, cyclic dependency: [7] (pred3::O curry1::I curry2::I curry3::O :- (np curry1::I curry2::I curry3::O)) -> [6] (pred0::O curry1::O curry2::I curry3::I :- (append curry1::O curry2::I curry3::I))
--mode ordering failure, cyclic dependency: [7] (pred3::O curry1::O curry2::I curry3::I :- (np curry1::O curry2::I curry3::I)) -> [6] (pred0::O curry1::I curry2::O curry3::I :- (append curry1::I curry2::O curry3::I))
vp = rget $ (procedure @'[ 'In, 'In, 'In ] vpIII) :& (procedure @'[ 'In, 'In, 'Out ] vpIIO) :& (procedure @'[ 'In, 'Out, 'In ] vpIOI) :& (procedure @'[ 'Out, 'In, 'In ] vpOII) :& (procedure @'[ 'Out, 'In, 'Out ] vpOIO) :& (procedure @'[ 'Out, 'Out, 'In ] vpOOI) :& RNil
  where
    vpIII = \arg1 z a -> Logic.once $ do
      -- solution: curry2[0,6,0] curry2[0,6,0,0] data1[0,3] data2[0,4] n[0,0] v[0,1] v0[0,0] v1[0,5] pred0(2) ~a[] ~a[0] ~a[0,2] ~arg1[] ~arg1[0] ~arg1[0,0] ~curry1[0] ~curry1[0,6,0] ~curry1[0,6,0,0] ~curry1[0,7,0] ~curry1[0,7,0,0] ~curry2[0] ~curry2[0,7,0] ~curry2[0,7,0,0] ~curry3[0] ~curry3[0,6,0] ~curry3[0,6,0,0] ~curry3[0,7,0] ~curry3[0,7,0,0] ~data1[0,4] ~data2[0,2] ~n[0,2] ~pred0[0,2] ~pred3[0,2] ~v[0,5] ~v[0,8] ~v0[0,1] ~v1[0,4] ~z[] ~z[0] ~z[0,2] ~pred0(1) ~pred0(3) ~pred3(1) ~pred3(2) ~pred3(3)
      -- cost: 5
      () <- (do
        (VP v0 n) <- pure arg1
        v <- pure v0
        v1 <- pure v
        data1 <- pure []
        data2 <- pure (v1:data1)
        () <- runProcedure @'[ 'In ] verb v
        let pred0 = procedure @'[ 'In, 'Out, 'In ] $
              \curry1 curry3 -> do
                (curry2) <- (do
                  (OneTuple (curry2)) <- runProcedure @'[ 'In, 'Out, 'In ] append curry1 curry3
                  pure (curry2)
                 )
                pure (OneTuple (curry2))
        let pred3 = procedure @'[ 'In, 'In, 'In ] $
              \curry1 curry2 curry3 -> do
                () <- (do
                  () <- runProcedure @'[ 'In, 'In, 'In ] np curry1 curry2 curry3
                  pure ()
                 )
                pure ()
        () <- runProcedure @'[ 'PredMode '[ 'In, 'Out, 'In ], 'In, 'PredMode '[ 'In, 'In, 'In ], 'In, 'In, 'In ] compose' pred0 data2 pred3 n z a
        pure ()
       )
      pure ()
    
    vpIIO = \arg1 z -> do
      -- solution: a[] a[0] a[0,2] curry3[0,6,0] curry3[0,6,0,0] curry3[0,7,0] curry3[0,7,0,0] data1[0,3] data2[0,4] n[0,0] v[0,1] v0[0,0] v1[0,5] pred0(3) pred3(3) ~arg1[] ~arg1[0] ~arg1[0,0] ~curry1[0] ~curry1[0,6,0] ~curry1[0,6,0,0] ~curry1[0,7,0] ~curry1[0,7,0,0] ~curry2[0] ~curry2[0,6,0] ~curry2[0,6,0,0] ~curry2[0,7,0] ~curry2[0,7,0,0] ~curry3[0] ~data1[0,4] ~data2[0,2] ~n[0,2] ~pred0[0,2] ~pred3[0,2] ~v[0,5] ~v[0,8] ~v0[0,1] ~v1[0,4] ~z[] ~z[0] ~z[0,2] ~pred0(1) ~pred0(2) ~pred3(1) ~pred3(2)
      -- cost: 7
      (a) <- (do
        (VP v0 n) <- pure arg1
        v <- pure v0
        v1 <- pure v
        data1 <- pure []
        data2 <- pure (v1:data1)
        () <- runProcedure @'[ 'In ] verb v
        let pred0 = procedure @'[ 'In, 'In, 'Out ] $
              \curry1 curry2 -> do
                (curry3) <- (do
                  (OneTuple (curry3)) <- runProcedure @'[ 'In, 'In, 'Out ] append curry1 curry2
                  pure (curry3)
                 )
                pure (OneTuple (curry3))
        let pred3 = procedure @'[ 'In, 'In, 'Out ] $
              \curry1 curry2 -> do
                (curry3) <- (do
                  (OneTuple (curry3)) <- runProcedure @'[ 'In, 'In, 'Out ] np curry1 curry2
                  pure (curry3)
                 )
                pure (OneTuple (curry3))
        (OneTuple (a)) <- runProcedure @'[ 'PredMode '[ 'In, 'In, 'Out ], 'In, 'PredMode '[ 'In, 'In, 'Out ], 'In, 'In, 'Out ] compose' pred0 data2 pred3 n z
        pure (a)
       )
      pure (OneTuple (a))
    
    vpIOI = \arg1 a -> do
      -- solution: curry2[0,6,0] curry2[0,6,0,0] curry2[0,7,0] curry2[0,7,0,0] data1[0,3] data2[0,4] n[0,0] v[0,1] v0[0,0] v1[0,5] z[] z[0] z[0,2] pred0(2) pred3(2) ~a[] ~a[0] ~a[0,2] ~arg1[] ~arg1[0] ~arg1[0,0] ~curry1[0] ~curry1[0,6,0] ~curry1[0,6,0,0] ~curry1[0,7,0] ~curry1[0,7,0,0] ~curry2[0] ~curry3[0] ~curry3[0,6,0] ~curry3[0,6,0,0] ~curry3[0,7,0] ~curry3[0,7,0,0] ~data1[0,4] ~data2[0,2] ~n[0,2] ~pred0[0,2] ~pred3[0,2] ~v[0,5] ~v[0,8] ~v0[0,1] ~v1[0,4] ~pred0(1) ~pred0(3) ~pred3(1) ~pred3(3)
      -- cost: 7
      (z) <- (do
        (VP v0 n) <- pure arg1
        v <- pure v0
        v1 <- pure v
        data1 <- pure []
        data2 <- pure (v1:data1)
        () <- runProcedure @'[ 'In ] verb v
        let pred0 = procedure @'[ 'In, 'Out, 'In ] $
              \curry1 curry3 -> do
                (curry2) <- (do
                  (OneTuple (curry2)) <- runProcedure @'[ 'In, 'Out, 'In ] append curry1 curry3
                  pure (curry2)
                 )
                pure (OneTuple (curry2))
        let pred3 = procedure @'[ 'In, 'Out, 'In ] $
              \curry1 curry3 -> do
                (curry2) <- (do
                  (OneTuple (curry2)) <- runProcedure @'[ 'In, 'Out, 'In ] np curry1 curry3
                  pure (curry2)
                 )
                pure (OneTuple (curry2))
        (OneTuple (z)) <- runProcedure @'[ 'PredMode '[ 'In, 'Out, 'In ], 'In, 'PredMode '[ 'In, 'Out, 'In ], 'In, 'Out, 'In ] compose' pred0 data2 pred3 n a
        pure (z)
       )
      pure (OneTuple (z))
    
    vpOII = \z a -> do
      -- solution: arg1[] arg1[0] arg1[0,0] curry1[0,7,0] curry1[0,7,0,0] curry3[0,7,0] curry3[0,7,0,0] data1[0,3] data2[0,4] n[0,2] v[0,8] v0[0,1] v1[0,5] pred3(1) pred3(3) ~a[] ~a[0] ~a[0,2] ~curry1[0] ~curry1[0,6,0] ~curry1[0,6,0,0] ~curry2[0] ~curry2[0,6,0] ~curry2[0,6,0,0] ~curry2[0,7,0] ~curry2[0,7,0,0] ~curry3[0] ~curry3[0,6,0] ~curry3[0,6,0,0] ~data1[0,4] ~data2[0,2] ~n[0,0] ~pred0[0,2] ~pred3[0,2] ~v[0,1] ~v[0,5] ~v0[0,0] ~v1[0,4] ~z[] ~z[0] ~z[0,2] ~pred0(1) ~pred0(2) ~pred0(3) ~pred3(2)
      -- cost: 8
      (arg1) <- (do
        data1 <- pure []
        (OneTuple (v)) <- runProcedure @'[ 'Out ] verb 
        v0 <- pure v
        v1 <- pure v
        data2 <- pure (v1:data1)
        let pred3 = procedure @'[ 'Out, 'In, 'Out ] $
              \curry2 -> do
                (curry1,curry3) <- (do
                  (curry1,curry3) <- runProcedure @'[ 'Out, 'In, 'Out ] np curry2
                  pure (curry1,curry3)
                 )
                pure (curry1,curry3)
        let pred0 = procedure @'[ 'In, 'In, 'In ] $
              \curry1 curry2 curry3 -> do
                () <- (do
                  () <- runProcedure @'[ 'In, 'In, 'In ] append curry1 curry2 curry3
                  pure ()
                 )
                pure ()
        (OneTuple (n)) <- runProcedure @'[ 'PredMode '[ 'In, 'In, 'In ], 'In, 'PredMode '[ 'Out, 'In, 'Out ], 'Out, 'In, 'In ] compose' pred0 data2 pred3 z a
        arg1 <- pure (VP v0 n)
        pure (arg1)
       )
      pure (OneTuple (arg1))
    
    vpOIO = \z -> do
      -- solution: a[] a[0] a[0,2] arg1[] arg1[0] arg1[0,0] curry1[0,7,0] curry1[0,7,0,0] curry3[0,6,0] curry3[0,6,0,0] curry3[0,7,0] curry3[0,7,0,0] data1[0,3] data2[0,4] n[0,2] v[0,8] v0[0,1] v1[0,5] pred0(3) pred3(1) pred3(3) ~curry1[0] ~curry1[0,6,0] ~curry1[0,6,0,0] ~curry2[0] ~curry2[0,6,0] ~curry2[0,6,0,0] ~curry2[0,7,0] ~curry2[0,7,0,0] ~curry3[0] ~data1[0,4] ~data2[0,2] ~n[0,0] ~pred0[0,2] ~pred3[0,2] ~v[0,1] ~v[0,5] ~v0[0,0] ~v1[0,4] ~z[] ~z[0] ~z[0,2] ~pred0(1) ~pred0(2) ~pred3(2)
      -- cost: 10
      (a,arg1) <- (do
        data1 <- pure []
        (OneTuple (v)) <- runProcedure @'[ 'Out ] verb 
        v0 <- pure v
        v1 <- pure v
        data2 <- pure (v1:data1)
        let pred3 = procedure @'[ 'Out, 'In, 'Out ] $
              \curry2 -> do
                (curry1,curry3) <- (do
                  (curry1,curry3) <- runProcedure @'[ 'Out, 'In, 'Out ] np curry2
                  pure (curry1,curry3)
                 )
                pure (curry1,curry3)
        let pred0 = procedure @'[ 'In, 'In, 'Out ] $
              \curry1 curry2 -> do
                (curry3) <- (do
                  (OneTuple (curry3)) <- runProcedure @'[ 'In, 'In, 'Out ] append curry1 curry2
                  pure (curry3)
                 )
                pure (OneTuple (curry3))
        (n,a) <- runProcedure @'[ 'PredMode '[ 'In, 'In, 'Out ], 'In, 'PredMode '[ 'Out, 'In, 'Out ], 'Out, 'In, 'Out ] compose' pred0 data2 pred3 z
        arg1 <- pure (VP v0 n)
        pure (a,arg1)
       )
      pure (arg1,a)
    
    vpOOI = \a -> do
      -- solution: arg1[] arg1[0] arg1[0,0] curry1[0,7,0] curry1[0,7,0,0] curry2[0,6,0] curry2[0,6,0,0] curry2[0,7,0] curry2[0,7,0,0] data1[0,3] data2[0,4] n[0,2] v[0,8] v0[0,1] v1[0,5] z[] z[0] z[0,2] pred0(2) pred3(1) pred3(2) ~a[] ~a[0] ~a[0,2] ~curry1[0] ~curry1[0,6,0] ~curry1[0,6,0,0] ~curry2[0] ~curry3[0] ~curry3[0,6,0] ~curry3[0,6,0,0] ~curry3[0,7,0] ~curry3[0,7,0,0] ~data1[0,4] ~data2[0,2] ~n[0,0] ~pred0[0,2] ~pred3[0,2] ~v[0,1] ~v[0,5] ~v0[0,0] ~v1[0,4] ~pred0(1) ~pred0(3) ~pred3(3)
      -- cost: 10
      (arg1,z) <- (do
        data1 <- pure []
        (OneTuple (v)) <- runProcedure @'[ 'Out ] verb 
        v0 <- pure v
        v1 <- pure v
        data2 <- pure (v1:data1)
        let pred3 = procedure @'[ 'Out, 'Out, 'In ] $
              \curry3 -> do
                (curry1,curry2) <- (do
                  (curry1,curry2) <- runProcedure @'[ 'Out, 'Out, 'In ] np curry3
                  pure (curry1,curry2)
                 )
                pure (curry1,curry2)
        let pred0 = procedure @'[ 'In, 'Out, 'In ] $
              \curry1 curry3 -> do
                (curry2) <- (do
                  (OneTuple (curry2)) <- runProcedure @'[ 'In, 'Out, 'In ] append curry1 curry3
                  pure (curry2)
                 )
                pure (OneTuple (curry2))
        (n,z) <- runProcedure @'[ 'PredMode '[ 'In, 'Out, 'In ], 'In, 'PredMode '[ 'Out, 'Out, 'In ], 'Out, 'Out, 'In ] compose' pred0 data2 pred3 a
        arg1 <- pure (VP v0 n)
        pure (arg1,z)
       )
      pure (arg1,z)
    
{- sentence/3
sentence arg1 z a :- ((arg1 = S n v, compose' pred0 n pred1 v z a, (pred0 curry1 curry2 curry3 :- (np curry1 curry2 curry3)), (pred1 curry1 curry2 curry3 :- (vp curry1 curry2 curry3)))).
constraints:
~curry1[0]
~curry2[0]
~curry3[0]
~pred0[0,1]
~pred1[0,1]
~(arg1[0,0] & n[0,0])
~(n[0,0] & n[0,1])
~(v[0,0] & v[0,1])
(n[0,0] | n[0,1])
(v[0,0] | v[0,1])
((curry1[0,2,0,0] & (curry2[0,2,0,0] & ~curry3[0,2,0,0])) | ((curry1[0,2,0,0] & (~curry2[0,2,0,0] & curry3[0,2,0,0])) | ((curry1[0,2,0,0] & (~curry2[0,2,0,0] & ~curry3[0,2,0,0])) | ((~curry1[0,2,0,0] & (curry2[0,2,0,0] & ~curry3[0,2,0,0])) | ((~curry1[0,2,0,0] & (~curry2[0,2,0,0] & curry3[0,2,0,0])) | (~curry1[0,2,0,0] & (~curry2[0,2,0,0] & ~curry3[0,2,0,0])))))))
((curry1[0,3,0,0] & (curry2[0,3,0,0] & ~curry3[0,3,0,0])) | ((curry1[0,3,0,0] & (~curry2[0,3,0,0] & curry3[0,3,0,0])) | ((curry1[0,3,0,0] & (~curry2[0,3,0,0] & ~curry3[0,3,0,0])) | ((~curry1[0,3,0,0] & (curry2[0,3,0,0] & ~curry3[0,3,0,0])) | ((~curry1[0,3,0,0] & (~curry2[0,3,0,0] & curry3[0,3,0,0])) | (~curry1[0,3,0,0] & (~curry2[0,3,0,0] & ~curry3[0,3,0,0])))))))
((~pred0[0,1] & (pred0(1) & (pred0(2) & (pred0(3) & (n[0,1] & (~pred1[0,1] & (pred1(1) & (pred1(2) & (~pred1(3) & (v[0,1] & (z[0,1] & a[0,1]))))))))))) | ((~pred0[0,1] & (pred0(1) & (pred0(2) & (pred0(3) & (n[0,1] & (~pred1[0,1] & (pred1(1) & (~pred1(2) & (~pred1(3) & (v[0,1] & (~z[0,1] & a[0,1]))))))))))) | ((~pred0[0,1] & (pred0(1) & (pred0(2) & (pred0(3) & (n[0,1] & (~pred1[0,1] & (~pred1(1) & (pred1(2) & (~pred1(3) & (~v[0,1] & (z[0,1] & a[0,1]))))))))))) | ((~pred0[0,1] & (pred0(1) & (pred0(2) & (pred0(3) & (n[0,1] & (~pred1[0,1] & (~pred1(1) & (~pred1(2) & (~pred1(3) & (~v[0,1] & (~z[0,1] & a[0,1]))))))))))) | ((~pred0[0,1] & (pred0(1) & (pred0(2) & (~pred0(3) & (n[0,1] & (~pred1[0,1] & (pred1(1) & (pred1(2) & (~pred1(3) & (v[0,1] & (z[0,1] & ~a[0,1]))))))))))) | ((~pred0[0,1] & (pred0(1) & (pred0(2) & (~pred0(3) & (n[0,1] & (~pred1[0,1] & (pred1(1) & (~pred1(2) & (~pred1(3) & (v[0,1] & (~z[0,1] & ~a[0,1]))))))))))) | ((~pred0[0,1] & (pred0(1) & (pred0(2) & (~pred0(3) & (n[0,1] & (~pred1[0,1] & (~pred1(1) & (pred1(2) & (~pred1(3) & (~v[0,1] & (z[0,1] & ~a[0,1]))))))))))) | ((~pred0[0,1] & (pred0(1) & (pred0(2) & (~pred0(3) & (n[0,1] & (~pred1[0,1] & (~pred1(1) & (~pred1(2) & (~pred1(3) & (~v[0,1] & (~z[0,1] & ~a[0,1]))))))))))) | ((~pred0[0,1] & (pred0(1) & (~pred0(2) & (pred0(3) & (n[0,1] & (~pred1[0,1] & (pred1(1) & (pred1(2) & (pred1(3) & (v[0,1] & (z[0,1] & a[0,1]))))))))))) | ((~pred0[0,1] & (pred0(1) & (~pred0(2) & (pred0(3) & (n[0,1] & (~pred1[0,1] & (pred1(1) & (~pred1(2) & (pred1(3) & (v[0,1] & (~z[0,1] & a[0,1]))))))))))) | ((~pred0[0,1] & (pred0(1) & (~pred0(2) & (pred0(3) & (n[0,1] & (~pred1[0,1] & (~pred1(1) & (pred1(2) & (pred1(3) & (~v[0,1] & (z[0,1] & a[0,1]))))))))))) | ((~pred0[0,1] & (pred0(1) & (~pred0(2) & (pred0(3) & (n[0,1] & (~pred1[0,1] & (~pred1(1) & (~pred1(2) & (pred1(3) & (~v[0,1] & (~z[0,1] & a[0,1]))))))))))) | ((~pred0[0,1] & (pred0(1) & (~pred0(2) & (~pred0(3) & (n[0,1] & (~pred1[0,1] & (pred1(1) & (pred1(2) & (pred1(3) & (v[0,1] & (z[0,1] & ~a[0,1]))))))))))) | ((~pred0[0,1] & (pred0(1) & (~pred0(2) & (~pred0(3) & (n[0,1] & (~pred1[0,1] & (pred1(1) & (~pred1(2) & (pred1(3) & (v[0,1] & (~z[0,1] & ~a[0,1]))))))))))) | ((~pred0[0,1] & (pred0(1) & (~pred0(2) & (~pred0(3) & (n[0,1] & (~pred1[0,1] & (~pred1(1) & (pred1(2) & (pred1(3) & (~v[0,1] & (z[0,1] & ~a[0,1]))))))))))) | ((~pred0[0,1] & (pred0(1) & (~pred0(2) & (~pred0(3) & (n[0,1] & (~pred1[0,1] & (~pred1(1) & (~pred1(2) & (pred1(3) & (~v[0,1] & (~z[0,1] & ~a[0,1]))))))))))) | ((~pred0[0,1] & (~pred0(1) & (pred0(2) & (pred0(3) & (~n[0,1] & (~pred1[0,1] & (pred1(1) & (pred1(2) & (~pred1(3) & (v[0,1] & (z[0,1] & a[0,1]))))))))))) | ((~pred0[0,1] & (~pred0(1) & (pred0(2) & (pred0(3) & (~n[0,1] & (~pred1[0,1] & (pred1(1) & (~pred1(2) & (~pred1(3) & (v[0,1] & (~z[0,1] & a[0,1]))))))))))) | ((~pred0[0,1] & (~pred0(1) & (pred0(2) & (pred0(3) & (~n[0,1] & (~pred1[0,1] & (~pred1(1) & (pred1(2) & (~pred1(3) & (~v[0,1] & (z[0,1] & a[0,1]))))))))))) | ((~pred0[0,1] & (~pred0(1) & (pred0(2) & (pred0(3) & (~n[0,1] & (~pred1[0,1] & (~pred1(1) & (~pred1(2) & (~pred1(3) & (~v[0,1] & (~z[0,1] & a[0,1]))))))))))) | ((~pred0[0,1] & (~pred0(1) & (pred0(2) & (~pred0(3) & (~n[0,1] & (~pred1[0,1] & (pred1(1) & (pred1(2) & (~pred1(3) & (v[0,1] & (z[0,1] & ~a[0,1]))))))))))) | ((~pred0[0,1] & (~pred0(1) & (pred0(2) & (~pred0(3) & (~n[0,1] & (~pred1[0,1] & (pred1(1) & (~pred1(2) & (~pred1(3) & (v[0,1] & (~z[0,1] & ~a[0,1]))))))))))) | ((~pred0[0,1] & (~pred0(1) & (pred0(2) & (~pred0(3) & (~n[0,1] & (~pred1[0,1] & (~pred1(1) & (pred1(2) & (~pred1(3) & (~v[0,1] & (z[0,1] & ~a[0,1]))))))))))) | ((~pred0[0,1] & (~pred0(1) & (pred0(2) & (~pred0(3) & (~n[0,1] & (~pred1[0,1] & (~pred1(1) & (~pred1(2) & (~pred1(3) & (~v[0,1] & (~z[0,1] & ~a[0,1]))))))))))) | ((~pred0[0,1] & (~pred0(1) & (~pred0(2) & (pred0(3) & (~n[0,1] & (~pred1[0,1] & (pred1(1) & (pred1(2) & (pred1(3) & (v[0,1] & (z[0,1] & a[0,1]))))))))))) | ((~pred0[0,1] & (~pred0(1) & (~pred0(2) & (pred0(3) & (~n[0,1] & (~pred1[0,1] & (pred1(1) & (~pred1(2) & (pred1(3) & (v[0,1] & (~z[0,1] & a[0,1]))))))))))) | ((~pred0[0,1] & (~pred0(1) & (~pred0(2) & (pred0(3) & (~n[0,1] & (~pred1[0,1] & (~pred1(1) & (pred1(2) & (pred1(3) & (~v[0,1] & (z[0,1] & a[0,1]))))))))))) | ((~pred0[0,1] & (~pred0(1) & (~pred0(2) & (pred0(3) & (~n[0,1] & (~pred1[0,1] & (~pred1(1) & (~pred1(2) & (pred1(3) & (~v[0,1] & (~z[0,1] & a[0,1]))))))))))) | ((~pred0[0,1] & (~pred0(1) & (~pred0(2) & (~pred0(3) & (~n[0,1] & (~pred1[0,1] & (pred1(1) & (pred1(2) & (pred1(3) & (v[0,1] & (z[0,1] & ~a[0,1]))))))))))) | ((~pred0[0,1] & (~pred0(1) & (~pred0(2) & (~pred0(3) & (~n[0,1] & (~pred1[0,1] & (pred1(1) & (~pred1(2) & (pred1(3) & (v[0,1] & (~z[0,1] & ~a[0,1]))))))))))) | ((~pred0[0,1] & (~pred0(1) & (~pred0(2) & (~pred0(3) & (~n[0,1] & (~pred1[0,1] & (~pred1(1) & (pred1(2) & (pred1(3) & (~v[0,1] & (z[0,1] & ~a[0,1]))))))))))) | (~pred0[0,1] & (~pred0(1) & (~pred0(2) & (~pred0(3) & (~n[0,1] & (~pred1[0,1] & (~pred1(1) & (~pred1(2) & (pred1(3) & (~v[0,1] & (~z[0,1] & ~a[0,1]))))))))))))))))))))))))))))))))))))))))))
(a[] <-> a[0])
(a[0] <-> a[0,1])
(arg1[] <-> arg1[0])
(arg1[0] <-> arg1[0,0])
(curry1[0,2,0] <-> curry1[0,2,0,0])
(curry1[0,3,0] <-> curry1[0,3,0,0])
(curry2[0,2,0] <-> curry2[0,2,0,0])
(curry2[0,3,0] <-> curry2[0,3,0,0])
(curry3[0,2,0] <-> curry3[0,2,0,0])
(curry3[0,3,0] <-> curry3[0,3,0,0])
(n[0,0] <-> v[0,0])
(z[] <-> z[0])
(z[0] <-> z[0,1])
(pred0(1) <-> curry1[0,2,0])
(pred0(2) <-> curry2[0,2,0])
(pred0(3) <-> curry3[0,2,0])
(pred1(1) <-> curry1[0,3,0])
(pred1(2) <-> curry2[0,3,0])
(pred1(3) <-> curry3[0,3,0])
1
-}

sentence = rget $ (procedure @'[ 'In, 'In, 'In ] sentenceIII) :& (procedure @'[ 'In, 'In, 'Out ] sentenceIIO) :& (procedure @'[ 'In, 'Out, 'In ] sentenceIOI) :& (procedure @'[ 'Out, 'In, 'In ] sentenceOII) :& (procedure @'[ 'Out, 'In, 'Out ] sentenceOIO) :& (procedure @'[ 'Out, 'Out, 'In ] sentenceOOI) :& RNil
  where
    sentenceIII = \arg1 z a -> Logic.once $ do
      -- solution: curry2[0,2,0] curry2[0,2,0,0] n[0,0] v[0,0] pred0(2) ~a[] ~a[0] ~a[0,1] ~arg1[] ~arg1[0] ~arg1[0,0] ~curry1[0] ~curry1[0,2,0] ~curry1[0,2,0,0] ~curry1[0,3,0] ~curry1[0,3,0,0] ~curry2[0] ~curry2[0,3,0] ~curry2[0,3,0,0] ~curry3[0] ~curry3[0,2,0] ~curry3[0,2,0,0] ~curry3[0,3,0] ~curry3[0,3,0,0] ~n[0,1] ~pred0[0,1] ~pred1[0,1] ~v[0,1] ~z[] ~z[0] ~z[0,1] ~pred0(1) ~pred0(3) ~pred1(1) ~pred1(2) ~pred1(3)
      -- cost: 4
      () <- (do
        (S n v) <- pure arg1
        let pred0 = procedure @'[ 'In, 'Out, 'In ] $
              \curry1 curry3 -> do
                (curry2) <- (do
                  (OneTuple (curry2)) <- runProcedure @'[ 'In, 'Out, 'In ] np curry1 curry3
                  pure (curry2)
                 )
                pure (OneTuple (curry2))
        let pred1 = procedure @'[ 'In, 'In, 'In ] $
              \curry1 curry2 curry3 -> do
                () <- (do
                  () <- runProcedure @'[ 'In, 'In, 'In ] vp curry1 curry2 curry3
                  pure ()
                 )
                pure ()
        () <- runProcedure @'[ 'PredMode '[ 'In, 'Out, 'In ], 'In, 'PredMode '[ 'In, 'In, 'In ], 'In, 'In, 'In ] compose' pred0 n pred1 v z a
        pure ()
       )
      pure ()
    
    sentenceIIO = \arg1 z -> do
      -- solution: a[] a[0] a[0,1] curry3[0,2,0] curry3[0,2,0,0] curry3[0,3,0] curry3[0,3,0,0] n[0,0] v[0,0] pred0(3) pred1(3) ~arg1[] ~arg1[0] ~arg1[0,0] ~curry1[0] ~curry1[0,2,0] ~curry1[0,2,0,0] ~curry1[0,3,0] ~curry1[0,3,0,0] ~curry2[0] ~curry2[0,2,0] ~curry2[0,2,0,0] ~curry2[0,3,0] ~curry2[0,3,0,0] ~curry3[0] ~n[0,1] ~pred0[0,1] ~pred1[0,1] ~v[0,1] ~z[] ~z[0] ~z[0,1] ~pred0(1) ~pred0(2) ~pred1(1) ~pred1(2)
      -- cost: 6
      (a) <- (do
        (S n v) <- pure arg1
        let pred0 = procedure @'[ 'In, 'In, 'Out ] $
              \curry1 curry2 -> do
                (curry3) <- (do
                  (OneTuple (curry3)) <- runProcedure @'[ 'In, 'In, 'Out ] np curry1 curry2
                  pure (curry3)
                 )
                pure (OneTuple (curry3))
        let pred1 = procedure @'[ 'In, 'In, 'Out ] $
              \curry1 curry2 -> do
                (curry3) <- (do
                  (OneTuple (curry3)) <- runProcedure @'[ 'In, 'In, 'Out ] vp curry1 curry2
                  pure (curry3)
                 )
                pure (OneTuple (curry3))
        (OneTuple (a)) <- runProcedure @'[ 'PredMode '[ 'In, 'In, 'Out ], 'In, 'PredMode '[ 'In, 'In, 'Out ], 'In, 'In, 'Out ] compose' pred0 n pred1 v z
        pure (a)
       )
      pure (OneTuple (a))
    
    sentenceIOI = \arg1 a -> do
      -- solution: curry2[0,2,0] curry2[0,2,0,0] curry2[0,3,0] curry2[0,3,0,0] n[0,0] v[0,0] z[] z[0] z[0,1] pred0(2) pred1(2) ~a[] ~a[0] ~a[0,1] ~arg1[] ~arg1[0] ~arg1[0,0] ~curry1[0] ~curry1[0,2,0] ~curry1[0,2,0,0] ~curry1[0,3,0] ~curry1[0,3,0,0] ~curry2[0] ~curry3[0] ~curry3[0,2,0] ~curry3[0,2,0,0] ~curry3[0,3,0] ~curry3[0,3,0,0] ~n[0,1] ~pred0[0,1] ~pred1[0,1] ~v[0,1] ~pred0(1) ~pred0(3) ~pred1(1) ~pred1(3)
      -- cost: 6
      (z) <- (do
        (S n v) <- pure arg1
        let pred0 = procedure @'[ 'In, 'Out, 'In ] $
              \curry1 curry3 -> do
                (curry2) <- (do
                  (OneTuple (curry2)) <- runProcedure @'[ 'In, 'Out, 'In ] np curry1 curry3
                  pure (curry2)
                 )
                pure (OneTuple (curry2))
        let pred1 = procedure @'[ 'In, 'Out, 'In ] $
              \curry1 curry3 -> do
                (curry2) <- (do
                  (OneTuple (curry2)) <- runProcedure @'[ 'In, 'Out, 'In ] vp curry1 curry3
                  pure (curry2)
                 )
                pure (OneTuple (curry2))
        (OneTuple (z)) <- runProcedure @'[ 'PredMode '[ 'In, 'Out, 'In ], 'In, 'PredMode '[ 'In, 'Out, 'In ], 'In, 'Out, 'In ] compose' pred0 n pred1 v a
        pure (z)
       )
      pure (OneTuple (z))
    
    sentenceOII = \z a -> do
      -- solution: arg1[] arg1[0] arg1[0,0] curry1[0,2,0] curry1[0,2,0,0] curry1[0,3,0] curry1[0,3,0,0] curry2[0,2,0] curry2[0,2,0,0] n[0,1] v[0,1] pred0(1) pred0(2) pred1(1) ~a[] ~a[0] ~a[0,1] ~curry1[0] ~curry2[0] ~curry2[0,3,0] ~curry2[0,3,0,0] ~curry3[0] ~curry3[0,2,0] ~curry3[0,2,0,0] ~curry3[0,3,0] ~curry3[0,3,0,0] ~n[0,0] ~pred0[0,1] ~pred1[0,1] ~v[0,0] ~z[] ~z[0] ~z[0,1] ~pred0(3) ~pred1(2) ~pred1(3)
      -- cost: 8
      (arg1) <- (do
        let pred0 = procedure @'[ 'Out, 'Out, 'In ] $
              \curry3 -> do
                (curry1,curry2) <- (do
                  (curry1,curry2) <- runProcedure @'[ 'Out, 'Out, 'In ] np curry3
                  pure (curry1,curry2)
                 )
                pure (curry1,curry2)
        let pred1 = procedure @'[ 'Out, 'In, 'In ] $
              \curry2 curry3 -> do
                (curry1) <- (do
                  (OneTuple (curry1)) <- runProcedure @'[ 'Out, 'In, 'In ] vp curry2 curry3
                  pure (curry1)
                 )
                pure (OneTuple (curry1))
        (n,v) <- runProcedure @'[ 'PredMode '[ 'Out, 'Out, 'In ], 'Out, 'PredMode '[ 'Out, 'In, 'In ], 'Out, 'In, 'In ] compose' pred0 pred1 z a
        arg1 <- pure (S n v)
        pure (arg1)
       )
      pure (OneTuple (arg1))
    
    sentenceOIO = \z -> do
      -- solution: a[] a[0] a[0,1] arg1[] arg1[0] arg1[0,0] curry1[0,2,0] curry1[0,2,0,0] curry1[0,3,0] curry1[0,3,0,0] curry3[0,2,0] curry3[0,2,0,0] curry3[0,3,0] curry3[0,3,0,0] n[0,1] v[0,1] pred0(1) pred0(3) pred1(1) pred1(3) ~curry1[0] ~curry2[0] ~curry2[0,2,0] ~curry2[0,2,0,0] ~curry2[0,3,0] ~curry2[0,3,0,0] ~curry3[0] ~n[0,0] ~pred0[0,1] ~pred1[0,1] ~v[0,0] ~z[] ~z[0] ~z[0,1] ~pred0(2) ~pred1(2)
      -- cost: 10
      (a,arg1) <- (do
        let pred0 = procedure @'[ 'Out, 'In, 'Out ] $
              \curry2 -> do
                (curry1,curry3) <- (do
                  (curry1,curry3) <- runProcedure @'[ 'Out, 'In, 'Out ] np curry2
                  pure (curry1,curry3)
                 )
                pure (curry1,curry3)
        let pred1 = procedure @'[ 'Out, 'In, 'Out ] $
              \curry2 -> do
                (curry1,curry3) <- (do
                  (curry1,curry3) <- runProcedure @'[ 'Out, 'In, 'Out ] vp curry2
                  pure (curry1,curry3)
                 )
                pure (curry1,curry3)
        (n,v,a) <- runProcedure @'[ 'PredMode '[ 'Out, 'In, 'Out ], 'Out, 'PredMode '[ 'Out, 'In, 'Out ], 'Out, 'In, 'Out ] compose' pred0 pred1 z
        arg1 <- pure (S n v)
        pure (a,arg1)
       )
      pure (arg1,a)
    
    sentenceOOI = \a -> do
      -- solution: arg1[] arg1[0] arg1[0,0] curry1[0,2,0] curry1[0,2,0,0] curry1[0,3,0] curry1[0,3,0,0] curry2[0,2,0] curry2[0,2,0,0] curry2[0,3,0] curry2[0,3,0,0] n[0,1] v[0,1] z[] z[0] z[0,1] pred0(1) pred0(2) pred1(1) pred1(2) ~a[] ~a[0] ~a[0,1] ~curry1[0] ~curry2[0] ~curry3[0] ~curry3[0,2,0] ~curry3[0,2,0,0] ~curry3[0,3,0] ~curry3[0,3,0,0] ~n[0,0] ~pred0[0,1] ~pred1[0,1] ~v[0,0] ~pred0(3) ~pred1(3)
      -- cost: 10
      (arg1,z) <- (do
        let pred0 = procedure @'[ 'Out, 'Out, 'In ] $
              \curry3 -> do
                (curry1,curry2) <- (do
                  (curry1,curry2) <- runProcedure @'[ 'Out, 'Out, 'In ] np curry3
                  pure (curry1,curry2)
                 )
                pure (curry1,curry2)
        let pred1 = procedure @'[ 'Out, 'Out, 'In ] $
              \curry3 -> do
                (curry1,curry2) <- (do
                  (curry1,curry2) <- runProcedure @'[ 'Out, 'Out, 'In ] vp curry3
                  pure (curry1,curry2)
                 )
                pure (curry1,curry2)
        (n,v,z) <- runProcedure @'[ 'PredMode '[ 'Out, 'Out, 'In ], 'Out, 'PredMode '[ 'Out, 'Out, 'In ], 'Out, 'Out, 'In ] compose' pred0 pred1 a
        arg1 <- pure (S n v)
        pure (arg1,z)
       )
      pure (arg1,z)
    