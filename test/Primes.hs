{-# LANGUAGE DataKinds, FlexibleContexts, NoImplicitPrelude, NoMonomorphismRestriction, TypeApplications #-}
module Primes where

import qualified Control.Monad.Logic as Logic
import Control.Monad.Logic.Moded.Prelude

{- integers/3
integers low high result :- ((if ((<=) low high) then (succ low m, integers m high rest, result = low:rest) else (result = []))).
constraints:
~(<=)[0,0,0]
~high[0,0]
~high[0,0,0,0]
~high[0,0,1,1]
~integers[0,0,1]
~low[0,0]
~low[0,0,0,0]
~succ[0,0,1]
~(low[0,0,1,0] & low[0,0,1,2])
~(m[0,0,1,0] & m[0,0,1,1])
~(rest[0,0,1,1] & rest[0,0,1,2])
~(result[0,0,1,2] & low[0,0,1,2])
~(low[0,0,1,0] | low[0,0,1,2])
(~low[0,0,0,0] & ~high[0,0,0,0])
(m[0,0,1,0] | m[0,0,1,1])
(rest[0,0,1,1] | rest[0,0,1,2])
((low[0,0,1,0] & ~m[0,0,1,0]) | ((~low[0,0,1,0] & m[0,0,1,0]) | (~low[0,0,1,0] & ~m[0,0,1,0])))
((<=)[0] <-> (<=)[0,0])
((<=)[0,0] <-> (<=)[0,0,0])
(high[] <-> high[0])
(high[0] <-> high[0,0])
(high[0,0,1,1] <-> high[])
(integers[0] <-> integers[0,0])
(integers[0,0] <-> integers[0,0,1])
(low[] <-> low[0])
(low[0] <-> low[0,0])
(low[0,0,1,2] <-> rest[0,0,1,2])
(m[0,0,1,1] <-> low[])
(rest[0,0,1,1] <-> result[])
(result[] <-> result[0])
(result[0] <-> result[0,0])
(result[0,0] <-> (result[0,0,1] | result[0,0,2]))
(result[0,0,1] <-> result[0,0,1,2])
(result[0,0,1] <-> result[0,0,2])
(result[0,0,2] <-> result[0,0,2,0])
(succ[0] <-> succ[0,0])
(succ[0,0] <-> succ[0,0,1])
1
-}

integers = rget $ (procedure @'[ 'In, 'In, 'Out ] integersIIO) :& RNil
  where
    integersIIO = \low high -> do
      -- solution: m[0,0,1,0] rest[0,0,1,1] result[] result[0] result[0,0] result[0,0,1] result[0,0,1,2] result[0,0,2] result[0,0,2,0]
      -- cost: 5
      (result) <- (do
        (result) <- Logic.ifte ((do
          guard $ (<=) low high
          pure ()
         )) (\() -> (do
          (OneTuple (m)) <- runProcedure @'[ 'In, 'Out ] succ low
          (OneTuple (rest)) <- integersIIO m high
          result <- pure (low:rest)
          pure (result)
         )) ((do
          result <- pure []
          pure (result)
         ))
        pure (result)
       )
      pure (OneTuple (result))
    
{- remove/3
remove arg1 arg2 arg3 :- ((arg2 = [], arg3 = []); (arg2 = j:js, mod j p m, remove p js njs, if (m = 0) then (result = njs) else (result = j0:njs, j0 = j), arg1 = p, arg3 = result)).
constraints:
~arg1[]
~j[1,3,2]
~m[1,3]
~m[1,3,0,0]
~mod[1]
~remove[1]
~(arg1[1,4] & p[1,4])
~(arg2[1,0] & j[1,0])
~(arg3[1,5] & result[1,5])
~(j[1,0] & j[1,1])
~(j[1,0] & j[1,3])
~(j[1,1] & j[1,3])
~(j0[1,3,2,0] & j0[1,3,2,1])
~(j0[1,3,2,1] & j[1,3,2,1])
~(js[1,0] & js[1,2])
~(m[1,1] & m[1,3])
~(njs[1,2] & njs[1,3])
~(p[1,1] & p[1,2])
~(p[1,1] & p[1,4])
~(p[1,2] & p[1,4])
~(result[1,3] & result[1,5])
~(result[1,3,1,0] & njs[1,3,1,0])
~(result[1,3,2,0] & j0[1,3,2,0])
(j[1,0] | (j[1,1] | j[1,3]))
(j0[1,3,2,0] | j0[1,3,2,1])
(js[1,0] | js[1,2])
(m[1,1] | m[1,3])
(njs[1,2] | njs[1,3])
(p[1,1] | (p[1,2] | p[1,4]))
(result[1,3] | result[1,5])
((~j[1,1] & (~p[1,1] & m[1,1])) | (~j[1,1] & (~p[1,1] & ~m[1,1])))
(arg1[] <-> arg1[1])
(arg1[1] <-> arg1[1,4])
(arg2[] <-> arg2[0])
(arg2[] <-> arg2[1])
(arg2[0] <-> arg2[0,0])
(arg2[1] <-> arg2[1,0])
(arg3[] <-> arg3[0])
(arg3[] <-> arg3[1])
(arg3[0] <-> arg3[0,1])
(arg3[1] <-> arg3[1,5])
(j[1,0] <-> js[1,0])
(j[1,3] <-> j[1,3,2])
(j[1,3,2] <-> j[1,3,2,1])
(j0[1,3,2,0] <-> njs[1,3,2,0])
(js[1,2] <-> arg2[])
(njs[1,2] <-> arg3[])
(njs[1,3] <-> (njs[1,3,1] | njs[1,3,2]))
(njs[1,3,1] <-> njs[1,3,1,0])
(njs[1,3,1] <-> njs[1,3,2])
(njs[1,3,2] <-> njs[1,3,2,0])
(p[1,2] <-> arg1[])
(result[1,3] <-> (result[1,3,1] | result[1,3,2]))
(result[1,3,1] <-> result[1,3,1,0])
(result[1,3,1] <-> result[1,3,2])
(result[1,3,2] <-> result[1,3,2,0])
1
-}

remove = rget $ (procedure @'[ 'In, 'In, 'In ] removeIII) :& (procedure @'[ 'In, 'In, 'Out ] removeIIO) :& RNil
  where
    removeIII = \arg1 arg2 arg3 -> Logic.once $ do
      -- solution: j[1,0] j0[1,3,2,0] js[1,0] m[1,1] njs[1,3] njs[1,3,1] njs[1,3,1,0] njs[1,3,2] njs[1,3,2,0] p[1,4] result[1,5]
      -- cost: 3
      () <- (do
        guard $ arg2 == []
        guard $ arg3 == []
        pure ()
       ) <|> (do
        p <- pure arg1
        (j:js) <- pure arg2
        result <- pure arg3
        (OneTuple (m)) <- runProcedure @'[ 'In, 'In, 'Out ] mod j p
        (njs) <- Logic.ifte ((do
          guard $ m == 0
          pure ()
         )) (\() -> (do
          njs <- pure result
          pure (njs)
         )) ((do
          (j0:njs) <- pure result
          guard $ j0 == j
          pure (njs)
         ))
        () <- removeIII p js njs
        pure ()
       )
      pure ()
    
    removeIIO = \arg1 arg2 -> do
      -- solution: arg3[] arg3[0] arg3[0,1] arg3[1] arg3[1,5] j[1,0] j0[1,3,2,1] js[1,0] m[1,1] njs[1,2] p[1,4] result[1,3] result[1,3,1] result[1,3,1,0] result[1,3,2] result[1,3,2,0]
      -- cost: 4
      (arg3) <- (do
        guard $ arg2 == []
        arg3 <- pure []
        pure (arg3)
       ) <|> (do
        p <- pure arg1
        (j:js) <- pure arg2
        (OneTuple (m)) <- runProcedure @'[ 'In, 'In, 'Out ] mod j p
        (OneTuple (njs)) <- removeIIO p js
        (result) <- Logic.ifte ((do
          guard $ m == 0
          pure ()
         )) (\() -> (do
          result <- pure njs
          pure (result)
         )) ((do
          j0 <- pure j
          result <- pure (j0:njs)
          pure (result)
         ))
        arg3 <- pure result
        pure (arg3)
       )
      pure (OneTuple (arg3))
    
{- sift/2
sift arg1 arg2 :- ((arg1 = [], arg2 = []); (arg1 = p:js, arg2 = p0:ps, p0 = p, remove p js new, sift new ps)).
constraints:
~remove[1]
~sift[1]
~(arg1[1,0] & p[1,0])
~(arg2[1,1] & p0[1,1])
~(js[1,0] & js[1,3])
~(new[1,3] & new[1,4])
~(p[1,0] & p[1,2])
~(p[1,0] & p[1,3])
~(p[1,2] & p[1,3])
~(p0[1,1] & p0[1,2])
~(p0[1,2] & p[1,2])
~(ps[1,1] & ps[1,4])
(js[1,0] | js[1,3])
(new[1,3] | new[1,4])
(p[1,0] | (p[1,2] | p[1,3]))
(p0[1,1] | p0[1,2])
(ps[1,1] | ps[1,4])
((~p[1,3] & (~js[1,3] & new[1,3])) | (~p[1,3] & (~js[1,3] & ~new[1,3])))
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg1[0] <-> arg1[0,0])
(arg1[1] <-> arg1[1,0])
(arg2[] <-> arg2[0])
(arg2[] <-> arg2[1])
(arg2[0] <-> arg2[0,1])
(arg2[1] <-> arg2[1,1])
(new[1,4] <-> arg1[])
(p[1,0] <-> js[1,0])
(p0[1,1] <-> ps[1,1])
(ps[1,4] <-> arg2[])
1
-}

sift = rget $ (procedure @'[ 'In, 'In ] siftII) :& (procedure @'[ 'In, 'Out ] siftIO) :& RNil
  where
    siftII = \arg1 arg2 -> Logic.once $ do
      -- solution: js[1,0] new[1,3] p[1,0] p0[1,1] ps[1,1]
      -- cost: 3
      () <- (do
        guard $ arg1 == []
        guard $ arg2 == []
        pure ()
       ) <|> (do
        (p:js) <- pure arg1
        (p0:ps) <- pure arg2
        guard $ p0 == p
        (OneTuple (new)) <- runProcedure @'[ 'In, 'In, 'Out ] remove p js
        () <- siftII new ps
        pure ()
       )
      pure ()
    
    siftIO = \arg1 -> do
      -- solution: arg2[] arg2[0] arg2[0,1] arg2[1] arg2[1,1] js[1,0] new[1,3] p[1,0] p0[1,2] ps[1,4]
      -- cost: 4
      (arg2) <- (do
        guard $ arg1 == []
        arg2 <- pure []
        pure (arg2)
       ) <|> (do
        (p:js) <- pure arg1
        p0 <- pure p
        (OneTuple (new)) <- runProcedure @'[ 'In, 'In, 'Out ] remove p js
        (OneTuple (ps)) <- siftIO new
        arg2 <- pure (p0:ps)
        pure (arg2)
       )
      pure (OneTuple (arg2))
    
{- primes/2
primes limit ps :- ((integers data0 limit js, data0 = 2, sift js ps)).
constraints:
~integers[0]
~sift[0]
~(data0[0,0] & data0[0,1])
~(js[0,0] & js[0,2])
(~data0[0,0] & (~limit[0,0] & js[0,0]))
(data0[0,0] | data0[0,1])
(js[0,0] | js[0,2])
((~js[0,2] & ps[0,2]) | (~js[0,2] & ~ps[0,2]))
(limit[] <-> limit[0])
(limit[0] <-> limit[0,0])
(ps[] <-> ps[0])
(ps[0] <-> ps[0,2])
1
-}

primes = rget $ (procedure @'[ 'In, 'In ] primesII) :& (procedure @'[ 'In, 'Out ] primesIO) :& RNil
  where
    primesII = \limit ps -> Logic.once $ do
      -- solution: data0[0,1] js[0,0]
      -- cost: 3
      () <- (do
        data0 <- pure 2
        (OneTuple (js)) <- runProcedure @'[ 'In, 'In, 'Out ] integers data0 limit
        () <- runProcedure @'[ 'In, 'In ] sift js ps
        pure ()
       )
      pure ()
    
    primesIO = \limit -> do
      -- solution: data0[0,1] js[0,0] ps[] ps[0] ps[0,2]
      -- cost: 4
      (ps) <- (do
        data0 <- pure 2
        (OneTuple (js)) <- runProcedure @'[ 'In, 'In, 'Out ] integers data0 limit
        (OneTuple (ps)) <- runProcedure @'[ 'In, 'Out ] sift js
        pure (ps)
       )
      pure (OneTuple (ps))
    