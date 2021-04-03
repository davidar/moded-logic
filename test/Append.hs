module Append where
import Control.Applicative
import Control.Monad.Logic

{- append/3
append arg1 arg2 arg3 :- ((arg1 = [], arg2 = x, arg3 = x, ()); ((arg1 = h0 : t, h0 = h), arg2 = b, (arg3 = h0 : tb, h0 = h), (append t b tb))).
constraints:
b[1]
b[]
h0[1]
h0[]
h[1]
h[]
t[1]
t[]
tb[1]
tb[]
x[0]
x[]
~(arg1[1,0,0] & h0[1,0,0])
~(arg2[0,1] & x[0,1])
~(arg2[1,1] & b[1,1])
~(arg3[0,2] & x[0,2])
~(arg3[1,2,0] & h0[1,2,0])
~(b[1,1] & b[1,3])
~(h0[1,0,0] & h0[1,0,1])
~(h0[1,0,1] & h[1,0,1])
~(h0[1,0] & h0[1,2])
~(h0[1,2,0] & h0[1,2,1])
~(h0[1,2,1] & h[1,2,1])
~(h[1,0] & h[1,2])
~(t[1,0] & t[1,3])
~(tb[1,2] & tb[1,3])
~(x[0,1] & x[0,2])
(arg1[0] <-> arg1[0,0])
(arg1[1,0] <-> arg1[1,0,0])
(arg1[1] <-> arg1[1,0])
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg2[0] <-> arg2[0,1])
(arg2[1] <-> arg2[1,1])
(arg2[] <-> arg2[0])
(arg2[] <-> arg2[1])
(arg3[0] <-> arg3[0,2])
(arg3[1,2] <-> arg3[1,2,0])
(arg3[1] <-> arg3[1,2])
(arg3[] <-> arg3[0])
(arg3[] <-> arg3[1])
(b[1,3,0] <-> arg2[])
(b[1,3] <-> b[1,3,0])
(b[1] <-> (b[1,1] | b[1,3]))
(h0[1,0,0] <-> t[1,0,0])
(h0[1,0] <-> (h0[1,0,0] | h0[1,0,1]))
(h0[1,2,0] <-> tb[1,2,0])
(h0[1,2] <-> (h0[1,2,0] | h0[1,2,1]))
(h0[1] <-> (h0[1,0] | h0[1,2]))
(h[1,0] <-> h[1,0,1])
(h[1,2] <-> h[1,2,1])
(h[1] <-> (h[1,0] | h[1,2]))
(t[1,0] <-> t[1,0,0])
(t[1,3,0] <-> arg1[])
(t[1,3] <-> t[1,3,0])
(t[1] <-> (t[1,0] | t[1,3]))
(tb[1,2] <-> tb[1,2,0])
(tb[1,3,0] <-> arg3[])
(tb[1,3] <-> tb[1,3,0])
(tb[1] <-> (tb[1,2] | tb[1,3]))
(x[0] <-> (x[0,1] | x[0,2]))
-}
-- mode ordering failure, cyclic dependency: [2] (arg3::out = h0::in : tb::in, h0::in = h::out) -> [0] (h0::out = h::in, arg1::out = h0::in : t::in)
-- mode ordering failure, cyclic dependency: [2] (h0::out = h::in, arg3::out = h0::in : tb::in) -> [0] (arg1::out = h0::in : t::in, h0::in = h::out)

-- mode ordering failure, cyclic dependency: [3] (append t::in b::in tb::out) -> [2] (arg3::out = h0::in : tb::in, h0::in = h::out) -> [0] (arg1::in = h0::out : t::out, h0::in = h::in)

-- mode ordering failure, cyclic dependency: [3] (append t::out b::in tb::in) -> [0] (arg1::out = h0::in : t::in, h0::in = h::out) -> [2] (arg3::in = h0::out : tb::out, h0::in = h::in)

-- mode ordering failure, cyclic dependency: [3] (append t::out b::in tb::in) -> [0] (arg1::out = h0::in : t::in, h0::in = h::out) -> [2] (arg3::in = h0::out : tb::out, h0::in = h::in)

-- mode ordering failure, cyclic dependency: [3] (append t::out b::out tb::in) -> [0] (arg1::out = h0::in : t::in, h0::in = h::out) -> [2] (arg3::in = h0::out : tb::out, h0::in = h::in)

append_iio arg1 arg2 = do
  (arg3) <- (do
    guard $ arg1 == []
    x <- pure arg2
    arg3 <- pure x
    () <- (do
      
      pure ()
     )
    pure (arg3)
   ) <|> (do
    (h,h0,t) <- (do
      (h0:t) <- pure arg1
      h <- pure h0
      pure (h,h0,t)
     )
    b <- pure arg2
    (tb) <- (do
      (tb) <- append_iio t b
      pure (tb)
     )
    (arg3) <- (do
      arg3 <- pure (h0:tb)
      guard $ h0 == h
      pure (arg3)
     )
    pure (arg3)
   )
  pure (arg3)
append_oii arg2 arg3 = do
  (arg1) <- (do
    arg1 <- pure []
    x <- pure arg2
    guard $ arg3 == x
    () <- (do
      
      pure ()
     )
    pure (arg1)
   ) <|> (do
    b <- pure arg2
    (h,h0,tb) <- (do
      (h0:tb) <- pure arg3
      h <- pure h0
      pure (h,h0,tb)
     )
    (t) <- (do
      (t) <- append_oii b tb
      pure (t)
     )
    (arg1) <- (do
      arg1 <- pure (h0:t)
      guard $ h0 == h
      pure (arg1)
     )
    pure (arg1)
   )
  pure (arg1)
--append_oii arg2 arg3 = do
--  (arg1) <- (do
--    arg1 <- pure []
--    x <- pure arg3
--    guard $ arg2 == x
--    () <- (do
--      
--      pure ()
--     )
--    pure (arg1)
--   ) <|> (do
--    b <- pure arg2
--    (h,h0,tb) <- (do
--      (h0:tb) <- pure arg3
--      h <- pure h0
--      pure (h,h0,tb)
--     )
--    (t) <- (do
--      (t) <- append_oii b tb
--      pure (t)
--     )
--    (arg1) <- (do
--      arg1 <- pure (h0:t)
--      guard $ h0 == h
--      pure (arg1)
--     )
--    pure (arg1)
--   )
--  pure (arg1)

append_ooi arg3 = do
  (arg1,arg2) <- (do
    arg1 <- pure []
    x <- pure arg3
    arg2 <- pure x
    () <- (do
      
      pure ()
     )
    pure (arg1,arg2)
   ) <|> (do
    (h,h0,tb) <- (do
      (h0:tb) <- pure arg3
      h <- pure h0
      pure (h,h0,tb)
     )
    (b,t) <- (do
      (t,b) <- append_ooi tb
      pure (b,t)
     )
    (arg1) <- (do
      arg1 <- pure (h0:t)
      guard $ h0 == h
      pure (arg1)
     )
    arg2 <- pure b
    pure (arg1,arg2)
   )
  pure (arg1,arg2)
{- append/4
append arg1 arg2 arg3 arg4 :- ((arg1 = a, arg2 = b, arg3 = c, arg4 = abc, (append a b ab, append ab c abc))).
constraints:
a[0]
a[]
ab[0,4]
ab[0]
ab[]
abc[0]
abc[]
b[0]
b[]
c[0]
c[]
~(a[0,0] & a[0,4])
~(ab[0,4,0] & ab[0,4,1])
~(abc[0,3] & abc[0,4])
~(arg1[0,0] & a[0,0])
~(arg2[0,1] & b[0,1])
~(arg3[0,2] & c[0,2])
~(arg4[0,3] & abc[0,3])
~(b[0,1] & b[0,4])
~(c[0,2] & c[0,4])
((a[0,4,0] & (b[0,4,0] & ~ab[0,4,0])) | ((a[0,4,0] & (~b[0,4,0] & ~ab[0,4,0])) | (~a[0,4,0] & (~b[0,4,0] & ab[0,4,0]))))
((ab[0,4,1] & (c[0,4,1] & ~abc[0,4,1])) | ((ab[0,4,1] & (~c[0,4,1] & ~abc[0,4,1])) | (~ab[0,4,1] & (~c[0,4,1] & abc[0,4,1]))))
(a[0,4] <-> a[0,4,0])
(a[0] <-> (a[0,0] | a[0,4]))
(ab[0,4] <-> (ab[0,4,0] | ab[0,4,1]))
(ab[0] <-> ab[0,4])
(abc[0,4] <-> abc[0,4,1])
(abc[0] <-> (abc[0,3] | abc[0,4]))
(arg1[0] <-> arg1[0,0])
(arg1[] <-> arg1[0])
(arg2[0] <-> arg2[0,1])
(arg2[] <-> arg2[0])
(arg3[0] <-> arg3[0,2])
(arg3[] <-> arg3[0])
(arg4[0] <-> arg4[0,3])
(arg4[] <-> arg4[0])
(b[0,4] <-> b[0,4,0])
(b[0] <-> (b[0,1] | b[0,4]))
(c[0,4] <-> c[0,4,1])
(c[0] <-> (c[0,2] | c[0,4]))
-}
append_iiii arg1 arg2 arg3 arg4 = do
  () <- (do
    a <- pure arg1
    b <- pure arg2
    c <- pure arg3
    (abc) <- (do
      (ab) <- append_iio a b
      (abc) <- append_iio ab c
      pure (abc)
     )
    guard $ arg4 == abc
    pure ()
   )
  pure ()
--append_iiii arg1 arg2 arg3 arg4 = do
--  () <- (do
--    abc <- pure arg4
--    (a,b,c) <- (do
--      (ab,c) <- append_ooi abc
--      (a,b) <- append_ooi ab
--      pure (a,b,c)
--     )
--    guard $ arg1 == a
--    guard $ arg2 == b
--    guard $ arg3 == c
--    pure ()
--   )
--  pure ()

--append_iiii arg1 arg2 arg3 arg4 = do
--  () <- (do
--    b <- pure arg2
--    abc <- pure arg4
--    (a,c) <- (do
--      (ab,c) <- append_ooi abc
--      (a) <- append_oii b ab
--      pure (a,c)
--     )
--    guard $ arg1 == a
--    guard $ arg3 == c
--    pure ()
--   )
--  pure ()

--append_iiii arg1 arg2 arg3 arg4 = do
--  () <- (do
--    b <- pure arg2
--    c <- pure arg3
--    abc <- pure arg4
--    (a) <- (do
--      (ab) <- append_oii c abc
--      (a) <- append_oii b ab
--      pure (a)
--     )
--    guard $ arg1 == a
--    pure ()
--   )
--  pure ()

--append_iiii arg1 arg2 arg3 arg4 = do
--  () <- (do
--    c <- pure arg3
--    abc <- pure arg4
--    (a,b) <- (do
--      (ab) <- append_oii c abc
--      (a,b) <- append_ooi ab
--      pure (a,b)
--     )
--    guard $ arg1 == a
--    guard $ arg2 == b
--    pure ()
--   )
--  pure ()

append_iiio arg1 arg2 arg3 = do
  (arg4) <- (do
    a <- pure arg1
    b <- pure arg2
    c <- pure arg3
    (abc) <- (do
      (ab) <- append_iio a b
      (abc) <- append_iio ab c
      pure (abc)
     )
    arg4 <- pure abc
    pure (arg4)
   )
  pure (arg4)
append_iioi arg1 arg2 arg4 = do
  (arg3) <- (do
    abc <- pure arg4
    (a,b,c) <- (do
      (ab,c) <- append_ooi abc
      (a,b) <- append_ooi ab
      pure (a,b,c)
     )
    guard $ arg1 == a
    guard $ arg2 == b
    arg3 <- pure c
    pure (arg3)
   )
  pure (arg3)
--append_iioi arg1 arg2 arg4 = do
--  (arg3) <- (do
--    b <- pure arg2
--    abc <- pure arg4
--    (a,c) <- (do
--      (ab,c) <- append_ooi abc
--      (a) <- append_oii b ab
--      pure (a,c)
--     )
--    guard $ arg1 == a
--    arg3 <- pure c
--    pure (arg3)
--   )
--  pure (arg3)

append_ioii arg1 arg3 arg4 = do
  (arg2) <- (do
    abc <- pure arg4
    (a,b,c) <- (do
      (ab,c) <- append_ooi abc
      (a,b) <- append_ooi ab
      pure (a,b,c)
     )
    guard $ arg1 == a
    arg2 <- pure b
    guard $ arg3 == c
    pure (arg2)
   )
  pure (arg2)
--append_ioii arg1 arg3 arg4 = do
--  (arg2) <- (do
--    c <- pure arg3
--    abc <- pure arg4
--    (a,b) <- (do
--      (ab) <- append_oii c abc
--      (a,b) <- append_ooi ab
--      pure (a,b)
--     )
--    guard $ arg1 == a
--    arg2 <- pure b
--    pure (arg2)
--   )
--  pure (arg2)

append_iooi arg1 arg4 = do
  (arg2,arg3) <- (do
    abc <- pure arg4
    (a,b,c) <- (do
      (ab,c) <- append_ooi abc
      (a,b) <- append_ooi ab
      pure (a,b,c)
     )
    guard $ arg1 == a
    arg2 <- pure b
    arg3 <- pure c
    pure (arg2,arg3)
   )
  pure (arg2,arg3)
append_oiii arg2 arg3 arg4 = do
  (arg1) <- (do
    abc <- pure arg4
    (a,b,c) <- (do
      (ab,c) <- append_ooi abc
      (a,b) <- append_ooi ab
      pure (a,b,c)
     )
    arg1 <- pure a
    guard $ arg2 == b
    guard $ arg3 == c
    pure (arg1)
   )
  pure (arg1)
--append_oiii arg2 arg3 arg4 = do
--  (arg1) <- (do
--    b <- pure arg2
--    abc <- pure arg4
--    (a,c) <- (do
--      (ab,c) <- append_ooi abc
--      (a) <- append_oii b ab
--      pure (a,c)
--     )
--    arg1 <- pure a
--    guard $ arg3 == c
--    pure (arg1)
--   )
--  pure (arg1)

--append_oiii arg2 arg3 arg4 = do
--  (arg1) <- (do
--    b <- pure arg2
--    c <- pure arg3
--    abc <- pure arg4
--    (a) <- (do
--      (ab) <- append_oii c abc
--      (a) <- append_oii b ab
--      pure (a)
--     )
--    arg1 <- pure a
--    pure (arg1)
--   )
--  pure (arg1)

--append_oiii arg2 arg3 arg4 = do
--  (arg1) <- (do
--    c <- pure arg3
--    abc <- pure arg4
--    (a,b) <- (do
--      (ab) <- append_oii c abc
--      (a,b) <- append_ooi ab
--      pure (a,b)
--     )
--    arg1 <- pure a
--    guard $ arg2 == b
--    pure (arg1)
--   )
--  pure (arg1)

append_oioi arg2 arg4 = do
  (arg1,arg3) <- (do
    abc <- pure arg4
    (a,b,c) <- (do
      (ab,c) <- append_ooi abc
      (a,b) <- append_ooi ab
      pure (a,b,c)
     )
    arg1 <- pure a
    guard $ arg2 == b
    arg3 <- pure c
    pure (arg1,arg3)
   )
  pure (arg1,arg3)
--append_oioi arg2 arg4 = do
--  (arg1,arg3) <- (do
--    b <- pure arg2
--    abc <- pure arg4
--    (a,c) <- (do
--      (ab,c) <- append_ooi abc
--      (a) <- append_oii b ab
--      pure (a,c)
--     )
--    arg1 <- pure a
--    arg3 <- pure c
--    pure (arg1,arg3)
--   )
--  pure (arg1,arg3)

append_ooii arg3 arg4 = do
  (arg1,arg2) <- (do
    abc <- pure arg4
    (a,b,c) <- (do
      (ab,c) <- append_ooi abc
      (a,b) <- append_ooi ab
      pure (a,b,c)
     )
    arg1 <- pure a
    arg2 <- pure b
    guard $ arg3 == c
    pure (arg1,arg2)
   )
  pure (arg1,arg2)
--append_ooii arg3 arg4 = do
--  (arg1,arg2) <- (do
--    c <- pure arg3
--    abc <- pure arg4
--    (a,b) <- (do
--      (ab) <- append_oii c abc
--      (a,b) <- append_ooi ab
--      pure (a,b)
--     )
--    arg1 <- pure a
--    arg2 <- pure b
--    pure (arg1,arg2)
--   )
--  pure (arg1,arg2)

append_oooi arg4 = do
  (arg1,arg2,arg3) <- (do
    abc <- pure arg4
    (a,b,c) <- (do
      (ab,c) <- append_ooi abc
      (a,b) <- append_ooi ab
      pure (a,b,c)
     )
    arg1 <- pure a
    arg2 <- pure b
    arg3 <- pure c
    pure (arg1,arg2,arg3)
   )
  pure (arg1,arg2,arg3)
{- reverse/2
reverse arg1 arg2 :- ((arg1 = [], arg2 = [], ()); ((arg1 = h0 : t, h0 = h), arg2 = l, (reverse t r, (append r data1 l, data0 = [], (data1 = h0 : data0, h0 = h))))).
constraints:
data0[1,2,1]
data0[1,2]
data0[1]
data0[]
data1[1,2,1]
data1[1,2]
data1[1]
data1[]
h0[1]
h0[]
h[1]
h[]
l[1]
l[]
r[1,2]
r[1]
r[]
t[1]
t[]
~(arg1[1,0,0] & h0[1,0,0])
~(arg2[1,1] & l[1,1])
~(data0[1,2,1,1] & data0[1,2,1,2])
~(data1[1,2,1,0] & data1[1,2,1,2])
~(data1[1,2,1,2,0] & h0[1,2,1,2,0])
~(h0[1,0,0] & h0[1,0,1])
~(h0[1,0,1] & h[1,0,1])
~(h0[1,0] & h0[1,2])
~(h0[1,2,1,2,0] & h0[1,2,1,2,1])
~(h0[1,2,1,2,1] & h[1,2,1,2,1])
~(h[1,0] & h[1,2])
~(l[1,1] & l[1,2])
~(r[1,2,0] & r[1,2,1])
~(t[1,0] & t[1,2])
((r[1,2,1,0] & (data1[1,2,1,0] & ~l[1,2,1,0])) | ((r[1,2,1,0] & (~data1[1,2,1,0] & ~l[1,2,1,0])) | (~r[1,2,1,0] & (~data1[1,2,1,0] & l[1,2,1,0]))))
(arg1[0] <-> arg1[0,0])
(arg1[1,0] <-> arg1[1,0,0])
(arg1[1] <-> arg1[1,0])
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg2[0] <-> arg2[0,1])
(arg2[1] <-> arg2[1,1])
(arg2[] <-> arg2[0])
(arg2[] <-> arg2[1])
(data0[1,2,1,2] <-> data0[1,2,1,2,0])
(data0[1,2,1] <-> (data0[1,2,1,1] | data0[1,2,1,2]))
(data0[1,2] <-> data0[1,2,1])
(data0[1] <-> data0[1,2])
(data1[1,2,1,2] <-> data1[1,2,1,2,0])
(data1[1,2,1] <-> (data1[1,2,1,0] | data1[1,2,1,2]))
(data1[1,2] <-> data1[1,2,1])
(data1[1] <-> data1[1,2])
(h0[1,0,0] <-> t[1,0,0])
(h0[1,0] <-> (h0[1,0,0] | h0[1,0,1]))
(h0[1,2,1,2,0] <-> data0[1,2,1,2,0])
(h0[1,2,1,2] <-> (h0[1,2,1,2,0] | h0[1,2,1,2,1]))
(h0[1,2,1] <-> h0[1,2,1,2])
(h0[1,2] <-> h0[1,2,1])
(h0[1] <-> (h0[1,0] | h0[1,2]))
(h[1,0] <-> h[1,0,1])
(h[1,2,1,2] <-> h[1,2,1,2,1])
(h[1,2,1] <-> h[1,2,1,2])
(h[1,2] <-> h[1,2,1])
(h[1] <-> (h[1,0] | h[1,2]))
(l[1,2,1] <-> l[1,2,1,0])
(l[1,2] <-> l[1,2,1])
(l[1] <-> (l[1,1] | l[1,2]))
(r[1,2,0] <-> arg2[])
(r[1,2,1] <-> r[1,2,1,0])
(r[1,2] <-> (r[1,2,0] | r[1,2,1]))
(r[1] <-> r[1,2])
(t[1,0] <-> t[1,0,0])
(t[1,2,0] <-> arg1[])
(t[1,2] <-> t[1,2,0])
(t[1] <-> (t[1,0] | t[1,2]))
-}
-- mode ordering failure, cyclic dependency: [2] ((append r::out data1::out l::in, (data1::in = h0::out : data0::out, h0::in = h::in), data0::in = []), reverse t::out r::in) -> [0] (arg1::out = h0::in : t::in, h0::in = h::out)
-- mode ordering failure, cyclic dependency: [2] ((append r::out data1::out l::in, data0::out = [], (data1::in = h0::in : data0::in, h0::in = h::out)), reverse t::in r::in) -> [0] (arg1::in = h0::out : t::out, h0::in = h::in)

-- mode ordering failure, cyclic dependency: [2] ((append r::out data1::out l::in, data0::out = [], (data1::in = h0::in : data0::in, h0::in = h::out)), reverse t::out r::in) -> [0] (h0::out = h::in, arg1::out = h0::in : t::in)

-- mode ordering failure, cyclic dependency: [2] ((append r::out data1::out l::in, data0::out = [], (h0::out = h::in, data1::in = h0::in : data0::in)), reverse t::out r::in) -> [0] (arg1::out = h0::in : t::in, h0::in = h::out)

-- mode ordering failure, cyclic dependency: [2] ((data0::out = [], (data1::out = h0::in : data0::in, h0::in = h::out), append r::out data1::in l::in), reverse t::in r::in) -> [0] (arg1::in = h0::out : t::out, h0::in = h::in)

-- mode ordering failure, cyclic dependency: [2] ((data0::out = [], (data1::out = h0::in : data0::in, h0::in = h::out), append r::out data1::in l::in), reverse t::out r::in) -> [0] (h0::out = h::in, arg1::out = h0::in : t::in)

-- mode ordering failure, cyclic dependency: [2] ((data0::out = [], (h0::out = h::in, data1::out = h0::in : data0::in), append r::out data1::in l::in), reverse t::out r::in) -> [0] (arg1::out = h0::in : t::in, h0::in = h::out)

-- mode ordering failure, cyclic dependency: [2] (reverse t::in r::out, (data0::out = [], (data1::out = h0::in : data0::in, h0::in = h::out), append r::in data1::in l::out)) -> [0] (arg1::in = h0::out : t::out, h0::in = h::in)

-- mode ordering failure, cyclic dependency: [2] (reverse t::out r::out, (data0::out = [], (data1::out = h0::in : data0::in, h0::in = h::out), append r::in data1::in l::out)) -> [0] (h0::out = h::in, arg1::out = h0::in : t::in)

-- mode ordering failure, cyclic dependency: [2] (reverse t::out r::out, (data0::out = [], (h0::out = h::in, data1::out = h0::in : data0::in), append r::in data1::in l::out)) -> [0] (arg1::out = h0::in : t::in, h0::in = h::out)

reverse_ii arg1 arg2 = do
  () <- (do
    guard $ arg1 == []
    guard $ arg2 == []
    () <- (do
      
      pure ()
     )
    pure ()
   ) <|> (do
    (h,h0,t) <- (do
      (h0:t) <- pure arg1
      h <- pure h0
      pure (h,h0,t)
     )
    l <- pure arg2
    () <- (do
      (r) <- (do
        (r,data1) <- append_ooi l
        data0 <- pure []
        () <- (do
          guard $ data1 == (h0:data0)
          guard $ h0 == h
          pure ()
         )
        pure (r)
       )
      () <- reverse_ii t r
      pure ()
     )
    pure ()
   )
  pure ()
--reverse_ii arg1 arg2 = do
--  () <- (do
--    guard $ arg1 == []
--    guard $ arg2 == []
--    () <- (do
--      
--      pure ()
--     )
--    pure ()
--   ) <|> (do
--    (h,h0,t) <- (do
--      (h0:t) <- pure arg1
--      h <- pure h0
--      pure (h,h0,t)
--     )
--    l <- pure arg2
--    () <- (do
--      (r) <- (do
--        data0 <- pure []
--        (data1) <- (do
--          data1 <- pure (h0:data0)
--          guard $ h0 == h
--          pure (data1)
--         )
--        (r) <- append_oii data1 l
--        pure (r)
--       )
--      () <- reverse_ii t r
--      pure ()
--     )
--    pure ()
--   )
--  pure ()

reverse_io arg1 = do
  (arg2) <- (do
    guard $ arg1 == []
    arg2 <- pure []
    () <- (do
      
      pure ()
     )
    pure (arg2)
   ) <|> (do
    (h,h0,t) <- (do
      (h0:t) <- pure arg1
      h <- pure h0
      pure (h,h0,t)
     )
    (l) <- (do
      (r) <- reverse_io t
      (l) <- (do
        data0 <- pure []
        (data1) <- (do
          data1 <- pure (h0:data0)
          guard $ h0 == h
          pure (data1)
         )
        (l) <- append_iio r data1
        pure (l)
       )
      pure (l)
     )
    arg2 <- pure l
    pure (arg2)
   )
  pure (arg2)
reverse_oi arg2 = do
  (arg1) <- (do
    arg1 <- pure []
    guard $ arg2 == []
    () <- (do
      
      pure ()
     )
    pure (arg1)
   ) <|> (do
    l <- pure arg2
    (h,h0,t) <- (do
      (h,h0,r) <- (do
        (r,data1) <- append_ooi l
        (data0,h,h0) <- (do
          (h0:data0) <- pure data1
          h <- pure h0
          pure (data0,h,h0)
         )
        guard $ data0 == []
        pure (h,h0,r)
       )
      (t) <- reverse_oi r
      pure (h,h0,t)
     )
    (arg1) <- (do
      arg1 <- pure (h0:t)
      guard $ h0 == h
      pure (arg1)
     )
    pure (arg1)
   )
  pure (arg1)
{- palindrome/1
palindrome arg1 :- ((arg1 = a, ((reverse a0 a1, a0 = a, a1 = a)))).
constraints:
a0[0,1,0]
a0[0,1]
a0[0]
a0[]
a1[0,1,0]
a1[0,1]
a1[0]
a1[]
a[0]
a[]
~(a0[0,1,0,0] & a0[0,1,0,1])
~(a0[0,1,0,1] & a[0,1,0,1])
~(a1[0,1,0,0] & a1[0,1,0,2])
~(a1[0,1,0,2] & a[0,1,0,2])
~(a[0,0] & a[0,1])
~(a[0,1,0,1] & a[0,1,0,2])
~(arg1[0,0] & a[0,0])
((a0[0,1,0,0] & ~a1[0,1,0,0]) | ((~a0[0,1,0,0] & a1[0,1,0,0]) | (~a0[0,1,0,0] & ~a1[0,1,0,0])))
(a0[0,1,0] <-> (a0[0,1,0,0] | a0[0,1,0,1]))
(a0[0,1] <-> a0[0,1,0])
(a0[0] <-> a0[0,1])
(a1[0,1,0] <-> (a1[0,1,0,0] | a1[0,1,0,2]))
(a1[0,1] <-> a1[0,1,0])
(a1[0] <-> a1[0,1])
(a[0,1,0] <-> (a[0,1,0,1] | a[0,1,0,2]))
(a[0,1] <-> a[0,1,0])
(a[0] <-> (a[0,0] | a[0,1]))
(arg1[0] <-> arg1[0,0])
(arg1[] <-> arg1[0])
-}
-- mode ordering failure, cyclic dependency: [2] a1::in = a::out -> [1] a0::out = a::in -> [0] reverse a0::in a1::out
-- mode ordering failure, cyclic dependency: [2] a1::in = a::out -> [1] a0::out = a::in -> [0] reverse a0::in a1::out

-- mode ordering failure, cyclic dependency: [2] a1::out = a::in -> [0] reverse a0::out a1::in -> [1] a0::in = a::out

-- mode ordering failure, cyclic dependency: [2] a1::out = a::in -> [0] reverse a0::out a1::in -> [1] a0::in = a::out

palindrome_i arg1 = do
  () <- (do
    a <- pure arg1
    () <- (do
      () <- (do
        a0 <- pure a
        (a1) <- reverse_io a0
        guard $ a1 == a
        pure ()
       )
      pure ()
     )
    pure ()
   )
  pure ()
--palindrome_i arg1 = do
--  () <- (do
--    a <- pure arg1
--    () <- (do
--      () <- (do
--        a0 <- pure a
--        a1 <- pure a
--        () <- reverse_ii a0 a1
--        pure ()
--       )
--      pure ()
--     )
--    pure ()
--   )
--  pure ()

--palindrome_i arg1 = do
--  () <- (do
--    a <- pure arg1
--    () <- (do
--      () <- (do
--        a1 <- pure a
--        (a0) <- reverse_oi a1
--        guard $ a0 == a
--        pure ()
--       )
--      pure ()
--     )
--    pure ()
--   )
--  pure ()

{- duplicate/2
duplicate arg1 arg2 :- ((arg1 = a, arg2 = b, ((append a0 a1 b, a0 = a, a1 = a)))).
constraints:
a0[0,2,0]
a0[0,2]
a0[0]
a0[]
a1[0,2,0]
a1[0,2]
a1[0]
a1[]
a[0]
a[]
b[0]
b[]
~(a0[0,2,0,0] & a0[0,2,0,1])
~(a0[0,2,0,1] & a[0,2,0,1])
~(a1[0,2,0,0] & a1[0,2,0,2])
~(a1[0,2,0,2] & a[0,2,0,2])
~(a[0,0] & a[0,2])
~(a[0,2,0,1] & a[0,2,0,2])
~(arg1[0,0] & a[0,0])
~(arg2[0,1] & b[0,1])
~(b[0,1] & b[0,2])
((a0[0,2,0,0] & (a1[0,2,0,0] & ~b[0,2,0,0])) | ((a0[0,2,0,0] & (~a1[0,2,0,0] & ~b[0,2,0,0])) | (~a0[0,2,0,0] & (~a1[0,2,0,0] & b[0,2,0,0]))))
(a0[0,2,0] <-> (a0[0,2,0,0] | a0[0,2,0,1]))
(a0[0,2] <-> a0[0,2,0])
(a0[0] <-> a0[0,2])
(a1[0,2,0] <-> (a1[0,2,0,0] | a1[0,2,0,2]))
(a1[0,2] <-> a1[0,2,0])
(a1[0] <-> a1[0,2])
(a[0,2,0] <-> (a[0,2,0,1] | a[0,2,0,2]))
(a[0,2] <-> a[0,2,0])
(a[0] <-> (a[0,0] | a[0,2]))
(arg1[0] <-> arg1[0,0])
(arg1[] <-> arg1[0])
(arg2[0] <-> arg2[0,1])
(arg2[] <-> arg2[0])
(b[0,2,0] <-> b[0,2,0,0])
(b[0,2] <-> b[0,2,0])
(b[0] <-> (b[0,1] | b[0,2]))
-}
-- mode ordering failure, cyclic dependency: [2] a1::out = a::in -> [0] append a0::out a1::in b::in -> [1] a0::in = a::out
-- mode ordering failure, cyclic dependency: [2] a1::out = a::in -> [0] append a0::out a1::in b::in -> [1] a0::in = a::out

duplicate_ii arg1 arg2 = do
  () <- (do
    a <- pure arg1
    (b) <- (do
      (b) <- (do
        a0 <- pure a
        a1 <- pure a
        (b) <- append_iio a0 a1
        pure (b)
       )
      pure (b)
     )
    guard $ arg2 == b
    pure ()
   )
  pure ()
--duplicate_ii arg1 arg2 = do
--  () <- (do
--    a <- pure arg1
--    b <- pure arg2
--    () <- (do
--      () <- (do
--        (a0,a1) <- append_ooi b
--        guard $ a0 == a
--        guard $ a1 == a
--        pure ()
--       )
--      pure ()
--     )
--    pure ()
--   )
--  pure ()

--duplicate_ii arg1 arg2 = do
--  () <- (do
--    a <- pure arg1
--    b <- pure arg2
--    () <- (do
--      () <- (do
--        a1 <- pure a
--        (a0) <- append_oii a1 b
--        guard $ a0 == a
--        pure ()
--       )
--      pure ()
--     )
--    pure ()
--   )
--  pure ()

--duplicate_ii arg1 arg2 = do
--  () <- (do
--    b <- pure arg2
--    (a) <- (do
--      (a) <- (do
--        (a0,a1) <- append_ooi b
--        a <- pure a0
--        guard $ a1 == a
--        pure (a)
--       )
--      pure (a)
--     )
--    guard $ arg1 == a
--    pure ()
--   )
--  pure ()

--duplicate_ii arg1 arg2 = do
--  () <- (do
--    b <- pure arg2
--    (a) <- (do
--      (a) <- (do
--        (a0,a1) <- append_ooi b
--        a <- pure a1
--        guard $ a0 == a
--        pure (a)
--       )
--      pure (a)
--     )
--    guard $ arg1 == a
--    pure ()
--   )
--  pure ()

duplicate_io arg1 = do
  (arg2) <- (do
    a <- pure arg1
    (b) <- (do
      (b) <- (do
        a0 <- pure a
        a1 <- pure a
        (b) <- append_iio a0 a1
        pure (b)
       )
      pure (b)
     )
    arg2 <- pure b
    pure (arg2)
   )
  pure (arg2)
duplicate_oi arg2 = do
  (arg1) <- (do
    b <- pure arg2
    (a) <- (do
      (a) <- (do
        (a0,a1) <- append_ooi b
        a <- pure a0
        guard $ a1 == a
        pure (a)
       )
      pure (a)
     )
    arg1 <- pure a
    pure (arg1)
   )
  pure (arg1)
--duplicate_oi arg2 = do
--  (arg1) <- (do
--    b <- pure arg2
--    (a) <- (do
--      (a) <- (do
--        (a0,a1) <- append_ooi b
--        a <- pure a1
--        guard $ a0 == a
--        pure (a)
--       )
--      pure (a)
--     )
--    arg1 <- pure a
--    pure (arg1)
--   )
--  pure (arg1)
