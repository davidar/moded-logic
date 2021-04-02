module Append where
import Control.Applicative
import Control.Monad.Logic

{- appendLong/3
appendLong a b c :-
  a = [], b = c;
  a = ah : at, c = ch : ct, ah = ch, appendLong at b ct.
constraints:
ah[1]
ah[]
at[1]
at[]
ch[1]
ch[]
ct[1]
ct[]
~(a[1,0] & ah[1,0])
~(ah[1,0] & ah[1,2])
~(ah[1,2] & ch[1,2])
~(at[1,0] & at[1,3])
~(b[0,1] & c[0,1])
~(c[1,1] & ch[1,1])
~(ch[1,1] & ch[1,2])
~(ct[1,1] & ct[1,3])
(a[0] <-> a[0,0])
(a[1] <-> a[1,0])
(a[] <-> a[0])
(a[] <-> a[1])
(ah[1,0] <-> at[1,0])
(ah[1] <-> (ah[1,0] | ah[1,2]))
(at[1,3] <-> a[])
(at[1] <-> (at[1,0] | at[1,3]))
(b[0] <-> b[0,1])
(b[1,3] <-> b[])
(b[1] <-> b[1,3])
(b[] <-> b[0])
(b[] <-> b[1])
(c[0] <-> c[0,1])
(c[1] <-> c[1,1])
(c[] <-> c[0])
(c[] <-> c[1])
(ch[1,1] <-> ct[1,1])
(ch[1] <-> (ch[1,1] | ch[1,2]))
(ct[1,3] <-> c[])
(ct[1] <-> (ct[1,1] | ct[1,3]))
-}
appendLong_iii a b c = (do
  guard $ a == []
  guard $ b == c
  pure ()
 ) <|> (do
  (ah:at) <- pure a
  (ch:ct) <- pure c
  guard $ ah == ch
  () <- appendLong_iii at b ct
  pure ()
 )
appendLong_iio a b = (do
  guard $ a == []
  c <- pure b
  pure (c)
 ) <|> (do
  (ah:at) <- pure a
  ch <- pure ah
  (ct) <- appendLong_iio at b
  c <- pure (ch:ct)
  pure (c)
 )
appendLong_ioi a c = (do
  guard $ a == []
  b <- pure c
  pure (b)
 ) <|> (do
  (ah:at) <- pure a
  (ch:ct) <- pure c
  guard $ ah == ch
  (b) <- appendLong_ioi at ct
  pure (b)
 )
appendLong_oii b c = (do
  a <- pure []
  guard $ b == c
  pure (a)
 ) <|> (do
  (ch:ct) <- pure c
  ah <- pure ch
  (at) <- appendLong_oii b ct
  a <- pure (ah:at)
  pure (a)
 )
appendLong_ooi c = (do
  a <- pure []
  b <- pure c
  pure (a,b)
 ) <|> (do
  (ch:ct) <- pure c
  ah <- pure ch
  (at,b) <- appendLong_ooi ct
  a <- pure (ah:at)
  pure (a,b)
 )
{- append/3
append arg1 arg2 arg3 :-
  arg1 = [], arg2 = b, arg3 = b;
  h0 = h, h1 = h, arg1 = h0 : t, arg2 = b, arg3 = h1 : tb, append t b tb.
constraints:
b[]
h0[1]
h0[]
h1[1]
h1[]
h[1]
h[]
t[1]
t[]
tb[1]
tb[]
~(arg1[1,2] & h0[1,2])
~(arg2[0,1] & b[0,1])
~(arg2[1,3] & b[1,3])
~(arg3[0,2] & b[0,2])
~(arg3[1,4] & h1[1,4])
~(b[0,1] & b[0,2])
~(b[1,3] & b[1,5])
~(h0[1,0] & h0[1,2])
~(h0[1,0] & h[1,0])
~(h1[1,1] & h1[1,4])
~(h1[1,1] & h[1,1])
~(h[1,0] & h[1,1])
~(t[1,2] & t[1,5])
~(tb[1,4] & tb[1,5])
(arg1[0] <-> arg1[0,0])
(arg1[1] <-> arg1[1,2])
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg2[0] <-> arg2[0,1])
(arg2[1] <-> arg2[1,3])
(arg2[] <-> arg2[0])
(arg2[] <-> arg2[1])
(arg3[0] <-> arg3[0,2])
(arg3[1] <-> arg3[1,4])
(arg3[] <-> arg3[0])
(arg3[] <-> arg3[1])
(b[0] <-> (b[0,1] | b[0,2]))
(b[1,5] <-> arg2[])
(b[1] <-> (b[1,3] | b[1,5]))
(b[] <-> b[0])
(b[] <-> b[1])
(h0[1,2] <-> t[1,2])
(h0[1] <-> (h0[1,0] | h0[1,2]))
(h1[1,4] <-> tb[1,4])
(h1[1] <-> (h1[1,1] | h1[1,4]))
(h[1] <-> (h[1,0] | h[1,1]))
(t[1,5] <-> arg1[])
(t[1] <-> (t[1,2] | t[1,5]))
(tb[1,5] <-> arg3[])
(tb[1] <-> (tb[1,4] | tb[1,5]))
-}
append_iii arg1 arg2 arg3 = (do
  guard $ arg1 == []
  b <- pure arg2
  guard $ arg3 == b
  pure ()
 ) <|> (do
  (h0:t) <- pure arg1
  b <- pure arg2
  (h1:tb) <- pure arg3
  h <- pure h1
  guard $ h0 == h
  () <- append_iii t b tb
  pure ()
 )
--append_iii arg1 arg2 arg3 = (do
--  guard $ arg1 == []
--  b <- pure arg2
--  guard $ arg3 == b
--  pure ()
-- ) <|> (do
--  (h0:t) <- pure arg1
--  h <- pure h0
--  b <- pure arg2
--  (h1:tb) <- pure arg3
--  guard $ h1 == h
--  () <- append_iii t b tb
--  pure ()
-- )

--append_iii arg1 arg2 arg3 = (do
--  guard $ arg1 == []
--  b <- pure arg3
--  guard $ arg2 == b
--  pure ()
-- ) <|> (do
--  (h0:t) <- pure arg1
--  b <- pure arg2
--  (h1:tb) <- pure arg3
--  h <- pure h1
--  guard $ h0 == h
--  () <- append_iii t b tb
--  pure ()
-- )

--append_iii arg1 arg2 arg3 = (do
--  guard $ arg1 == []
--  b <- pure arg3
--  guard $ arg2 == b
--  pure ()
-- ) <|> (do
--  (h0:t) <- pure arg1
--  h <- pure h0
--  b <- pure arg2
--  (h1:tb) <- pure arg3
--  guard $ h1 == h
--  () <- append_iii t b tb
--  pure ()
-- )

append_iio arg1 arg2 = (do
  guard $ arg1 == []
  b <- pure arg2
  arg3 <- pure b
  pure (arg3)
 ) <|> (do
  (h0:t) <- pure arg1
  h <- pure h0
  h1 <- pure h
  b <- pure arg2
  (tb) <- append_iio t b
  arg3 <- pure (h1:tb)
  pure (arg3)
 )
append_ioi arg1 arg3 = (do
  guard $ arg1 == []
  b <- pure arg3
  arg2 <- pure b
  pure (arg2)
 ) <|> (do
  (h0:t) <- pure arg1
  (h1:tb) <- pure arg3
  h <- pure h1
  guard $ h0 == h
  (b) <- append_ioi t tb
  arg2 <- pure b
  pure (arg2)
 )
--append_ioi arg1 arg3 = (do
--  guard $ arg1 == []
--  b <- pure arg3
--  arg2 <- pure b
--  pure (arg2)
-- ) <|> (do
--  (h0:t) <- pure arg1
--  h <- pure h0
--  (h1:tb) <- pure arg3
--  guard $ h1 == h
--  (b) <- append_ioi t tb
--  arg2 <- pure b
--  pure (arg2)
-- )

append_oii arg2 arg3 = (do
  arg1 <- pure []
  b <- pure arg2
  guard $ arg3 == b
  pure (arg1)
 ) <|> (do
  b <- pure arg2
  (h1:tb) <- pure arg3
  h <- pure h1
  h0 <- pure h
  (t) <- append_oii b tb
  arg1 <- pure (h0:t)
  pure (arg1)
 )
--append_oii arg2 arg3 = (do
--  arg1 <- pure []
--  b <- pure arg3
--  guard $ arg2 == b
--  pure (arg1)
-- ) <|> (do
--  b <- pure arg2
--  (h1:tb) <- pure arg3
--  h <- pure h1
--  h0 <- pure h
--  (t) <- append_oii b tb
--  arg1 <- pure (h0:t)
--  pure (arg1)
-- )

append_ooi arg3 = (do
  arg1 <- pure []
  b <- pure arg3
  arg2 <- pure b
  pure (arg1,arg2)
 ) <|> (do
  (h1:tb) <- pure arg3
  h <- pure h1
  h0 <- pure h
  (t,b) <- append_ooi tb
  arg1 <- pure (h0:t)
  arg2 <- pure b
  pure (arg1,arg2)
 )
{- append/4
append a b c abc :-
  append a b ab, append ab c abc.
constraints:
ab[0]
ab[]
~(ab[0,0] & ab[0,1])
((a[0,0] & (b[0,0] & ~ab[0,0])) | ((a[0,0] & (~b[0,0] & ~ab[0,0])) | ((~a[0,0] & (b[0,0] & ~ab[0,0])) | ((~a[0,0] & (~b[0,0] & ab[0,0])) | (~a[0,0] & (~b[0,0] & ~ab[0,0]))))))
((ab[0,1] & (c[0,1] & ~abc[0,1])) | ((ab[0,1] & (~c[0,1] & ~abc[0,1])) | ((~ab[0,1] & (c[0,1] & ~abc[0,1])) | ((~ab[0,1] & (~c[0,1] & abc[0,1])) | (~ab[0,1] & (~c[0,1] & ~abc[0,1]))))))
(a[0] <-> a[0,0])
(a[] <-> a[0])
(ab[0] <-> (ab[0,0] | ab[0,1]))
(abc[0] <-> abc[0,1])
(abc[] <-> abc[0])
(b[0] <-> b[0,0])
(b[] <-> b[0])
(c[0] <-> c[0,1])
(c[] <-> c[0])
-}
append_iiii a b c abc = (do
  (ab) <- append_iio a b
  () <- append_iii ab c abc
  pure ()
 )
--append_iiii a b c abc = (do
--  (ab) <- append_oii c abc
--  () <- append_iii a b ab
--  pure ()
-- )

append_iiio a b c = (do
  (ab) <- append_iio a b
  (abc) <- append_iio ab c
  pure (abc)
 )
append_iioi a b abc = (do
  (ab) <- append_iio a b
  (c) <- append_ioi ab abc
  pure (c)
 )
--append_iioi a b abc = (do
--  (ab,c) <- append_ooi abc
--  () <- append_iii a b ab
--  pure (c)
-- )

append_ioii a c abc = (do
  (ab) <- append_oii c abc
  (b) <- append_ioi a ab
  pure (b)
 )
append_iooi a abc = (do
  (ab,c) <- append_ooi abc
  (b) <- append_ioi a ab
  pure (b,c)
 )
append_oiii b c abc = (do
  (ab) <- append_oii c abc
  (a) <- append_oii b ab
  pure (a)
 )
append_oioi b abc = (do
  (ab,c) <- append_ooi abc
  (a) <- append_oii b ab
  pure (a,c)
 )
append_ooii c abc = (do
  (ab) <- append_oii c abc
  (a,b) <- append_ooi ab
  pure (a,b)
 )
append_oooi abc = (do
  (ab,c) <- append_ooi abc
  (a,b) <- append_ooi ab
  pure (a,b,c)
 )
{- reverse/2
reverse arg1 arg2 :-
  arg1 = [], arg2 = [];
  h0 = h, h1 = h, data0 = [], data1 = h0 : data0, arg1 = h1 : t, arg2 = l, reverse t r, append r data1 l.
constraints:
data0[1]
data0[]
data1[1]
data1[]
h0[1]
h0[]
h1[1]
h1[]
h[1]
h[]
l[1]
l[]
r[1]
r[]
t[1]
t[]
~(arg1[1,4] & h1[1,4])
~(arg2[1,5] & l[1,5])
~(data0[1,2] & data0[1,3])
~(data1[1,3] & data1[1,7])
~(data1[1,3] & h0[1,3])
~(h0[1,0] & h0[1,3])
~(h0[1,0] & h[1,0])
~(h1[1,1] & h1[1,4])
~(h1[1,1] & h[1,1])
~(h[1,0] & h[1,1])
~(l[1,5] & l[1,7])
~(r[1,6] & r[1,7])
~(t[1,4] & t[1,6])
((r[1,7] & (data1[1,7] & ~l[1,7])) | ((r[1,7] & (~data1[1,7] & ~l[1,7])) | ((~r[1,7] & (data1[1,7] & ~l[1,7])) | ((~r[1,7] & (~data1[1,7] & l[1,7])) | (~r[1,7] & (~data1[1,7] & ~l[1,7]))))))
(arg1[0] <-> arg1[0,0])
(arg1[1] <-> arg1[1,4])
(arg1[] <-> arg1[0])
(arg1[] <-> arg1[1])
(arg2[0] <-> arg2[0,1])
(arg2[1] <-> arg2[1,5])
(arg2[] <-> arg2[0])
(arg2[] <-> arg2[1])
(data0[1] <-> (data0[1,2] | data0[1,3]))
(data1[1] <-> (data1[1,3] | data1[1,7]))
(h0[1,3] <-> data0[1,3])
(h0[1] <-> (h0[1,0] | h0[1,3]))
(h1[1,4] <-> t[1,4])
(h1[1] <-> (h1[1,1] | h1[1,4]))
(h[1] <-> (h[1,0] | h[1,1]))
(l[1] <-> (l[1,5] | l[1,7]))
(r[1,6] <-> arg2[])
(r[1] <-> (r[1,6] | r[1,7]))
(t[1,6] <-> arg1[])
(t[1] <-> (t[1,4] | t[1,6]))
-}
reverse_ii arg1 arg2 = (do
  guard $ arg1 == []
  guard $ arg2 == []
  pure ()
 ) <|> (do
  (h1:t) <- pure arg1
  h <- pure h1
  l <- pure arg2
  (r,data1) <- append_ooi l
  (h0:data0) <- pure data1
  guard $ h0 == h
  guard $ data0 == []
  () <- reverse_ii t r
  pure ()
 )
--reverse_ii arg1 arg2 = (do
--  guard $ arg1 == []
--  guard $ arg2 == []
--  pure ()
-- ) <|> (do
--  (h1:t) <- pure arg1
--  l <- pure arg2
--  (r,data1) <- append_ooi l
--  (h0:data0) <- pure data1
--  h <- pure h0
--  guard $ h1 == h
--  guard $ data0 == []
--  () <- reverse_ii t r
--  pure ()
-- )

--reverse_ii arg1 arg2 = (do
--  guard $ arg1 == []
--  guard $ arg2 == []
--  pure ()
-- ) <|> (do
--  data0 <- pure []
--  (h1:t) <- pure arg1
--  h <- pure h1
--  h0 <- pure h
--  data1 <- pure (h0:data0)
--  l <- pure arg2
--  (r) <- append_oii data1 l
--  () <- reverse_ii t r
--  pure ()
-- )

--reverse_ii arg1 arg2 = (do
--  guard $ arg1 == []
--  guard $ arg2 == []
--  pure ()
-- ) <|> (do
--  data0 <- pure []
--  (h1:t) <- pure arg1
--  h <- pure h1
--  h0 <- pure h
--  l <- pure arg2
--  (r,data1) <- append_ooi l
--  guard $ data1 == (h0:data0)
--  () <- reverse_ii t r
--  pure ()
-- )

reverse_io arg1 = (do
  guard $ arg1 == []
  arg2 <- pure []
  pure (arg2)
 ) <|> (do
  data0 <- pure []
  (h1:t) <- pure arg1
  h <- pure h1
  h0 <- pure h
  data1 <- pure (h0:data0)
  (r) <- reverse_io t
  (l) <- append_iio r data1
  arg2 <- pure l
  pure (arg2)
 )
reverse_oi arg2 = (do
  arg1 <- pure []
  guard $ arg2 == []
  pure (arg1)
 ) <|> (do
  l <- pure arg2
  (r,data1) <- append_ooi l
  (h0:data0) <- pure data1
  h <- pure h0
  h1 <- pure h
  guard $ data0 == []
  (t) <- reverse_oi r
  arg1 <- pure (h1:t)
  pure (arg1)
 )
{- palindrome/1
palindrome a :-
  a0 = a, a1 = a, reverse a0 a1.
constraints:
a0[0]
a0[]
a1[0]
a1[]
~(a0[0,0] & a0[0,2])
~(a0[0,0] & a[0,0])
~(a1[0,1] & a1[0,2])
~(a1[0,1] & a[0,1])
~(a[0,0] & a[0,1])
((a0[0,2] & ~a1[0,2]) | ((~a0[0,2] & a1[0,2]) | (~a0[0,2] & ~a1[0,2])))
(a0[0] <-> (a0[0,0] | a0[0,2]))
(a1[0] <-> (a1[0,1] | a1[0,2]))
(a[0] <-> (a[0,0] | a[0,1]))
(a[] <-> a[0])
-}
-- mode ordering failure, cyclic dependency: [2] reverse a0::in a1::out -> [1] a1::in = a::out -> [0] a0::out = a::in
-- mode ordering failure, cyclic dependency: [2] reverse a0::out a1::in -> [0] a0::in = a::out -> [1] a1::out = a::in

palindrome_i a = (do
  a0 <- pure a
  (a1) <- reverse_io a0
  guard $ a1 == a
  pure ()
 )
--palindrome_i a = (do
--  a0 <- pure a
--  a1 <- pure a
--  () <- reverse_ii a0 a1
--  pure ()
-- )

--palindrome_i a = (do
--  a1 <- pure a
--  (a0) <- reverse_oi a1
--  guard $ a0 == a
--  pure ()
-- )

{- duplicate/2
duplicate a b :-
  a0 = a, a1 = a, append a0 a1 b.
constraints:
a0[0]
a0[]
a1[0]
a1[]
~(a0[0,0] & a0[0,2])
~(a0[0,0] & a[0,0])
~(a1[0,1] & a1[0,2])
~(a1[0,1] & a[0,1])
~(a[0,0] & a[0,1])
((a0[0,2] & (a1[0,2] & ~b[0,2])) | ((a0[0,2] & (~a1[0,2] & ~b[0,2])) | ((~a0[0,2] & (a1[0,2] & ~b[0,2])) | ((~a0[0,2] & (~a1[0,2] & b[0,2])) | (~a0[0,2] & (~a1[0,2] & ~b[0,2]))))))
(a0[0] <-> (a0[0,0] | a0[0,2]))
(a1[0] <-> (a1[0,1] | a1[0,2]))
(a[0] <-> (a[0,0] | a[0,1]))
(a[] <-> a[0])
(b[0] <-> b[0,2])
(b[] <-> b[0])
-}
-- mode ordering failure, cyclic dependency: [2] append a0::in a1::out b::in -> [1] a1::in = a::out -> [0] a0::out = a::in
-- mode ordering failure, cyclic dependency: [2] append a0::out a1::in b::in -> [0] a0::in = a::out -> [1] a1::out = a::in

duplicate_ii a b = (do
  (a0,a1) <- append_ooi b
  guard $ a0 == a
  guard $ a1 == a
  pure ()
 )
--duplicate_ii a b = (do
--  a0 <- pure a
--  (a1) <- append_ioi a0 b
--  guard $ a1 == a
--  pure ()
-- )

--duplicate_ii a b = (do
--  a0 <- pure a
--  a1 <- pure a
--  () <- append_iii a0 a1 b
--  pure ()
-- )

--duplicate_ii a b = (do
--  a1 <- pure a
--  (a0) <- append_oii a1 b
--  guard $ a0 == a
--  pure ()
-- )

duplicate_io a = (do
  a0 <- pure a
  a1 <- pure a
  (b) <- append_iio a0 a1
  pure (b)
 )
duplicate_oi b = (do
  (a0,a1) <- append_ooi b
  a <- pure a0
  guard $ a1 == a
  pure (a)
 )
--duplicate_oi b = (do
--  (a0,a1) <- append_ooi b
--  a <- pure a1
--  guard $ a0 == a
--  pure (a)
-- )
