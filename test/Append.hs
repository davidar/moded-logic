module Append where
import Control.Applicative
import Control.Monad.Logic

{- appendLong/3
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
constraints:
ah[1]
ah[]
at[1]
at[]
b[1]
b[]
ch[1]
ch[]
ct[1]
ct[]
xs[0]
xs[]
~(a1[1,0] & ah[1,0])
~(a2[0,1] & xs[0,1])
~(a2[1,1] & b[1,1])
~(a3[0,2] & xs[0,2])
~(a3[1,2] & ch[1,2])
~(ah[1,0] & ah[1,3])
~(ah[1,3] & ch[1,3])
~(at[1,0] & at[1,4])
~(b[1,1] & b[1,4])
~(ch[1,2] & ch[1,3])
~(ct[1,2] & ct[1,4])
~(xs[0,1] & xs[0,2])
(a1[0] <-> a1[0,0])
(a1[1] <-> a1[1,0])
(a1[] <-> a1[0])
(a1[] <-> a1[1])
(a2[0] <-> a2[0,1])
(a2[1] <-> a2[1,1])
(a2[] <-> a2[0])
(a2[] <-> a2[1])
(a3[0] <-> a3[0,2])
(a3[1] <-> a3[1,2])
(a3[] <-> a3[0])
(a3[] <-> a3[1])
(ah[1,0] <-> at[1,0])
(ah[1] <-> (ah[1,0] | ah[1,3]))
(at[1,4] <-> a1[])
(at[1] <-> (at[1,0] | at[1,4]))
(b[1,4] <-> a2[])
(b[1] <-> (b[1,1] | b[1,4]))
(ch[1,2] <-> ct[1,2])
(ch[1] <-> (ch[1,2] | ch[1,3]))
(ct[1,4] <-> a3[])
(ct[1] <-> (ct[1,2] | ct[1,4]))
(xs[0] <-> (xs[0,1] | xs[0,2]))
-}
append_iii a1 a2 a3 = (do
  guard $ a1 == []
  xs <- pure a2
  guard $ a3 == xs
  pure ()
 ) <|> (do
  (ah:at) <- pure a1
  b <- pure a2
  (ch:ct) <- pure a3
  guard $ ah == ch
  () <- append_iii at b ct
  pure ()
 )
--append_iii a1 a2 a3 = (do
--  guard $ a1 == []
--  xs <- pure a3
--  guard $ a2 == xs
--  pure ()
-- ) <|> (do
--  (ah:at) <- pure a1
--  b <- pure a2
--  (ch:ct) <- pure a3
--  guard $ ah == ch
--  () <- append_iii at b ct
--  pure ()
-- )

append_iio a1 a2 = (do
  guard $ a1 == []
  xs <- pure a2
  a3 <- pure xs
  pure (a3)
 ) <|> (do
  (ah:at) <- pure a1
  b <- pure a2
  ch <- pure ah
  (ct) <- append_iio at b
  a3 <- pure (ch:ct)
  pure (a3)
 )
append_ioi a1 a3 = (do
  guard $ a1 == []
  xs <- pure a3
  a2 <- pure xs
  pure (a2)
 ) <|> (do
  (ah:at) <- pure a1
  (ch:ct) <- pure a3
  guard $ ah == ch
  (b) <- append_ioi at ct
  a2 <- pure b
  pure (a2)
 )
append_oii a2 a3 = (do
  a1 <- pure []
  xs <- pure a2
  guard $ a3 == xs
  pure (a1)
 ) <|> (do
  b <- pure a2
  (ch:ct) <- pure a3
  ah <- pure ch
  (at) <- append_oii b ct
  a1 <- pure (ah:at)
  pure (a1)
 )
--append_oii a2 a3 = (do
--  a1 <- pure []
--  xs <- pure a3
--  guard $ a2 == xs
--  pure (a1)
-- ) <|> (do
--  b <- pure a2
--  (ch:ct) <- pure a3
--  ah <- pure ch
--  (at) <- append_oii b ct
--  a1 <- pure (ah:at)
--  pure (a1)
-- )

append_ooi a3 = (do
  a1 <- pure []
  xs <- pure a3
  a2 <- pure xs
  pure (a1,a2)
 ) <|> (do
  (ch:ct) <- pure a3
  ah <- pure ch
  (at,b) <- append_ooi ct
  a1 <- pure (ah:at)
  a2 <- pure b
  pure (a1,a2)
 )
{- append/4
constraints:
ab[0]
ab[]
~(ab[0,0] & ab[0,1])
((a[0,0] & (b[0,0] & ~ab[0,0])) | ((a[0,0] & (~b[0,0] & ~ab[0,0])) | ((a[0,0] & (~b[0,0] & ~ab[0,0])) | ((~a[0,0] & (b[0,0] & ~ab[0,0])) | ((~a[0,0] & (~b[0,0] & ab[0,0])) | ((~a[0,0] & (~b[0,0] & ~ab[0,0])) | (~a[0,0] & (~b[0,0] & ~ab[0,0]))))))))
((ab[0,1] & (c[0,1] & ~abc[0,1])) | ((ab[0,1] & (~c[0,1] & ~abc[0,1])) | ((ab[0,1] & (~c[0,1] & ~abc[0,1])) | ((~ab[0,1] & (c[0,1] & ~abc[0,1])) | ((~ab[0,1] & (~c[0,1] & abc[0,1])) | ((~ab[0,1] & (~c[0,1] & ~abc[0,1])) | (~ab[0,1] & (~c[0,1] & ~abc[0,1]))))))))
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
constraints:
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
x0[1]
x0[]
x1[1]
x1[]
~(a1[1,4] & h1[1,4])
~(a2[1,5] & l[1,5])
~(h0[1,0] & h0[1,3])
~(h0[1,0] & h[1,0])
~(h1[1,1] & h1[1,4])
~(h1[1,1] & h[1,1])
~(h[1,0] & h[1,1])
~(l[1,5] & l[1,7])
~(r[1,6] & r[1,7])
~(t[1,4] & t[1,6])
~(x0[1,2] & x0[1,3])
~(x1[1,3] & h0[1,3])
~(x1[1,3] & x1[1,7])
((r[1,7] & (x1[1,7] & ~l[1,7])) | ((r[1,7] & (~x1[1,7] & ~l[1,7])) | ((r[1,7] & (~x1[1,7] & ~l[1,7])) | ((~r[1,7] & (x1[1,7] & ~l[1,7])) | ((~r[1,7] & (~x1[1,7] & l[1,7])) | ((~r[1,7] & (~x1[1,7] & ~l[1,7])) | (~r[1,7] & (~x1[1,7] & ~l[1,7]))))))))
(a1[0] <-> a1[0,0])
(a1[1] <-> a1[1,4])
(a1[] <-> a1[0])
(a1[] <-> a1[1])
(a2[0] <-> a2[0,1])
(a2[1] <-> a2[1,5])
(a2[] <-> a2[0])
(a2[] <-> a2[1])
(h0[1,3] <-> x0[1,3])
(h0[1] <-> (h0[1,0] | h0[1,3]))
(h1[1,4] <-> t[1,4])
(h1[1] <-> (h1[1,1] | h1[1,4]))
(h[1] <-> (h[1,0] | h[1,1]))
(l[1] <-> (l[1,5] | l[1,7]))
(r[1,6] <-> a2[])
(r[1] <-> (r[1,6] | r[1,7]))
(t[1,6] <-> a1[])
(t[1] <-> (t[1,4] | t[1,6]))
(x0[1] <-> (x0[1,2] | x0[1,3]))
(x1[1] <-> (x1[1,3] | x1[1,7]))
-}
reverse_ii a1 a2 = (do
  guard $ a1 == []
  guard $ a2 == []
  pure ()
 ) <|> (do
  (h1:t) <- pure a1
  h <- pure h1
  l <- pure a2
  (r,x1) <- append_ooi l
  (h0:x0) <- pure x1
  guard $ h0 == h
  guard $ x0 == []
  () <- reverse_ii t r
  pure ()
 )
--reverse_ii a1 a2 = (do
--  guard $ a1 == []
--  guard $ a2 == []
--  pure ()
-- ) <|> (do
--  (h1:t) <- pure a1
--  l <- pure a2
--  (r,x1) <- append_ooi l
--  (h0:x0) <- pure x1
--  h <- pure h0
--  guard $ h1 == h
--  guard $ x0 == []
--  () <- reverse_ii t r
--  pure ()
-- )

--reverse_ii a1 a2 = (do
--  guard $ a1 == []
--  guard $ a2 == []
--  pure ()
-- ) <|> (do
--  x0 <- pure []
--  (h1:t) <- pure a1
--  h <- pure h1
--  h0 <- pure h
--  l <- pure a2
--  (r,x1) <- append_ooi l
--  guard $ x1 == (h0:x0)
--  () <- reverse_ii t r
--  pure ()
-- )

--reverse_ii a1 a2 = (do
--  guard $ a1 == []
--  guard $ a2 == []
--  pure ()
-- ) <|> (do
--  x0 <- pure []
--  (h1:t) <- pure a1
--  h <- pure h1
--  h0 <- pure h
--  x1 <- pure (h0:x0)
--  l <- pure a2
--  (r) <- append_oii x1 l
--  () <- reverse_ii t r
--  pure ()
-- )

reverse_io a1 = (do
  guard $ a1 == []
  a2 <- pure []
  pure (a2)
 ) <|> (do
  x0 <- pure []
  (h1:t) <- pure a1
  h <- pure h1
  h0 <- pure h
  x1 <- pure (h0:x0)
  (r) <- reverse_io t
  (l) <- append_iio r x1
  a2 <- pure l
  pure (a2)
 )
reverse_oi a2 = (do
  a1 <- pure []
  guard $ a2 == []
  pure (a1)
 ) <|> (do
  l <- pure a2
  (r,x1) <- append_ooi l
  (h0:x0) <- pure x1
  h <- pure h0
  h1 <- pure h
  guard $ x0 == []
  (t) <- reverse_oi r
  a1 <- pure (h1:t)
  pure (a1)
 )