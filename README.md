# moded-logic

Haskell implementation of [Constraint-Based Mode Analysis of Mercury](https://lara.epfl.ch/w/_media/cc09:modeanalysisoverton.pdf).

## Input

```hs
append [] b b.
append (h:t) b (h:tb) :- append t b tb.
```

## Output

```hs
append_iii a1 a2 a3 = (do
  guard $ a1 == []
  b <- pure a2
  guard $ a3 == b
  pure ()
 ) <|> (do
  (h0:t) <- pure a1
  b <- pure a2
  (h1:tb) <- pure a3
  h <- pure h1
  guard $ h0 == h
  () <- append_iii t b tb
  pure ()
 )

append_iio a1 a2 = (do
  guard $ a1 == []
  b <- pure a2
  a3 <- pure b
  pure (a3)
 ) <|> (do
  (h0:t) <- pure a1
  h <- pure h0
  h1 <- pure h
  b <- pure a2
  (tb) <- append_iio t b
  a3 <- pure (h1:tb)
  pure (a3)
 )

append_ooi a3 = (do
  a1 <- pure []
  b <- pure a3
  a2 <- pure b
  pure (a1,a2)
 ) <|> (do
  (h1:tb) <- pure a3
  h <- pure h1
  h0 <- pure h
  (t,b) <- append_ooi tb
  a1 <- pure (h0:t)
  a2 <- pure b
  pure (a1,a2)
 )
```
