{-# OPTIONS_GHC -F -pgmF=horn-preprocessor #-}
module DCG where

append [] b b
append (h:t) b (h:tb) :- append t b tb

{-# INLINE compose #-}
compose f g a z :- g a b, f b z

data Tree = S Tree Tree | NP String String | VP String Tree

det "the"
det "a"
noun "cat"
noun "bat"
verb "eats"

np (NP d n) = append d . append " " . append n :- det d, noun n
vp (VP v n) = append v . append " " . np n :- verb v
sentence (S n v) = np n . append " " . vp v
