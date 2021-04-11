{-# LANGUAGE NoMonomorphismRestriction #-}
{-# OPTIONS_GHC -Wwarn #-}
module Control.Monad.Logic.Moded.Prelude where

import Control.Applicative
import Control.Monad
import Control.Monad.IO.Class

choose = foldr ((<|>) . pure) empty

succ_io a = pure (succ a)
succ_oi b = pure (pred b)
succ_ii a b = guard (succ a == b)
div_iio a b = pure (div a b)
div_iii a b c = guard (div a b == c)
mod_iio a b = pure (mod a b)
divMod_iioo a b = pure (divMod a b)
divMod_iioi a b m = guard (mod a b == m) >> pure (div a b)
divMod_iiii a b d m = guard (divMod a b == (d,m))
plus_iio a b = pure (a + b)
plus_ioi a c = pure (c - a)
plus_oii b c = pure (c - b)
times_iio a b = pure (a * b)
times_ioi a c = pure (c / a)
times_oii b c = pure (c / b)
timesInt_iio a b = pure (a * b)
timesInt_ioi a c = guard (mod c a == 0) >> pure (div c a)
timesInt_oii b c = guard (mod c b == 0) >> pure (div c b)
sum_io xs = pure (sum xs)
print_i x = liftIO (print x)
