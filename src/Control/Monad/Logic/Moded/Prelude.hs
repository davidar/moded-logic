module Control.Monad.Logic.Moded.Prelude where

succ_io a = pure (succ a)
succ_oi b = pure (pred b)
mod_iio a b = pure (mod a b)
plus_iio a b = pure (a + b)
plus_ioi a c = pure (c - a)
plus_oii b c = pure (c - b)
