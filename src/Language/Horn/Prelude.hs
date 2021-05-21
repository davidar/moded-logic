{-# LANGUAGE NoMonomorphismRestriction, TypeOperators, DataKinds,
  FlexibleContexts, TypeApplications, BlockArguments #-}
{-# OPTIONS_GHC -Wwarn -Wno-unticked-promoted-constructors #-}

module Language.Horn.Prelude
  ( choose
  , modesPrelude
  , succ
  , div
  , mod
  , divMod
  , plus
  , times
  , timesInt
  , sum
  , maximum
  , print
  , putStrLn
  , show
  , observeAll
  , nub
  , module Control.Applicative
  , module Control.Monad
  , module Control.Monad.Fail
  , module Control.Monad.Logic.Class
  , module Control.Monad.Logic.Moded.Mode
  , module Control.Monad.Logic.Moded.Procedure
  , module Data.MemoTrie
  , module Data.Tuple.OneTuple
  , module Data.Vinyl
  , module Prelude
  ) where

import Control.Applicative (Alternative(..), Applicative(..))
import Control.Monad (guard)
import Control.Monad.Fail (MonadFail)
import Control.Monad.IO.Class (MonadIO(..))
import qualified Control.Monad.Logic as Logic
import Control.Monad.Logic.Class (MonadLogic)
import Control.Monad.Logic.Moded.Mode (Mode(..))
import Control.Monad.Logic.Moded.Procedure
  ( ConstructProcedure(..)
  , PredType
  , Procedure
  )
import Data.List (nub)
import qualified Data.Map as Map
import Data.MemoTrie (memo, memo2, memo3)
import Data.Tuple.OneTuple (OneTuple(..), only)
import Data.Vinyl (type (∈), Rec(..), rget)
import qualified Prelude
import Prelude
  ( Eq(..)
  , Fractional(..)
  , Int
  , Integer
  , Integral
  , Maybe(..)
  , Num(..)
  , Ord(..)
  , Read
  , Show
  , String
  , ($)
  , (.)
  , (<$>)
  )

choose :: (Prelude.Foldable t, Alternative f) => t a -> f a
choose = Prelude.foldr ((<|>) . pure) empty

modesPrelude :: Map.Map Prelude.String [[Mode]]
modesPrelude =
  Map.fromList
    [ ("empty", [[]])
    , ("succ", [[In, In], [In, Out], [Out, In]])
    , ("div", [[In, In, In], [In, In, Out]])
    , ("mod", [[In, In, In], [In, In, Out]])
    , ( "divMod"
      , [ [In, In, In, In]
        , [In, In, In, Out]
        , [In, In, Out, In]
        , [In, In, Out, Out]
        ])
    , ("plus", [[In, In, In], [In, In, Out], [In, Out, In], [Out, In, In]])
    , ("times", [[In, In, In], [In, In, Out], [In, Out, In], [Out, In, In]])
    , ("timesInt", [[In, In, In], [In, In, Out], [In, Out, In], [Out, In, In]])
    , ("sum", [[In, In], [In, Out]])
    , ("maximum", [[In, In], [In, Out]])
    , ("print", [[In]])
    , ("putStrLn", [[In]])
    , ("show", [[In, In], [In, Out], [Out, In]])
    , ("observeAll", [[PredMode [Out], Out]])
    , ("(<)", [[In, In]])
    , ("(<=)", [[In, In]])
    , ("(>)", [[In, In]])
    , ("(>=)", [[In, In]])
    , ("(/=)", [[In, In]])
    ]

succ ::
     ( mode ∈ '[ '[ In, In], '[ In, Out], '[ Out, In]]
     , Alternative m
     , Eq a
     , Prelude.Enum a
     )
  => Procedure m () '[ a, a] mode
succ =
  rget $
  (procedure @'[ In, In] \a b -> guard (Prelude.succ a == b)) :&
  (procedure @'[ In, Out] \a -> pure (OneTuple $ Prelude.succ a)) :&
  (procedure @'[ Out, In] \b -> pure (OneTuple $ Prelude.pred b)) :&
  RNil

div ::
     (mode ∈ '[ '[ In, In, In], '[ In, In, Out]], Alternative m, Integral a)
  => Procedure m () '[ a, a, a] mode
div =
  rget $
  (procedure @'[ In, In, In] \a b c -> guard (Prelude.div a b == c)) :&
  (procedure @'[ In, In, Out] \a b -> pure (OneTuple $ Prelude.div a b)) :&
  RNil

mod ::
     (mode ∈ '[ '[ In, In, In], '[ In, In, Out]], Alternative m, Integral a)
  => Procedure m () '[ a, a, a] mode
mod =
  rget $
  (procedure @'[ In, In, In] \a b c -> guard (Prelude.mod a b == c)) :&
  (procedure @'[ In, In, Out] \a b -> pure (OneTuple $ Prelude.mod a b)) :&
  RNil

divMod ::
     ( mode ∈ '[ '[ In, In, In, In], '[ In, In, In, Out], '[ In, In, Out, In], '[ In, In, Out, Out]]
     , Alternative m
     , Integral a
     )
  => Procedure m () '[ a, a, a, a] mode
divMod =
  rget $
  (procedure @'[ In, In, In, In] $ \a b d m ->
     guard (Prelude.divMod a b == (d, m))) :&
  (procedure @'[ In, In, In, Out] $ \a b d ->
     if Prelude.div a b == d
       then pure (OneTuple $ Prelude.mod a b)
       else empty) :&
  (procedure @'[ In, In, Out, In] $ \a b m ->
     if Prelude.mod a b == m
       then pure (OneTuple $ Prelude.div a b)
       else empty) :&
  (procedure @'[ In, In, Out, Out] \a b -> pure (Prelude.divMod a b)) :&
  RNil

plus ::
     ( mode ∈ '[ '[ In, In, In], '[ In, In, Out], '[ In, Out, In], '[ Out, In, In]]
     , Alternative m
     , Num a
     , Eq a
     )
  => Procedure m () '[ a, a, a] mode
plus =
  rget $
  (procedure @'[ In, In, In] \a b c -> guard (a + b == c)) :&
  (procedure @'[ In, In, Out] \a b -> pure (OneTuple $ a + b)) :&
  (procedure @'[ In, Out, In] \a c -> pure (OneTuple $ c - a)) :&
  (procedure @'[ Out, In, In] \b c -> pure (OneTuple $ c - b)) :&
  RNil

times ::
     ( mode ∈ '[ '[ In, In, In], '[ In, In, Out], '[ In, Out, In], '[ Out, In, In]]
     , Alternative m
     , Fractional a
     , Eq a
     )
  => Procedure m () '[ a, a, a] mode
times =
  rget $
  (procedure @'[ In, In, In] \a b c -> guard (a * b == c)) :&
  (procedure @'[ In, In, Out] \a b -> pure (OneTuple $ a * b)) :&
  (procedure @'[ In, Out, In] \a c -> pure (OneTuple $ c / a)) :&
  (procedure @'[ Out, In, In] \b c -> pure (OneTuple $ c / b)) :&
  RNil

timesInt ::
     ( mode ∈ '[ '[ In, In, In], '[ In, In, Out], '[ In, Out, In], '[ Out, In, In]]
     , Alternative m
     , Integral a
     )
  => Procedure m () '[ a, a, a] mode
timesInt =
  rget $
  (procedure @'[ In, In, In] \a b c -> guard (a * b == c)) :&
  (procedure @'[ In, In, Out] \a b -> pure (OneTuple $ a * b)) :&
  (procedure @'[ In, Out, In] $ \a c ->
     runProcedure @'[ In, In, Out, In] divMod c a 0) :&
  (procedure @'[ Out, In, In] $ \b c ->
     runProcedure @'[ In, In, Out, In] divMod c b 0) :&
  RNil

sum ::
     ( mode ∈ '[ '[ In, In], '[ In, Out]]
     , Alternative m
     , Prelude.Foldable t
     , Num a
     , Eq a
     )
  => Procedure m () '[ t a, a] mode
sum =
  rget $
  (procedure @'[ In, In] \xs s -> guard (Prelude.sum xs == s)) :&
  (procedure @'[ In, Out] \xs -> pure (OneTuple $ Prelude.sum xs)) :&
  RNil

maximum ::
     ( mode ∈ '[ '[ In, In], '[ In, Out]]
     , Alternative m
     , Prelude.Foldable t
     , Ord a
     )
  => Procedure m () '[ t a, a] mode
maximum =
  rget $
  (procedure @'[ In, In] \xs s -> guard (Prelude.maximum xs == s)) :&
  (procedure @'[ In, Out] \xs -> pure (OneTuple $ Prelude.maximum xs)) :&
  RNil

print :: (MonadIO m, Prelude.Show a) => Procedure m () '[ a] '[ In]
print = procedure $ liftIO . Prelude.print

putStrLn :: (MonadIO m) => Procedure m () '[ String] '[ In]
putStrLn = procedure $ liftIO . Prelude.putStrLn

show ::
     ( mode ∈ '[ '[ In, In], '[ In, Out], '[ Out, In]]
     , Alternative m
     , Read a
     , Show a
     )
  => Procedure m () '[ a, Prelude.String] mode
show =
  rget $
  (procedure @'[ In, In] \a s -> guard (Prelude.show a == s)) :&
  (procedure @'[ In, Out] \a -> pure (OneTuple $ Prelude.show a)) :&
  (procedure @'[ Out, In] \s -> pure (OneTuple $ Prelude.read s)) :&
  RNil

observeAll ::
     Applicative m
  => Procedure m () '[ PredType Logic.Logic () '[ a], [a]] '[ 'PredMode '[ 'Out], 'Out]
observeAll =
  procedure \p -> pure (OneTuple $ Logic.observeAll (only <$> runProcedure p))
