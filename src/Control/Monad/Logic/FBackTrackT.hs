module Control.Monad.Logic.FBackTrackT
  ( FBackTrackT
  , observeAll
  , observeAllT
  ) where

import Control.Applicative
import Control.Monad
import Control.Monad.Identity
import Control.Monad.Logic.Class
import Control.Monad.Trans

data FBackTrackTE m a
  = Nil
  | One a
  | Choice a (FBackTrackT m a)
  | Incomplete (FBackTrackT m a)

newtype FBackTrackT m a =
  FBackTrackT
    { unFBackTrackT :: m (FBackTrackTE m a)
    }

instance Monad m => Functor (FBackTrackT m) where
  fmap = liftM

instance Monad m => Applicative (FBackTrackT m) where
  pure = FBackTrackT . pure . One
  liftA2 = liftM2

instance Monad m => Monad (FBackTrackT m) where
  m >>= f =
    FBackTrackT $
    unFBackTrackT m >>= \s ->
      case s of
        Nil -> pure Nil
        One a -> unFBackTrackT $ f a
        Choice a r ->
          unFBackTrackT $ f a <|> (FBackTrackT . pure . Incomplete $ r >>= f)
        Incomplete i -> pure $ Incomplete (i >>= f)

instance Monad m => Alternative (FBackTrackT m) where
  empty = FBackTrackT $ pure Nil
  m1 <|> m2 =
    FBackTrackT $
    unFBackTrackT m1 >>= \s ->
      case s of
        Nil -> pure $ Incomplete m2
        One a -> pure $ Choice a m2
        Choice a r -> pure $ Choice a (m2 <|> r)
        Incomplete i ->
          unFBackTrackT m2 >>= \r ->
            case r of
              Nil -> pure s
              One b -> pure $ Choice b i
              Choice b r' -> pure $ Choice b (i <|> r')
              Incomplete j -> pure $ Incomplete (i <|> j)

instance Monad m => MonadPlus (FBackTrackT m)

instance Monad m => MonadLogic (FBackTrackT m) where
  msplit m =
    FBackTrackT $
    unFBackTrackT m >>= \s ->
      case s of
        Nil -> pure . One $ Nothing
        One x -> pure . One $ Just (x, empty)
        Choice x r -> pure . One $ Just (x, r)
        Incomplete i -> pure . Incomplete $ msplit i

instance MonadTrans FBackTrackT where
  lift m = FBackTrackT (m >>= pure . One)

instance MonadIO m => MonadIO (FBackTrackT m) where
  liftIO = lift . liftIO

observeAllT :: Monad m => FBackTrackT m a -> m [a]
observeAllT m =
  unFBackTrackT m >>= \s ->
    case s of
      Nil -> pure []
      One a -> pure [a]
      Choice a r -> do
        t <- observeAllT r
        pure (a : t)
      Incomplete r -> observeAllT r

observeAll :: FBackTrackT Identity a -> [a]
observeAll = runIdentity . observeAllT
