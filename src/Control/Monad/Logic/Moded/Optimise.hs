module Control.Monad.Logic.Moded.Optimise
  ( Macro
  , simp
  , inlinePreds
  , prunePreds
  ) where

import Control.Monad.Logic.Moded.AST
  ( Atom(..)
  , Goal(..)
  , Name
  , Rule(..)
  , Var(..)
  )
import Control.Monad.Logic.Moded.Mode (ModeString)
import Control.Monad.Logic.Moded.Path (Path, nonlocals)
import Control.Monad.State (MonadState(..), State)
import Data.Foldable (toList)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

type Macro = ([Var], Goal Var, Set Var)

simplify :: Goal Var -> Goal Var
simplify (Conj gs) = Conj $ conjs ++ other
  where
    gs' = simplify <$> gs
    isConj (Conj _) = True
    isConj (Disj [Conj _]) = True
    isConj _ = False
    unConj (Conj c) = c
    unConj (Disj [Conj c]) = c
    unConj _ = undefined
    conjs = concat $ unConj <$> filter isConj gs'
    other = filter (not . isConj) gs'
simplify (Disj gs) = Disj $ simplify <$> gs
simplify (Ifte c t e) = Ifte (simplify c) (simplify t) (simplify e)
simplify (Anon name vs g) = Anon name vs (simplify g)
simplify (Atom a) = Atom a

simp :: Rule u Var -> Rule u Var
simp r = r {ruleBody = simplify (ruleBody r)}

inlinePreds ::
     Map Name [ModeString]
  -> [(Name, Macro)]
  -> Rule Var Var
  -> State Int (Rule Var Var)
inlinePreds m env_ r = do
  body' <- tGoal env_ [] (ruleBody r)
  pure $ r {ruleBody = body'}
  where
    tGoal :: [(Name, Macro)] -> Path -> Goal Var -> State Int (Goal Var)
    tGoal env p (Disj gs) =
      Disj <$> sequence [tGoal env (p ++ [d]) g | (d, g) <- zip [0 ..] gs]
    tGoal env p (Conj gs) =
      fmap Conj . sequence $ do
        let env' =
              env ++ do
                (c, Anon (V name) vs body) <- zip [0 ..] gs
                let preds = Set.map V $ ruleName r `Set.insert` Map.keysSet m
                    macros = Set.fromList $ V . fst <$> env
                    nls = nonlocals (p ++ [c]) r
                pure (name, (vs, body, Set.unions [preds, macros, nls]))
        g <- gs
        pure $
          case g of
            Atom (Pred (V name) vs)
              | Just (us, body, nls) <- lookup name env' -> do
                count <- get
                put (count + 1)
                let binds = zip us vs
                    f (V u)
                      | Just v <- lookup (V u) binds = v
                      | V u `elem` nls = V u
                      | otherwise = V $ u ++ "_" ++ show count
                return (f <$> body)
            _ -> return g
    tGoal env p (Ifte c t e) = do
      c' <- tGoal env (p ++ [0]) c
      t' <- tGoal env (p ++ [1]) t
      e' <- tGoal env (p ++ [2]) e
      return $ Ifte c' t' e'
    tGoal env p (Anon name vs g) = do
      g' <- tGoal env (p ++ [0]) g
      return $ Anon name vs g'
    tGoal _ _ (Atom a) = return $ Atom a

prunePreds :: Rule Var Var -> Rule Var Var
prunePreds r = r {ruleBody = tGoal (ruleBody r)}
  where
    tGoal :: Goal Var -> Goal Var
    tGoal (Disj gs) = Disj $ tGoal <$> gs
    tGoal (Conj gs) = Conj $ tGoal <$> gs
    tGoal (Ifte c t e) = Ifte (tGoal c) (tGoal t) (tGoal e)
    tGoal (Anon name vs g)
      | (length . filter (== name) . toList $ ruleBody r) > 1 =
        Anon name vs (tGoal g)
      | otherwise = Conj []
    tGoal (Atom a) = Atom a
