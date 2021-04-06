module Control.Monad.Logic.Moded.Preprocess
  ( Val(..)
  , combineDefs
  , superhomogeneous
  , distinctVars
  , simplify
  ) where

import Control.Monad (forM)
import Control.Monad.Logic.Moded.AST
  ( Atom(..)
  , Goal(..)
  , Name
  , Prog
  , Rule(..)
  , Var(..)
  , subgoals
  )
import Control.Monad.State
import Data.List (group, groupBy, sort)

data Val
  = Var Var
  | Cons Name [Val]

instance Show Val where
  show (Var v) = show v
  show (Cons name vs) = unwords (name : map show vs)

combineDefs :: Prog Val Val -> Prog Var Val
combineDefs rules = do
  let p (Rule n vs _) (Rule n' vs' _) = n == n' && length vs == length vs'
  defs <- groupBy p rules
  let Rule name vars _ = head defs
      params = [V $ "arg" ++ show i | i <- [1 .. length vars]]
      body' =
        Disj $ do
          Rule _ vars body <- defs
          pure . Conj $
            (fmap Atom . filter (\(Unif _ v) -> show v /= "_") $
             zipWith Unif (Var <$> params) vars) ++
            [body]
  pure $ Rule name params body'

superhomogeneous :: Rule Var Val -> Rule Var Var
superhomogeneous (Rule name args body) =
  Rule name args $ evalState (tGoal body) (0, [])
  where
    tVal :: Val -> State (Int, [Atom Var]) Var
    tVal (Var v) = return v
    tVal (Cons name vs) = do
      vs' <- mapM tVal vs
      (count, body) <- get
      let u = V $ "data" ++ show count
      put (count + 1, body ++ [Func name vs' u])
      return u
    tAtom :: Atom Val -> State (Int, [Atom Var]) (Atom Var)
    tAtom (Unif (Var u) (Var v)) = return $ Unif u v
    tAtom (Unif (Var u) (Cons name vs)) = do
      vs' <- mapM tVal vs
      return $ Func name vs' u
    tAtom (Unif u v) = error $ "tAtom " ++ show (Unif u v)
    tAtom (Func name vs u) = do
      u' <- tVal u
      vs' <- mapM tVal vs
      return $ Func name vs' u'
    tAtom (Pred name vs) = do
      vs' <- mapM tVal vs
      return $ Pred name vs'
    tGoal :: Goal Val -> State (Int, [Atom Var]) (Goal Var)
    tGoal (Disj gs) = Disj <$> mapM tGoal gs
    tGoal (Conj gs) = Conj <$> mapM tGoal gs
    tGoal (Ifte c t e) = do
      c' <- tGoal c
      t' <- tGoal t
      e' <- tGoal e
      return $ Ifte c' t' e'
    tGoal (Atom a) = do
      (count, _) <- get
      put (count, [])
      a' <- tAtom a
      (_, body) <- get
      return $
        if null body
          then Atom a'
          else Conj $ Atom <$> a' : body

distinctVars :: Rule Var Var -> Rule Var Var
distinctVars (Rule name args body) = Rule name args $ evalState (tGoal body) 0
  where
    vars (Atom (Func _ vs _)) = vs
    vars (Atom _) = []
    vars g = subgoals g >>= vars
    fdups = [head l | l <- group . sort $ vars body, length l > 1]
    tGoal :: Goal Var -> State Int (Goal Var)
    tGoal (Disj gs) = Disj <$> mapM tGoal gs
    tGoal (Conj gs) = Conj <$> mapM tGoal gs
    tGoal (Ifte c t e) = do
      c' <- tGoal c
      t' <- tGoal t
      e' <- tGoal e
      return $ Ifte c' t' e'
    tGoal (Atom (Func name vs u)) = do
      (vs', body) <- tVars fdups vs
      return . Conj $ Atom <$> Func name vs' u : concat body
    tGoal (Atom (Pred name vs)) = do
      let pdups = [head l | l <- group (sort vs), length l > 1]
      (vs', body) <- tVars pdups vs
      return . Conj $ Atom <$> Pred name vs' : concat body
    tGoal (Atom a) = return $ Atom a
    tVars dups vs =
      fmap unzip . forM vs $ \v ->
        if v `elem` dups && show v /= "_"
          then do
            count <- get
            put $ count + 1
            let v' = V (show v ++ show count)
            return (v', [Unif v' v])
          else return (v, [])

simplify :: Goal Var -> Goal Var
simplify (Conj gs) = Conj $ conjs ++ other
  where
    gs' = simplify <$> gs
    isConj (Conj _) = True
    isConj _ = False
    unConj (Conj c) = c
    conjs = concat $ unConj <$> filter isConj gs'
    other = filter (not . isConj) gs'
simplify (Disj gs) = Disj $ simplify <$> gs
simplify (Ifte c t e) = Ifte (simplify c) (simplify t) (simplify e)
simplify g = g
