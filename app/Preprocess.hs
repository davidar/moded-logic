module Preprocess
  ( Val(..)
  , combineDefs
  , superhomogeneous
  , distinctVars
  ) where

import Control.Monad (forM)
import Control.Monad.Logic.Moded.AST
  ( Atom(..)
  , Func(..)
  , Goal(..)
  , Name
  , Rule(..)
  , Var(..)
  , subgoals
  )
import Control.Monad.State
  ( MonadState(..)
  , State
  , evalState
  , gets
  , modify
  , runState
  )
import Data.Foldable (toList)
import Data.List (group, groupBy, nub, sort)
import Data.Map (Map)
import qualified Data.Map as Map

data Val
  = Var Var
  | Cons Name [Val]
  | Lambda [Val] (Goal Val)
  | Curry Name [Val]
  deriving (Eq, Ord)

combineDefs :: [Rule Val Val] -> [Rule Var Val]
combineDefs rules = do
  defs <-
    groupBy
      (\(Rule n vs _) (Rule n' vs' _) -> n == n' && length vs == length vs')
      rules
  let params
        | [def] <- defs
        , args <- ruleArgs def
        , args == nub args
        , isVar `all` args = unVar <$> args
        | otherwise =
          [V ("arg" ++ show i) | i <- [1 .. length (ruleArgs (head defs))]]
      isVar Var {} = True
      isVar _ = False
      unVar (Var v) = v
      unVar _ = undefined
      body' =
        Disj $ do
          Rule _ vars' body <- defs
          let unifs =
                [ Atom $ Unif p (FVar v)
                | (p, v) <- map Var params `zip` vars'
                , v /= Var (V "_")
                , p /= v
                ]
          pure . Conj $ unifs ++ [body]
  pure $ Rule (ruleName $ head defs) params body'

superhomogeneous :: [(Name, Int)] -> Rule Var Val -> Rule Var Var
superhomogeneous arities r =
  r {ruleBody = evalState (tGoal $ ruleBody r) (0, [])}
  where
    tVal :: Val -> State (Int, [Goal Var]) Var
    tVal (Var (V name))
      | Just _ <- lookup name arities = tVal (Curry name [])
    tVal (Var v) = return v
    tVal (Cons name vs) = do
      vs' <- mapM tVal vs
      (count, body) <- get
      let u = V $ "data" ++ show count
      put (count + 1, body ++ [Atom . Unif u . Func name $ FVar <$> vs'])
      return u
    tVal (Lambda vs g) = do
      vs' <- mapM tVal vs
      g' <- tGoal g
      (count, body) <- get
      let name = V $ "pred" ++ show count
      put (count + 1, body ++ [Anon name vs' g'])
      return name
    tVal (Curry p vs) = do
      let arity =
            case lookup p arities of
              Just n -> n
              Nothing -> error $ "unknown predicate " ++ p
          k = arity - length vs
          extra = [Var . V $ "curry" ++ show i | i <- [1 .. k]]
          g = Atom $ Pred (Var $ V p) (vs ++ extra)
      tVal (Lambda extra g)
    tValFunc :: Val -> State (Int, [Goal Var]) (Func Var)
    tValFunc (Cons name vs) = do
      vs' <- mapM tValFunc vs
      return $ Func name vs'
    tValFunc v = FVar <$> tVal v
    tFunc :: Func Val -> State (Int, [Goal Var]) (Func Var)
    tFunc (Func name vs) = do
      vs' <- mapM tFunc vs
      return $ Func name vs'
    tFunc (FVar v) = tValFunc v
    tAtom :: Atom Val -> State (Int, [Goal Var]) (Atom Var)
    tAtom (Unif u v) = do
      u' <- tVal u
      v' <- tFunc v
      return $ Unif u' v'
    tAtom (Pred (Var name) vs) = do
      vs' <- mapM tVal vs
      return $ Pred name vs'
    tAtom Pred {} = error "tAtom Pred"
    tGoal :: Goal Val -> State (Int, [Goal Var]) (Goal Var)
    tGoal (Disj gs) = Disj <$> mapM tGoal gs
    tGoal (Conj gs) = Conj <$> mapM tGoal gs
    tGoal (Ifte c t e) = do
      c' <- tGoal c
      t' <- tGoal t
      e' <- tGoal e
      return $ Ifte c' t' e'
    tGoal (Anon name vs g) = do
      name' <- tVal name
      vs' <- mapM tVal vs
      g' <- tGoal g
      return $ Anon name' vs' g'
    tGoal (Atom a) = do
      (count, gs) <- get
      let (a', (count', body)) = runState (tAtom a) (count, [])
      put (count', gs)
      return $
        if null body
          then Atom a'
          else Conj $ Atom a' : body

distinctVars :: Rule Var Var -> Rule Var Var
distinctVars r = r {ruleBody = evalState (tGoal [] $ ruleBody r) Map.empty}
  where
    vars (Atom (Unif _ f)) = toList f
    vars (Atom _) = []
    vars g = subgoals g >>= vars
    tFunc :: [Var] -> Func Var -> State (Map Var Int) (Func Var, [Atom Var])
    tFunc fdups (Func name vs) = do
      (vs', bodies) <- unzip <$> tFunc fdups `mapM` vs
      return (Func name vs', concat bodies)
    tFunc fdups (FVar v) = do
      (v', body) <- tVar fdups v
      return (FVar v', body)
    tGoal :: [Var] -> Goal Var -> State (Map Var Int) (Goal Var)
    tGoal fdups (Disj gs) = Disj <$> tGoal fdups `mapM` gs
    tGoal fdups (Conj gs) = Conj <$> tGoal fdups' `mapM` gs
      where
        fdups' =
          fdups ++ [head l | l <- group . sort . vars $ Conj gs, length l > 1]
    tGoal fdups (Ifte c t e) = do
      c' <- tGoal fdups c
      t' <- tGoal fdups t
      e' <- tGoal fdups e
      return $ Ifte c' t' e'
    tGoal fdups (Anon name vs g) = do
      g' <- tGoal fdups g
      return $ Anon name vs g'
    tGoal _ a@(Atom (Unif _ (FVar _))) = return a
    tGoal fdups (Atom (Unif u v)) = do
      (v', body) <- tFunc fdups v
      return . Conj $ Atom <$> Unif u v' : body
    tGoal _ (Atom (Pred name vs)) = do
      let pdups = [head l | l <- group (sort vs), length l > 1]
      (vs', body) <- tVars pdups vs
      return . Conj $ Atom <$> Pred name vs' : concat body
    tVars :: [Var] -> [Var] -> State (Map Var Int) ([Var], [[Atom Var]])
    tVars dups vs = fmap unzip . forM vs $ tVar dups
    tVar :: [Var] -> Var -> State (Map Var Int) (Var, [Atom Var])
    tVar dups (V v) =
      if V v `elem` dups && v /= "_"
        then do
          count <- gets $ Map.lookup (V v)
          case count of
            Nothing -> do
              modify $ Map.insert (V v) 0
              return (V v, [])
            Just c -> do
              modify $ Map.insert (V v) (c + 1)
              let v' = V (v ++ show c)
              return (v', [Unif v' (FVar $ V v)])
        else return (V v, [])
