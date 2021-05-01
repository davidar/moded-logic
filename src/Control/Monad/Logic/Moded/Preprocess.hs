module Control.Monad.Logic.Moded.Preprocess
  ( Val(..)
  , combineDefs
  , superhomogeneous
  , distinctVars
  , simplify
  , simp
  ) where

import Control.Monad.Logic.Moded.AST
  ( Atom(..)
  , Goal(..)
  , Name
  , Rule(..)
  , Var(..)
  , subgoals
  )
import Control.Monad.State
import Data.List (group, groupBy, sort, transpose)

data Val
  = Var Var
  | Cons Name [Val]
  | Lambda [Val] (Goal Val)
  | Curry Name [Val]
  deriving (Eq, Ord)

instance Show Val where
  show (Var v) = show v
  show (Cons name vs) = unwords (name : map show vs)
  show (Lambda vs g) = unwords (map show vs) ++ " :- " ++ show g
  show (Curry p vs) = "(" ++ unwords (p : map show vs) ++ ")"

combineDefs :: [Rule Val Val] -> [Rule Var Val]
combineDefs rules = do
  defs <-
    groupBy
      (\(Rule n vs _) (Rule n' vs' _) -> n == n' && length vs == length vs')
      rules
  let params = do
        (i, a:as) <- zip [1 :: Integer ..] (transpose $ ruleArgs <$> defs)
        pure $
          case a of
            Var v
              | (a ==) `all` as -> v
            _ -> V $ "arg" ++ show i
      body' =
        Disj $ do
          Rule _ vars' body <- defs
          let unifs =
                [ Atom $ Unif p v
                | (p, v) <- map Var params `zip` vars'
                , show v /= "_"
                , show p /= show v
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
      put (count + 1, body ++ [Atom $ Func name vs' u])
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
          g = Atom $ Pred p (vs ++ extra)
      tVal (Lambda extra g)
    tAtom :: Atom Val -> State (Int, [Goal Var]) (Atom Var)
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
distinctVars r = r {ruleBody = evalState (tGoal $ ruleBody r) 0}
  where
    vars (Atom (Func _ vs _)) = vs
    vars (Atom _) = []
    vars g = subgoals g >>= vars
    fdups = [head l | l <- group . sort . vars $ ruleBody r, length l > 1]
    tGoal :: Goal Var -> State Int (Goal Var)
    tGoal (Disj gs) = Disj <$> mapM tGoal gs
    tGoal (Conj gs) = Conj <$> mapM tGoal gs
    tGoal (Ifte c t e) = do
      c' <- tGoal c
      t' <- tGoal t
      e' <- tGoal e
      return $ Ifte c' t' e'
    tGoal (Anon name vs g) = do
      g' <- tGoal g
      return $ Anon name vs g'
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
    unConj _ = undefined
    conjs = concat $ unConj <$> filter isConj gs'
    other = filter (not . isConj) gs'
simplify (Disj gs) = Disj $ simplify <$> gs
simplify (Ifte c t e) = Ifte (simplify c) (simplify t) (simplify e)
simplify (Anon name vs g) = Anon name vs (simplify g)
simplify (Atom a) = Atom a

simp :: Rule u Var -> Rule u Var
simp r = r {ruleBody = simplify (ruleBody r)}
