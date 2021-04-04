{-# LANGUAGE DeriveFunctor, DeriveFoldable, FlexibleContexts, FlexibleInstances, OverloadedStrings, QuasiQuotes #-}
module Control.Monad.Logic.Moded where

import Algebra.Graph.AdjacencyMap
import Algebra.Graph.AdjacencyMap.Algorithm
import Control.Monad
import Control.Monad.State
import Data.Foldable
import Data.List
import qualified Data.Map as Map
import Data.Monoid
import Data.Ord
import qualified Data.Set as Set
import Data.Set (Set)
import NeatInterpolation
import qualified Control.Monad.Logic.Moded.Solver as Sat
import qualified Data.Text as T
import Data.Text (Text)
import System.IO.Unsafe

type Name = String

newtype Var = V String
            deriving (Eq, Ord)

data Atom v = Unif v v
            | Func Name [v] v
            | Pred Name [v]
            deriving (Eq, Ord, Functor, Foldable)

data Goal v = Atom (Atom v)
            | Conj [Goal v]
            | Disj [Goal v]
            | Ifte (Goal v) (Goal v) (Goal v)
            deriving (Eq, Ord, Functor, Foldable)

data Rule u v = Rule Name [u] (Goal v)

type Path = [Int]

type Constraints = Set Sat.Expr

data ModedVar = In String | Out String
              deriving (Eq, Ord)

type Prog u v = [Rule u v]

type CState = [((Name, Int), ((Rule Var Var, Constraints), [(Constraints, Either String (Rule ModedVar ModedVar))]))]

data Val = Var Var
         | Cons Name [Val]

-- TODO prioritise Ord based on cardinality estimates
data DepNode = DepNode Int (Goal ModedVar)
             deriving (Eq, Ord)

instance Show Var where
    show (V v) = v

instance Show ModedVar where
    show (In v) = v ++"::in"
    show (Out v) = v ++"::out"

instance (Show v) => Show (Atom v) where
    show (Unif u v) = show u ++" = "++ show v
    show (Func ":" [h,t] u) = show u ++" = "++ show h ++" : "++ show t
    show (Func name vs u) = show u ++" = "++ unwords (name : map show vs)
    show (Pred name []) = name
    show (Pred name vs) = unwords (name : map show vs)

instance (Show v) => Show (Goal v) where
    show (Atom a) = show a
    show (Conj gs) = "("++ intercalate ", " (map show gs) ++")"
    show (Disj gs) = "("++ intercalate "; " (map show gs) ++")"
    show (Ifte c t e) = "if " <> show c <> " then " <> show t <> " else " <> show e

instance (Show u, Show v) => Show (Rule u v) where
    show (Rule name vars g) =
        unwords (name : map show vars) ++" :- "++ show g ++"."

instance Show Val where
    show (Var v) = show v
    show (Cons name vs) = unwords (name : map show vs)

instance Show DepNode where
    show (DepNode i g) = "["++ show i ++"] "++ show g

dropIndex :: Int -> [a] -> [a]
dropIndex i xs = h ++ drop 1 t
  where (h, t) = splitAt i xs

body :: Rule u v -> Goal v
body (Rule _ _ goal) = goal

stripMode :: ModedVar -> Var
stripMode (In v) = V v
stripMode (Out v) = V v

unDepNode :: DepNode -> Goal ModedVar
unDepNode (DepNode _ g) = g

-- | Variables inside a goal
inside :: (Ord v) => Path -> Rule u v -> Set v
inside p = Set.fromList . toList . extract p . body

-- | Variables accessible from parent/sibling contexts
outside :: Path -> Goal Var -> Set Var
outside [] g = Set.empty
outside (c:ps) (Conj gs) = Set.fromList (dropIndex c gs >>= toList) `Set.union` outside ps (gs !! c)
outside (d:ps) (Disj gs) = outside ps (gs !! d)
outside (0:ps) (Ifte c t e) = Set.fromList (toList t) `Set.union` outside ps c
outside (1:ps) (Ifte c t e) = Set.fromList (toList c) `Set.union` outside ps t
outside (2:ps) (Ifte c t e) = outside ps e

nonlocals' :: Path -> Rule ModedVar ModedVar -> Set Var
nonlocals' p (Rule name vars body) = nonlocals p (Rule name (stripMode <$> vars) (stripMode <$> body))

nonlocals :: Path -> Rule Var Var -> Set Var
nonlocals p r@(Rule _ vars body) = inside p r `Set.intersection` out
  where out = Set.fromList vars `Set.union` outside p body

locals :: Path -> Rule Var Var -> Set Var
locals p r@(Rule _ vars body) = inside p r Set.\\ out
  where out = Set.fromList vars `Set.union` outside p body

subgoals :: Goal v -> [Goal v]
subgoals (Conj gs) = gs
subgoals (Disj gs) = gs
subgoals (Ifte c t e) = [c,t,e]

extract :: Path -> Goal v -> Goal v
extract [] g = g
extract (p:ps) g = extract ps $ subgoals g !! p

term :: Path -> Var -> Sat.Expr
term p (V v) = Sat.Var . Sat.Ident $ v ++ show p

-- | Complete set of constraints (sec 5.2.2)
cComp :: CState -> Path -> Rule Var Var -> Constraints
cComp procs p r = cGen p r `Set.union` cGoal procs p r

-- | General constraints (sec 5.2.2)
cGen :: Path -> Rule Var Var -> Constraints
cGen p r = cLocal p r `Set.union` cExt p r

-- | Local constraints (sec 5.2.2)
cLocal :: Path -> Rule Var Var -> Constraints
cLocal p r = term p `Set.map` locals p r

-- | External constraints (sec 5.2.2)
cExt :: Path -> Rule Var Var -> Constraints
cExt [] _ = Set.empty
cExt p r = (Sat.Neg . term p) `Set.map` (inside (init p) r Set.\\ inside p r)

-- | Disjunction constraints (sec 5.2.3)
cDisj :: Path -> Rule Var Var -> Constraints
cDisj p r = Set.unions $ do
    let Disj disj = extract p $ body r
    (d, g) <- zip [0..] disj
    pure $ Set.map (\v -> term p v `Sat.Iff` term (p ++ [d]) v) $ nonlocals (p ++ [d]) r

-- | Conjunction constraints (sec 5.2.3)
cConj :: Path -> Rule Var Var -> Constraints
cConj p r = Set.fromList $ do
    let Conj conj = extract p $ body r
    v <- Set.elems $ inside p r
    let terms = [term (p ++ [c]) v | (c,g) <- zip [0..] conj, v `elem` g]
        c = term p v `Sat.Iff` foldr1 Sat.Disj terms
        cs = [Sat.Neg (Sat.Conj s t) | s <- terms, t <- terms, s < t]
    (c:cs)

-- | If-then-else constraints (sec 5.2.3)
cIte :: Path -> Rule Var Var -> Constraints
cIte p r = Set.fromList . concat $
    [[term p v `Sat.Iff` (term pc v `Sat.Disj` term pt v `Sat.Disj` term pe v) | v <- vs]
    ,[Sat.Neg $ term pc v `Sat.Conj` term pt v | v <- vs]
    ,[Sat.Neg $ term pc v | v <- nls]
    ,[term pt v `Sat.Iff` term pe v | v <- nls]
    ]
  where vs = Set.elems $ inside p r
        nls = Set.elems $ nonlocals p r
        pc = p ++ [0]
        pt = p ++ [1]
        pe = p ++ [2]

nand :: Path -> Var -> Var -> Sat.Expr
nand p u v = Sat.Neg (Sat.Conj (term p u) (term p v))

-- | Goal-specific constraints
cGoal :: CState -> Path -> Rule Var Var -> Constraints
cGoal procs p r = case extract p (body r) of
    Disj disj -> Set.unions $ cDisj p r :
        [cComp procs (p ++ [d]) r | d <- take (length disj) [0..]]
    Conj conj -> Set.unions $ cConj p r :
        [cComp procs (p ++ [c]) r | c <- take (length conj) [0..]]
    Ifte c t e -> Set.unions $ cIte p r :
        [cComp procs (p ++ [c]) r | c <- [0,1,2]]
-- Atomic goals (sec 5.2.4)
    Atom (Unif u v) -> Set.singleton $ nand p u v
    Atom (Func _ [] _) -> Set.empty
    Atom (Func _ [v] u) -> Set.singleton $ nand p u v
    Atom (Func _ (v:vs) u) -> Set.fromList $
        nand p u v : [term p v `Sat.Iff` term p v' | v' <- vs]
    Atom (Pred name vars)
      | Rule rname rvars _ <- r, name == rname, length vars == length rvars -> Set.fromList $ do
        (u,v) <- zip vars rvars
        pure $ term p u `Sat.Iff` term [] v
      | Just (_, procs') <- lookup (name, length vars) procs ->
        Set.singleton . foldr1 Sat.Disj . nub . sort $ do
            (_, Right (Rule _ mvars _)) <- procs'
            pure . foldr1 Sat.Conj $ do
                (v,mv) <- zip vars mvars
                let t = term p v
                pure $ case mv of
                    In _ -> Sat.Neg t
                    Out _ -> t
      | otherwise -> error $ "unknown predicate "++ name ++"/"++ show (length vars)

constraints :: CState -> Rule Var Var -> Constraints
constraints procs rule = Set.map (Sat.simp . Sat.subst env) cs
  where cs = cComp procs [] rule
        env = Map.fromList $
            [(i, Sat.Top) | Sat.Var i <- Set.elems cs] ++
            [(i, Sat.Bottom) | Sat.Neg (Sat.Var i) <- Set.elems cs]

solveConstraints :: CState -> Rule Var Var -> IO (Set Constraints)
solveConstraints procs rule = do
    let cs = constraints procs rule
    Sat.Solutions solutions <- Sat.solveProp . foldr1 Sat.Conj $ Set.elems cs
    return . Set.fromList $ Set.fromList <$> solutions

unsafeSolveConstraints :: CState -> Rule Var Var -> Set Constraints
unsafeSolveConstraints procs = unsafePerformIO . solveConstraints procs

mode :: Rule Var Var -> Constraints -> Either String (Rule ModedVar ModedVar)
mode r@(Rule name vars body) soln = case walk [] body of
    Left cycle -> Left $ "mode ordering failure, cyclic dependency: "++
                    intercalate " -> " (show <$> toList cycle)
    Right body' -> Right $ Rule name (annotate [] <$> vars) body'
  where annotate p (V v) | term p (V v) `Set.member` soln = Out v
                         | Sat.Neg (term p (V v)) `Set.member` soln = In v
        walk p (Disj disj) = Disj <$> sequence [walk (p ++ [d]) g | (d,g) <- zip [0..] disj]
        walk p (Conj conj) = do
            conj' <- sequence [walk (p ++ [c]) g | (c,g) <- zip [0..] conj]
            conj'' <- sortConj [(g, nonlocals (p ++ [c]) r)
                             | (c,g) <- zip [0..] conj']
            pure $ Conj conj''
        walk p (Ifte c t e) = do
            c' <- walk (p ++ [0]) c
            t' <- walk (p ++ [1]) t
            e' <- walk (p ++ [2]) e
            pure $ Ifte c' t' e'
        walk p (Atom a) = pure . Atom $ annotate p <$> a

mode' :: CState -> Rule Var Var -> CState
mode' procs rule@(Rule name vars _) = procs ++
    [ ( (name, length vars)
      , ( (rule, constraints procs rule)
        , [ (soln, mode rule soln)
          | soln <- Set.elems $ unsafeSolveConstraints procs rule]
        )
      )
    ]

sortConj :: [(Goal ModedVar, Set Var)] -> Either (Cycle DepNode) [Goal ModedVar]
sortConj gs = map unDepNode <$> topSort (overlay vs es)
  where vs = vertices $ zipWith DepNode [0..] (fst <$> gs)
        es = edges $ do
            let ins  = [Set.fromList [v | V v <- Set.elems nl
                                        , In v `elem` g
                                        , Out v `notElem` g] | (g,nl) <- gs]
                outs = [Set.fromList [v | V v <- Set.elems nl
                                        , Out v `elem` g] | (g,nl) <- gs]
            (i,(g,_)) <- zip [0..] gs
            (j,(h,_)) <- zip [0..] gs
            guard . not . Set.null $ Set.intersection (outs !! i) (ins !! j)
            return (DepNode i g, DepNode j h)

mv :: ModedVar -> Text
mv = T.pack . show . stripMode

cgFunc :: Name -> [ModedVar] -> Text
cgFunc ":" [u,v] = "(" <> mv u <> ":" <> mv v <> ")"
cgFunc name [] = T.pack name
cgFunc name vs = "(" <> T.unwords (T.pack name : map mv vs) <> ")"

cgPred :: Name -> [ModedVar] -> (Text, Text)
cgPred name vs =
    ( "(" <> T.intercalate "," [T.pack v | Out v <- vs] <> ")"
    , T.pack name <> "_" <> T.pack (modes vs) <> " " <> T.intercalate " " [T.pack v | In v <- vs])
  where modes [] = ""
        modes (In  _:vs) = 'i' : modes vs
        modes (Out _:vs) = 'o' : modes vs

cgAtom :: Atom ModedVar -> Text
cgAtom (Unif (Out u) v) = T.pack u <> " <- pure " <> mv v
cgAtom (Unif u (Out v)) = T.pack v <> " <- pure " <> mv u
cgAtom (Unif u v) = "guard $ " <> mv u <> " == " <> mv v
cgAtom (Func name vs@(Out v:_) u) = cgFunc name vs <> " <- pure " <> mv u
cgAtom (Func name vs (Out u)) = T.pack u <> " <- pure " <> cgFunc name vs
cgAtom (Func name vs u) = "guard $ " <> mv u <> " == " <> cgFunc name vs
cgAtom (Pred name vars) = lhs <> " <- " <> rhs
  where (lhs,rhs) = cgPred name vars

cgGoal :: Path -> Rule ModedVar ModedVar -> Text
cgGoal p r = case extract p $ body r of
    Disj disj -> T.intercalate " <|> " [cgGoal (p ++ [d]) r | d <- take (length disj) [0..]]
    Conj conj ->
        let code = T.unlines $ do
                c <- take (length conj) [0..]
                let p' = p ++ [c]
                pure $ case extract p' $ body r of
                    Atom a -> cgAtom a
                    g -> "(" <> T.intercalate ","
                        [T.pack v | V v <- Set.elems $ nonlocals' p' r
                                  , Out v `elem` g]
                        <> ") <- " <> cgGoal p' r
            ret = T.intercalate "," [T.pack v | V v <- Set.elems $ nonlocals' p r
                                              , Out v `elem` Conj conj]
        in [text|
            (do
              $code
              pure ($ret)
             )
        |]
    Ifte c t e -> "ifte (" <> cgGoal (p ++ [0]) r <> ") (\\(" <> cret <> ") -> " <> cgGoal (p ++ [1]) r <> ") (" <> cgGoal (p ++ [2]) r <> ")"
      where cret = T.intercalate ","
                [T.pack v | V v <- Set.elems $ nonlocals' (p ++ [0]) r
                          , Out v `elem` c]
    Atom a -> cgAtom a

cgRule :: Rule ModedVar ModedVar -> Text
cgRule r@(Rule name vars body) =
    let (lhs,rhs) = cgPred name vars
        code = cgGoal [] r
        rets = T.intercalate "," [T.pack v | V v <- Set.elems $ nonlocals' [] r, Out v `elem` body]
    in [text|
        $rhs = do
          ($rets) <- $code
          pure $lhs
    |]

compile :: Prog Var Var -> Text
compile rules = [text|
    import Control.Applicative
    import Control.Monad.Logic

    $code
  |]
  where cstate = foldl mode' [] rules
        code = T.unlines $ do
            ((name, arity), ((rule, constraints), procs)) <- cstate
            let doc = T.pack <$>
                    [ "{- "++ name ++"/"++ show arity
                    , show rule
                    , "constraints:"
                    ] ++ map show (Set.elems constraints)
                      ++ ["-}"]
                defs = do
                    (def:defs) <- groupBy (\a b -> comparing (head . T.words) a b == EQ) . sort $ do
                        (soln,p) <- procs
                        pure $ case p of
                            Left e -> "-- " <> T.pack e
                            Right r -> T.unlines $
                                let (hd:tl) = T.lines $ cgRule r
                                    meta = "  -- solution: " <>
                                        T.unwords (T.pack . show <$> Set.elems soln)
                                in hd : meta : tl
                    def : (T.unlines . map commentLine . T.lines <$> defs)
                commentLine l | "--" `T.isPrefixOf` l = l
                              | otherwise = "--" <> l
            doc ++ defs

combineDefs :: Prog Val Val -> Prog Var Val
combineDefs rules = do
    let p (Rule n vs _) (Rule n' vs' _) = n == n' && length vs == length vs'
    defs <- groupBy p rules
    let Rule name vars _ = head defs
        params = [V $ "arg" ++ show i | i <- [1..length vars]]
        body' = Disj $ do
            Rule _ vars body <- defs
            pure . Conj $ (Atom <$> zipWith Unif (Var <$> params) vars) ++ [body]
    pure $ Rule name params body'

superhomogeneous :: Rule Var Val -> Rule Var Var
superhomogeneous (Rule name args body) = Rule name args (tGoal body)
  where tVal :: Val -> State [Atom Var] Var
        tVal (Var v) = return v
        tVal (Cons name vs) = do
            vs' <- mapM tVal vs
            body <- get
            let u = V $ "data" ++ show (length body)
            put $ body ++ [Func name vs' u]
            return u
        tAtom :: Atom Val -> State [Atom Var] (Atom Var)
        tAtom (Unif (Var u) (Var v)) = return $ Unif u v
        tAtom (Unif (Var u) (Cons name vs)) = do
            vs' <- mapM tVal vs
            return $ Func name vs' u
        tAtom (Unif u v) = error $ "tAtom "++ show (Unif u v)
        tAtom (Func name vs u) = do
            u' <- tVal u
            vs' <- mapM tVal vs
            return $ Func name vs' u'
        tAtom (Pred name vs) = do
            vs' <- mapM tVal vs
            return $ Pred name vs'
        tGoal :: Goal Val -> Goal Var
        tGoal (Disj gs) = Disj $ tGoal <$> gs
        tGoal (Conj gs) = Conj $ tGoal <$> gs
        tGoal (Ifte c t e) = Ifte (tGoal c) (tGoal t) (tGoal e)
        tGoal (Atom a) = if null body then Atom a' else Conj $ Atom <$> a' : body
          where (a', body) = runState (tAtom a) []

distinctVars :: Rule Var Var -> Rule Var Var
distinctVars (Rule name args body) = Rule name args $ evalState (tGoal body) 0
  where vars (Atom (Func _ vs _)) = vs
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
            return . Conj $ Atom <$> Pred name vs': concat body
        tGoal (Atom a) = return $ Atom a
        tVars dups vs = fmap unzip . forM vs $ \v ->
            if v `elem` dups
            then do
                count <- get
                put $ count + 1
                let v' = V (show v ++ show count)
                return (v', [Unif v' v])
            else return (v, [])
