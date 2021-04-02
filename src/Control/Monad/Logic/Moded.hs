{-# LANGUAGE DeriveFunctor, DeriveFoldable, FlexibleContexts, FlexibleInstances, OverloadedStrings, QuasiQuotes #-}
module Control.Monad.Logic.Moded where

import Algebra.Graph.AdjacencyMap
import Algebra.Graph.AdjacencyMap.Algorithm
import Control.Monad
import Control.Monad.State
import Data.Foldable
import Data.List
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

data Goal v = Unif v v
            | Func Name [v] v
            | Pred Name [v]
            deriving (Eq, Ord, Functor, Foldable)

data Rule v = Rule Name [v] [[Goal v]]

type Path = [Int]

type Constraints = Set Sat.Expr

data ModedVar = In String | Out String
              deriving (Eq, Ord)

type Prog v = [Rule v]

type CState = [((Name, Int), ((Rule Var, Constraints), [Either String (Rule ModedVar)]))]

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

instance (Show v) => Show (Goal v) where
    show (Unif u v) = show u ++" = "++ show v
    show (Func ":" [h,t] u) = show u ++" = "++ show h ++" : "++ show t
    show (Func name vs u) = show u ++" = "++ unwords (name : map show vs)
    show (Pred name []) = name
    show (Pred name vs) = unwords (name : map show vs)

instance (Show v) => Show (Rule v) where
    show (Rule name vars disj) =
        unwords (name : map show vars) ++" :-\n  "++
            (intercalate ";\n  " $ intercalate ", " . map show <$> disj) ++"."

instance Show Val where
    show (Var v) = show v
    show (Cons name vs) = unwords (name : map show vs)

instance Show DepNode where
    show (DepNode i g) = "["++ show i ++"] "++ show g

dropIndex :: Int -> [a] -> [a]
dropIndex i xs = h ++ drop 1 t
  where (h, t) = splitAt i xs

body :: Rule v -> [[Goal v]]
body (Rule _ _ goal) = goal

stripMode :: ModedVar -> Var
stripMode (In v) = V v
stripMode (Out v) = V v

unDepNode :: DepNode -> Goal ModedVar
unDepNode (DepNode _ g) = g

variables :: Goal v -> [v]
variables = toList

term :: Path -> Var -> Sat.Expr
term p (V v) = Sat.Var . Sat.Ident $ v ++ show p

-- | Complete set of constraints (sec 5.2.2)
cComp :: CState -> Path -> Rule Var -> Constraints
cComp procs p r = cGen p r `Set.union` cGoal procs p r

-- | General constraints (sec 5.2.2)
cGen :: Path -> Rule Var -> Constraints
cGen p r = cLocal p r `Set.union` cExt p r

-- | Local constraints (sec 5.2.2)
cLocal :: Path -> Rule Var -> Constraints
cLocal [] (Rule _ vars disj) =
    let inside = Set.fromList $ do
            conj <- disj
            conj >>= variables
        outside = Set.fromList vars
        locals = inside Set.\\ outside
    in term [] `Set.map` locals
cLocal [d] (Rule _ vars disj) =
    let conj = disj !! d
        inside = Set.fromList $ conj >>= variables
        outside = Set.fromList $ vars ++ do
            conj' <- dropIndex d disj
            conj' >>= variables
        locals = inside Set.\\ outside
    in term [d] `Set.map` locals
cLocal [d,c] (Rule _ vars disj) =
    let conj = disj !! d
        inside = Set.fromList . variables $ conj !! c
        outside = Set.fromList $ vars ++ (dropIndex c conj >>= variables) ++ do
            conj' <- dropIndex d disj
            conj' >>= variables
        locals = inside Set.\\ outside
    in term [d,c] `Set.map` locals

-- | External constraints (sec 5.2.2)
cExt _ _ = Set.empty

-- | Disjunction constraints (sec 5.2.3)
cDisj :: Rule Var -> Constraints
cDisj (Rule _ vars disj) = Set.unions $ do
    (d, conj) <- zip [0..] disj
    let inside = Set.fromList $ conj >>= variables
        outside = Set.fromList $ vars ++ do
            conj' <- dropIndex d disj
            conj' >>= variables
        nonlocals = inside `Set.intersection` outside
    pure $ Set.map (\v -> term [] v `Sat.Iff` term [d] v) nonlocals

-- | Conjunction constraints (sec 5.2.3)
cConj :: Int -> [Goal Var] -> Constraints
cConj d conj = Set.fromList $ do
    v <- nub $ conj >>= variables
    let terms = [term [d,c] v | (c,g) <- zip [0..] conj, v `elem` variables g]
        c = term [d] v `Sat.Iff` foldr1 Sat.Disj terms
        cs = [Sat.Neg (Sat.Conj s t) | s <- terms, t <- terms, s < t]
    (c:cs)

nand :: Path -> Var -> Var -> Sat.Expr
nand p u v = Sat.Neg (Sat.Conj (term p u) (term p v))

-- | Goal-specific constraints
cGoal :: CState -> Path -> Rule Var -> Constraints
cGoal procs [] r = Set.unions $ cDisj r : [cComp procs [d] r | d <- take (length disj) [0..]]
    where disj = body r
cGoal procs [d] r = Set.unions $ cConj d conj : [cComp procs [d,c] r | c <- take (length conj) [0..]]
    where conj = body r !! d
-- Atomic goals (sec 5.2.4)
cGoal procs p@[d,c] r = case body r !! d !! c of
    Unif u v -> Set.singleton $ nand p u v
    Func _ [] _ -> Set.empty
    Func _ [v] u -> Set.singleton $ nand p u v
    Func _ (v:vs) u -> Set.fromList $
        nand p u v : [term p v `Sat.Iff` term p v' | v' <- vs]
    Pred name vars
      | Rule rname rvars _ <- r, name == rname, length vars == length rvars -> Set.fromList $ do
        (u,v) <- zip vars rvars
        pure $ term p u `Sat.Iff` term [] v
      | Just (_, procs') <- lookup (name, length vars) procs ->
        Set.singleton . foldr1 Sat.Disj . nub . sort $ do
            Right (Rule _ mvars _) <- procs'
            pure . foldr1 Sat.Conj $ do
                (v,mv) <- zip vars mvars
                let t = term p v
                pure $ case mv of
                    In _ -> Sat.Neg t
                    Out _ -> t
      | otherwise -> error $ "unknown predicate "++ name ++"/"++ show (length vars)

solveConstraints :: CState -> Rule Var -> IO (Set Constraints)
solveConstraints procs rule = do
    let cs = cComp procs [] rule
    Sat.Solutions solutions <- Sat.solveProp . foldr1 Sat.Conj $ Set.elems cs
    return . Set.fromList $ Set.fromList <$> solutions

unsafeSolveConstraints :: CState -> Rule Var -> Set Constraints
unsafeSolveConstraints procs = unsafePerformIO . solveConstraints procs

mode :: Rule Var -> Constraints -> Either String (Rule ModedVar)
mode (Rule name vars disj) soln = case disj' of
    Left cycle -> Left $ "mode ordering failure, cyclic dependency: "++
                    intercalate " -> " (show <$> toList cycle)
    Right r -> Right $ Rule name (annotate [] <$> vars) r
  where annotate p (V v) | term p (V v) `Set.member` soln = Out v
                         | Sat.Neg (term p (V v)) `Set.member` soln = In v
        disj' = sequence $ do
            (d,conj) <- zip [0..] disj
            pure $ sortConj [annotate [d,c] <$> g | (c,g) <- zip [0..] conj]

mode' :: CState -> Rule Var -> CState
mode' procs rule@(Rule name vars _) = procs ++
    [((name, length vars), ((rule, cComp procs [] rule), mode rule <$> Set.elems (unsafeSolveConstraints procs rule)))]

sortConj :: [Goal ModedVar] -> Either (Cycle DepNode) [Goal ModedVar]
sortConj gs = map unDepNode <$> topSort (overlay vs es)
  where vs = vertices $ zipWith DepNode [0..] gs
        es = edges $ do
            let ins  = [Set.fromList [v | In  v <- variables g] | g <- gs]
                outs = [Set.fromList [v | Out v <- variables g] | g <- gs]
            (i,g) <- zip [0..] gs
            (j,h) <- zip [0..] gs
            guard . not . Set.null $ Set.intersection (outs !! i) (ins !! j)
            return (DepNode i g, DepNode j h)

mv :: ModedVar -> Text
mv = T.pack . show . stripMode

cgFunc :: Name -> [ModedVar] -> Text
cgFunc name [] = T.pack name
cgFunc ":" [u,v] = "(" <> mv u <> ":" <> mv v <> ")"

cgPred :: Name -> [ModedVar] -> (Text, Text)
cgPred name vs =
    ( "(" <> T.intercalate "," [T.pack v | Out v <- vs] <> ")"
    , T.pack name <> "_" <> T.pack (modes vs) <> " " <> T.intercalate " " [T.pack v | In v <- vs])
  where modes [] = ""
        modes (In  _:vs) = 'i' : modes vs
        modes (Out _:vs) = 'o' : modes vs

cgGoal :: Goal ModedVar -> Text
cgGoal (Unif (Out u) v) = T.pack u <> " <- pure " <> mv v
cgGoal (Unif u (Out v)) = T.pack v <> " <- pure " <> mv u
cgGoal (Unif u v) = "guard $ " <> mv u <> " == " <> mv v
cgGoal (Func name vs@(Out v:_) u) = cgFunc name vs <> " <- pure " <> mv u
cgGoal (Func name vs (Out u)) = T.pack u <> " <- pure " <> cgFunc name vs
cgGoal (Func name vs u) = "guard $ " <> mv u <> " == " <> cgFunc name vs
cgGoal (Pred name vars) = lhs <> " <- " <> rhs
  where (lhs,rhs) = cgPred name vars

cgRule :: Rule ModedVar -> Text
cgRule (Rule name vars disj) = ((rhs <>" = ")<>) . T.intercalate " <|> " $ do
    conj <- disj
    let body = T.unlines $ cgGoal <$> conj
    pure [text|
        (do
          $body
          pure $lhs
         )
     |]
  where (lhs,rhs) = cgPred name vars

compile :: Prog Var -> Text
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
                        p <- procs
                        pure $ case p of
                            Left e -> "-- " <> T.pack e
                            Right r -> cgRule r
                    def : (T.unlines . map commentLine . T.lines <$> defs)
                commentLine l | "--" `T.isPrefixOf` l = l
                              | otherwise = "--" <> l
            doc ++ defs

combineDefs :: Prog Val -> Prog Val
combineDefs rules = do
    let p (Rule n vs _) (Rule n' vs' _) = n == n' && length vs == length vs'
    defs <- groupBy p rules
    if length defs == 1 then pure (head defs) else do
        let Rule name vars _ = head defs
            params = [Var . V $ "arg" ++ show i | i <- [1..length vars]]
            disj' = do
                Rule _ vars disj <- defs
                [zipWith Unif params vars ++ conj | conj <- disj]
        pure $ Rule name params disj'

superhomogeneous :: Rule Val -> Rule Var
superhomogeneous (Rule name args disj) = Rule name vars disj'
  where (vars, argbody) = runState (mapM tVal args) []
        disj' :: [[Goal Var]]
        disj' = do
            conj <- disj
            let (conj', body) = runState (mapM tGoal conj) argbody
            pure $ body ++ conj'
        tVal :: Val -> State [Goal Var] Var
        tVal (Var v) = return v
        tVal (Cons name vs) = do
            vs' <- mapM tVal vs
            body <- get
            let u = V $ "data" ++ show (length body)
            put $ body ++ [Func name vs' u]
            return u
        tGoal :: Goal Val -> State [Goal Var] (Goal Var)
        tGoal (Unif (Var u) (Var v)) = return $ Unif u v
        tGoal (Unif (Var u) (Cons name vs)) = do
            vs' <- mapM tVal vs
            return $ Func name vs' u
        tGoal (Unif u v) = error $ "tGoal "++ show (Unif u v)
        tGoal (Func name vs u) = do
            u' <- tVal u
            vs' <- mapM tVal vs
            return $ Func name vs' u'
        tGoal (Pred name vs) = do
            vs' <- mapM tVal vs
            return $ Pred name vs'

distinctFuncVars :: Rule Var -> Rule Var
distinctFuncVars (Rule name args disj) = Rule name args $ do
    conj <- disj
    let vars = do
            goal <- conj
            case goal of
                Func _ vs _ -> vs
                _ -> []
        fdups = [(head l, length l) | l <- group (sort vars), length l > 1]
        tVar dups (V v) | V v `elem` map fst dups = do
            body <- get
            let v' = v ++ show (length body)
            put $ body ++ [Unif (V v') (V v)]
            return (V v')
        tVar _ v = return v
        tGoal (Func name vs u) = do
            vs' <- mapM (tVar fdups) vs
            return $ Func name vs' u
        tGoal (Pred name vs) = do
            let pdups = [(head l, length l) | l <- group (sort vs), length l > 1]
            vs' <- mapM (tVar pdups) vs
            return $ Pred name vs'
        tGoal g = return g
        (conj', body) = runState (mapM tGoal conj) []
    pure $ body ++ conj'
