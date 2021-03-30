{-# LANGUAGE DeriveFunctor, DeriveFoldable, FlexibleInstances, OverloadedStrings, QuasiQuotes #-}
module Control.Monad.Logic.Moded where

import Control.Monad
import Data.Graph
import Data.Foldable
import Data.List
import Data.Monoid
import Data.Ord
import qualified Data.Set as Set
import Data.Set (Set)
import NeatInterpolation
import qualified Picologic
import qualified Data.Text as T
import Data.Text (Text)
import System.IO.Unsafe

type Name = String
type Var = String

data Goal v = Unif v v
            | Func Name [v] v
            | Pred Name [v]
            deriving (Functor, Foldable)

data Rule v = Rule Name [v] [[Goal v]]

type Path = [Int]

type Constraints = Set Picologic.Expr

data ModedVar = In Var | Out Var

type Prog v = [Rule v]

type CState = [Rule ModedVar]

instance Show (Goal Var) where
    show (Unif u v) = u ++" = "++ v
    show (Func ":" [h,t] u) = u ++" = "++ h ++" : "++ t
    show (Func name vs u) = u ++" = "++ unwords (name : vs)
    show (Pred name []) = name
    show (Pred name vs) = unwords (name : vs)

instance Show (Rule Var) where
    show (Rule name vars disj) = unwords (name : vars) ++" :-\n\t"++ (intercalate ";\n\t" $ intercalate ", " . map show <$> disj) ++"."

dropIndex :: Int -> [a] -> [a]
dropIndex i xs = h ++ drop 1 t
  where (h, t) = splitAt i xs

body :: Rule v -> [[Goal v]]
body (Rule _ _ goal) = goal

stripMode :: ModedVar -> Var
stripMode (In v) = v
stripMode (Out v) = v

variables :: Goal v -> [v]
variables = toList

term :: Path -> Var -> Picologic.Expr
term p v = Picologic.Var . Picologic.Ident $ v ++ show p

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
    pure $ Set.map (\v -> term [] v `Picologic.Iff` term [d] v) nonlocals

-- | Conjunction constraints (sec 5.2.3)
cConj :: Int -> [Goal Var] -> Constraints
cConj d conj = Set.fromList $ do
    v <- nub $ conj >>= variables
    let terms = [term [d,c] v | (c,g) <- zip [0..] conj, v `elem` variables g]
        c = term [d] v `Picologic.Iff` foldr1 Picologic.Disj terms
        cs = [Picologic.Neg (Picologic.Conj s t) | s <- terms, t <- terms, s < t]
    (c:cs)

nand :: Path -> Var -> Var -> Picologic.Expr
nand p u v = Picologic.Neg (Picologic.Conj (term p u) (term p v))

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
        nand p u v : [term p v `Picologic.Iff` term p v' | v' <- vs]
    Pred name vars
      | Rule rname rvars _ <- r, name == rname, length vars == length rvars -> Set.fromList $ do
        (u,v) <- zip vars rvars
        pure $ term p u `Picologic.Iff` term [] v
      | procs' <- filterRules name (length vars) procs, not (null procs') ->
        Set.singleton . foldr1 Picologic.Disj $ do
            (Rule _ mvars _) <- procs'
            pure . foldr1 Picologic.Conj $ do
                (v,mv) <- zip vars mvars
                let t = term p v
                pure $ case mv of
                    In _ -> Picologic.Neg t
                    Out _ -> t
      | otherwise -> error $ "unknown predicate "++ name ++"/"++ show (length vars)

filterRules :: Name -> Int -> Prog v -> Prog v
filterRules name arity = filter $ \(Rule s vs _) -> name == s && arity == length vs

solveConstraints :: CState -> Rule Var -> IO (Set Constraints)
solveConstraints procs rule = do
    Picologic.Solutions solutions <- Picologic.solveProp . foldr1 Picologic.Conj . Set.elems $ cComp procs [] rule
    return . Set.fromList $ Set.fromList <$> solutions

unsafeSolveConstraints :: CState -> Rule Var -> Set Constraints
unsafeSolveConstraints procs = unsafePerformIO . solveConstraints procs

mode :: Rule Var -> Constraints -> Rule ModedVar
mode (Rule name vars disj) soln = Rule name (annotate [] <$> vars) $ do
    (d,conj) <- zip [0..] disj
    pure $ sortConj [annotate [d,c] <$> g | (c,g) <- zip [0..] conj]
  where annotate p v | term p v `Set.member` soln = Out v
                     | Picologic.Neg (term p v) `Set.member` soln = In v

mode' :: CState -> Rule Var -> CState
mode' procs rule = procs ++
    (mode rule <$> Set.elems (unsafeSolveConstraints procs rule))

unSCC :: SCC a -> a
unSCC (AcyclicSCC v) = v
unSCC (CyclicSCC _) = error "cyclic dependency"

sortConj :: [Goal ModedVar] -> [Goal ModedVar]
sortConj gs = map unSCC . stronglyConnComp $ do
    let ins  = [Set.fromList [v | In  v <- variables g] | g <- gs]
        outs = [Set.fromList [v | Out v <- variables g] | g <- gs]
    (i,g) <- zip [0..] gs
    let js = [j | j <- take (length gs) [0..]
                , not . Set.null $ Set.intersection (ins !! i) (outs !! j)]
    return (g, i, js)

mv :: ModedVar -> Text
mv = T.pack . stripMode

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
  where procs = foldl mode' [] rules
        funcs = nubBy (\a b -> comparing (head . T.words) a b == EQ) $ cgRule <$> procs
        code = T.unlines funcs
