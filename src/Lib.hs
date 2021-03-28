{-# LANGUAGE DeriveFunctor, DeriveFoldable, OverloadedStrings, QuasiQuotes #-}
module Lib where

import Data.Graph
import Data.Foldable
import Data.List
import Data.Monoid
import qualified Data.Set as Set
import Data.Set (Set)
import NeatInterpolation
import qualified Picologic
import qualified Data.Text as T
import Data.Text (Text)

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
cComp :: Path -> Rule Var -> Constraints
cComp p r = cGen p r `Set.union` cGoal p r

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
cGoal :: Path -> Rule Var -> Constraints
cGoal [] r = Set.unions $ cDisj r : [cComp [d] r | d <- take (length disj) [0..]]
    where disj = body r
cGoal [d] r = Set.unions $ cConj d conj : [cComp [d,c] r | c <- take (length conj) [0..]]
    where conj = body r !! d
-- Atomic goals (sec 5.2.4)
cGoal p@[d,c] r = case body r !! d !! c of
    Unif u v -> Set.singleton $ nand p u v
    Func _ [] _ -> Set.empty
    Func _ [v] u -> Set.singleton $ nand p u v
    Func _ (v:vs) u -> Set.fromList $
        nand p u v : [term p v `Picologic.Iff` term p v' | v' <- vs]
    Pred name vars | Rule rname rvars _ <- r, name == rname -> Set.fromList $ do
        (u,v) <- zip vars rvars
        pure $ term p u `Picologic.Iff` term [] v

solveConstraints :: Rule Var -> IO (Set Constraints)
solveConstraints rule = do
    Picologic.Solutions solutions <- Picologic.solveProp . foldr1 Picologic.Conj . Set.elems $ cComp [] rule
    return . Set.fromList $ Set.fromList <$> solutions

mode :: Constraints -> Rule Var -> Rule ModedVar
mode soln (Rule name vars disj) = Rule name (annotate [] <$> vars) $ do
    (d,conj) <- zip [0..] disj
    pure $ sortConj [annotate [d,c] <$> g | (c,g) <- zip [0..] conj]
  where annotate p v | term p v `Set.member` soln = Out v
                     | Picologic.Neg (term p v) `Set.member` soln = In v

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
