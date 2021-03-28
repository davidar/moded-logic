module Lib where

import Data.Char
import Data.Graph
import Data.List
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Picologic

type Name = String
type Var = String

data Goal = Unif Var Var
          | Func Name [Var] Var
          | Pred Name [Var]

data Rule = Rule Name [Var] [[Goal]]

type Path = [Int]

type Constraints = Set Picologic.Expr

showVar :: Var -> String
showVar v = toLower <$> take (length v - 2) v

showFunc :: Name -> [Var] -> String
showFunc name [] = name
showFunc ":" [u,v] = "("++ showVar u ++":"++ showVar v ++")"

showPred :: Name -> [Var] -> (String,String)
showPred name vs =
    ( "("++ intercalate "," [showVar v | v <- vs, ".o" `isSuffixOf` v] ++")"
    , name ++"_"++ (last <$> vs) ++" "++ intercalate " " [showVar v | v <- vs, ".i" `isSuffixOf` v])

instance Show Goal where
    show (Unif u v) | ".o" `isSuffixOf` v = showVar v ++" <- pure "++ showVar u
                    | ".o" `isSuffixOf` u = showVar u ++" <- pure "++ showVar v
                    | otherwise = "guard $ "++ showVar u ++" == "++ showVar v
    show (Func name vs u)
        | (v:_) <- vs, ".o" `isSuffixOf` v = showFunc name vs ++" <- pure "++ showVar u
        | ".o" `isSuffixOf` u = showVar u ++" <- pure "++ showFunc name vs
        | otherwise = "guard $ "++ showVar u ++" == "++ showFunc name vs
    show (Pred name vars) = lhs ++" <- "++ rhs
        where (lhs,rhs) = showPred name vars

instance Show Rule where
    show (Rule name vars disj) = rhs ++" = ("++ (intercalate ("\n\t"++ ret ++"\n ) <|> (") ["do\n\t"++ (intercalate "\n\t" $ show <$> conj) | conj <- disj]) ++"\n\t"++ ret ++"\n )"
        where (lhs,rhs) = showPred name vars
              ret = "pure "++ lhs

dropIndex :: Int -> [a] -> [a]
dropIndex i xs = h ++ drop 1 t
    where (h, t) = splitAt i xs

body :: Rule -> [[Goal]]
body (Rule _ _ goal) = goal

variables :: Goal -> [Var]
variables (Unif x y) = [x, y]
variables (Func _ vars var) = (var : vars)
variables (Pred _ vars) = vars

term :: Path -> Var -> Picologic.Expr
term p v = Picologic.Var . Picologic.Ident $ v ++ show p

-- | Complete set of constraints (sec 5.2.2)
cComp :: Path -> Rule -> Constraints
cComp p r = cGen p r `Set.union` cGoal p r

-- | General constraints (sec 5.2.2)
cGen :: Path -> Rule -> Constraints
cGen p r = cLocal p r `Set.union` cExt p r

-- | Local constraints (sec 5.2.2)
cLocal :: Path -> Rule -> Constraints
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
cDisj :: Rule -> Constraints
cDisj (Rule _ vars disj) = Set.unions $ do
    (d, conj) <- zip [0..] disj
    let inside = Set.fromList $ conj >>= variables
        outside = Set.fromList $ vars ++ do
            conj' <- dropIndex d disj
            conj' >>= variables
        nonlocals = inside `Set.intersection` outside
    pure $ Set.map (\v -> term [] v `Picologic.Iff` term [d] v) nonlocals

-- | Conjunction constraints (sec 5.2.3)
cConj :: Int -> [Goal] -> Constraints
cConj d conj = Set.fromList $ do
    v <- nub $ conj >>= variables
    let terms = [term [d,c] v | (c,g) <- zip [0..] conj, v `elem` variables g]
        c = term [d] v `Picologic.Iff` foldr1 Picologic.Disj terms
        cs = [Picologic.Neg (Picologic.Conj s t) | s <- terms, t <- terms, s < t]
    (c:cs)

nand :: Path -> Var -> Var -> Picologic.Expr
nand p u v = Picologic.Neg (Picologic.Conj (term p u) (term p v))

-- | Goal-specific constraints
cGoal :: Path -> Rule -> Constraints
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

mode :: Constraints -> Rule -> Rule
mode soln (Rule name vars disj) = Rule name (annotate [] <$> vars)
    [sortConj [go [d,c] g | (c,g) <- zip [0..] conj] | (d,conj) <- zip [0..] disj]
    where annotate p v | term p v `Set.member` soln = v ++".o"
                       | Picologic.Neg (term p v) `Set.member` soln = v ++".i"
          go p (Unif u v) = Unif (annotate p u) (annotate p v)
          go p (Func name vs u) = Func name (annotate p <$> vs) (annotate p u)
          go p (Pred name vs) = Pred name (annotate p <$> vs)

unSCC :: SCC a -> a
unSCC (AcyclicSCC v) = v
unSCC (CyclicSCC _) = error "cyclic dependency"

sortConj :: [Goal] -> [Goal]
sortConj gs = map unSCC . stronglyConnComp $ do
    let ins  = [Set.fromList [take (length v - 2) v
                             | v <- variables g, ".i" `isSuffixOf` v] | g <- gs]
        outs = [Set.fromList [take (length v - 2) v
                             | v <- variables g, ".o" `isSuffixOf` v] | g <- gs]
    (i,g) <- zip [0..] gs
    let js = [j | j <- take (length gs) [0..]
                , not . Set.null $ Set.intersection (ins !! i) (outs !! j)]
    return (g, i, js)
