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

type Constraints = [Picologic.Expr]

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

term :: Var -> Path -> Picologic.Expr
term v p = Picologic.Var . Picologic.Ident $ v ++ show p

constraints :: Rule -> Picologic.Expr
constraints = foldr1 Picologic.Conj . sort . cComp []

cComp :: Path -> Rule -> Constraints
cComp p r = cGen p r ++ cGoal p r
cGen p r = cLocal p r
cLocal [] (Rule _ vars disj) = do
    let inside = nub $ do
            conj <- disj
            conj >>= variables
        outside = vars
        locals = inside \\ outside
    v <- locals
    pure $ term v []
cLocal [d] (Rule _ vars disj) = do
    let conj = disj !! d
        inside = nub $ conj >>= variables
        outside = nub $ vars ++ do
            conj' <- dropIndex d disj
            conj' >>= variables
        locals = inside \\ outside
    v <- locals
    pure $ term v [d]
cLocal [d,c] (Rule _ vars disj) = do
    let conj = disj !! d
        inside = variables $ conj !! c
        outside = nub $ vars ++ (dropIndex c conj >>= variables) ++ do
            conj' <- dropIndex d disj
            conj' >>= variables
        locals = inside \\ outside
    v <- locals
    pure $ term v [d,c]

cDisj :: Rule -> Constraints
cDisj (Rule _ vars disj) = do
    (d, conj) <- zip [0..] disj
    let inside = nub $ conj >>= variables
        outside = nub $ vars ++ do
            conj' <- dropIndex d disj
            conj' >>= variables
        nonlocals = inside `intersect` outside
    v <- nonlocals
    pure $ term v [] `Picologic.Iff` term v [d]

cConj :: Int -> [Goal] -> Constraints
cConj d conj = do
    let inside = nub $ conj >>= variables
    v <- inside
    let terms = [term v [d,c] | (c,g) <- zip [0..] conj, v `elem` variables g]
        c = term v [d] `Picologic.Iff` foldr1 Picologic.Disj terms
        cs = [Picologic.Neg (Picologic.Conj s t) | s <- terms, t <- terms, s < t]
    (c:cs)

nand p u v = Picologic.Neg (Picologic.Conj (term u p) (term v p))

cGoal :: Path -> Rule -> Constraints
cGoal []  r = cDisj r ++ concat [cComp [d] r | d <- take (length disj) [0..]]
    where disj = body r
cGoal [d] r = cConj d conj ++ concat [cComp [d,c] r | c <- take (length conj) [0..]]
    where conj = body r !! d
cGoal p@[d,c] r = case body r !! d !! c of
    Unif u v -> pure $ nand p u v
    Func _ [] _ -> []
    Func _ [v] u -> pure $ nand p u v
    Func _ (v:vs) u ->
        nand p u v : [term v p `Picologic.Iff` term v' p | v' <- vs]
    Pred name vars | Rule rname rvars _ <- r, name == rname -> do
        (u,v) <- zip vars rvars
        pure $ term u p `Picologic.Iff` term v []

mode :: [Picologic.Expr] -> Rule -> Rule
mode soln (Rule name vars disj) = Rule name (annotate [] <$> vars)
    [sortConj [go [d,c] g | (c,g) <- zip [0..] conj] | (d,conj) <- zip [0..] disj]
    where annotate p v | term v p `elem` soln = v ++".o"
                       | Picologic.Neg (term v p) `elem` soln = v ++".i"
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
