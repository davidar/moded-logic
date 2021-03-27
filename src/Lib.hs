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
          | Conj [Goal]
          | Disj [Goal]
          | Soft Goal Goal Goal

data Rule = Rule Name [Var] Goal

type Path = [Int]

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
    show (Conj goals) = "do\n\t"++ (intercalate "\n\t" $ show <$> goals)

instance Show Rule where
    show (Rule name vars (Disj goals)) = rhs ++" = ("++ (intercalate ("\n\t"++ ret ++"\n ) <|> (") $ show <$> goals) ++"\n\t"++ ret ++"\n )"
        where (lhs,rhs) = showPred name vars
              ret = "pure "++ lhs

dropIndex :: Int -> [a] -> [a]
dropIndex i xs = h ++ drop 1 t
    where (h, t) = splitAt i xs

body :: Rule -> Goal
body (Rule _ _ goal) = goal

subgoals :: Goal -> [Goal]
subgoals (Conj goals) = goals
subgoals (Disj goals) = goals
subgoals (Soft if_ then_ else_) = [if_, then_, else_]
subgoals _ = []

variables :: Goal -> Set Var
variables (Unif x y) = Set.fromList [x, y]
variables (Func _ vars var) = Set.fromList (var : vars)
variables (Pred _ vars) = Set.fromList vars
variables g = Set.unions $ variables <$> subgoals g

outside :: Path -> Goal -> Set Var
outside p g = case p of
    [] -> Set.empty
    (c:cs) -> Set.unions (outside cs (subgoals g !! c) : (variables <$> dropIndex c (subgoals g)))

outside' :: Path -> Rule -> Set Var
outside' p (Rule _ vars goal) = Set.fromList vars `Set.union` outside p goal

extract :: Path -> Goal -> Goal
extract [] g = g
extract (c:cs) g = extract cs $ subgoals g !! c

nonlocals :: Path -> Rule -> Set Var
nonlocals p r = (variables . extract p $ body r) `Set.intersection` outside' p r

locals :: Path -> Rule -> Set Var
locals p r = (variables . extract p $ body r) Set.\\ outside' p r

term :: Var -> Path -> Picologic.Expr
term v p = Picologic.Var . Picologic.Ident $ v ++ show p

constraints' :: Rule -> Picologic.Expr
constraints' = foldr1 Picologic.Conj . constraints []

constraints :: Path -> Rule -> [Picologic.Expr]
constraints p r = [term v p | v <- Set.toList (locals p r)] ++ case extract p (body r) of
    Disj goals -> do
        d <- take (length goals) [0..]
        let p' = p ++ [d]
        [Picologic.Iff (term v p) (term v p') | v <- Set.toList (nonlocals p r)] ++
            constraints p' r
    Conj goals -> (do
        v <- Set.toList (variables (Conj goals))
        let terms = [term v (p ++ [c]) | (c,g) <- zip [0..] goals, Set.member v (variables g)]
        [Picologic.Iff (term v p) (foldr1 Picologic.Disj terms)] ++
            [Picologic.Neg (Picologic.Conj s t) | s <- terms, t <- terms, s < t]) ++
            concat [constraints (p ++ [c]) r | (c,g) <- zip [0..] goals]
    Unif u v -> [Picologic.Neg (Picologic.Conj (term u p) (term v p))]
    Func _ [] u -> []
    Func _ [v] u ->
        [Picologic.Neg (Picologic.Conj (term u p) (term v p))]
    Func _ (v:vs) u ->
        [Picologic.Iff (term v p) (term v' p) | v' <- vs] ++
            [Picologic.Neg (Picologic.Conj (term u p) (term v p))]
    Pred name vars | Rule rname rvars _ <- r, name == rname ->
        [Picologic.Iff (term u p) (term v []) | (u,v) <- zip vars rvars]

mode :: [Picologic.Expr] -> Rule -> Rule
mode soln (Rule name vars goal) = Rule name (annotate [] <$> vars) (go [] goal)
    where annotate p v | term v p `elem` soln = v ++".o"
                       | Picologic.Neg (term v p) `elem` soln = v ++".i"
          go p (Unif u v) = Unif (annotate p u) (annotate p v)
          go p (Func name vs u) = Func name (annotate p <$> vs) (annotate p u)
          go p (Pred name vs) = Pred name (annotate p <$> vs)
          go p (Conj gs) = Conj $ sortConj [go (p ++ [i]) g | (i,g) <- zip [0..] gs]
          go p (Disj gs) = Disj [go (p ++ [i]) g | (i,g) <- zip [0..] gs]
          go p (Soft if_ then_ else_) = Soft (go (p ++ [0]) if_) (go (p ++ [1]) then_) (go (p ++ [2]) else_)

unSCC :: SCC a -> a
unSCC (AcyclicSCC v) = v
unSCC (CyclicSCC _) = error "cyclic dependency"

sortConj :: [Goal] -> [Goal]
sortConj gs = map unSCC . stronglyConnComp $ do
    let ins  = [Set.fromList [take (length v - 2) v
                             | v <- Set.toList (variables g), ".i" `isSuffixOf` v] | g <- gs]
        outs = [Set.fromList [take (length v - 2) v
                             | v <- Set.toList (variables g), ".o" `isSuffixOf` v] | g <- gs]
    (i,g) <- zip [0..] gs
    let js = [j | j <- take (length gs) [0..]
                , not . Set.null $ Set.intersection (ins !! i) (outs !! j)]
    return (g, i, js)
