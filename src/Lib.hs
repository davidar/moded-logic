module Lib where

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

instance Show Goal where
    show (Unif x y) = x ++" = "++ y
    show (Func "[|]" [x,y] var) = var ++" = ["++ x ++" | "++ y ++"]"
    show (Func name [] var) = var ++" = "++ name
    show (Func name vars var) = var ++" = "++ name ++"("++ intercalate ", " vars ++")"
    show (Pred name vars) = name ++"("++ intercalate ", " vars ++")"
    show (Conj goals) = intercalate ", " $ show <$> goals
    show (Disj goals) = "("++ (intercalate "; " $ show <$> goals) ++")"
    show (Soft if_ then_ else_) = show if_ ++" -> "++ show then_ ++"; "++ show else_

instance Show Rule where
    show (Rule name vars goal) = name ++"("++ intercalate ", " vars ++") :- "++ show goal ++"."

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
