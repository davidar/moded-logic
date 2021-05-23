module Control.Monad.Logic.Moded.Path
  ( Path
  , inside
  , insideNonneg
  , nonlocals
  , locals
  , extract
  , extendPath
  ) where

import Control.Monad.Logic.Moded.AST (Goal(..), Rule(..), Var, subgoals)
import Data.Foldable (Foldable(toList))
import qualified Data.Set as Set
import Data.Set (Set)

type Path = [Int]

dropIndex :: Int -> [a] -> [a]
dropIndex i xs = h ++ drop 1 t
  where
    (h, t) = splitAt i xs

-- | Variables inside a goal
inside :: Path -> Rule Var Var -> Set Var
inside p = insideGoal . extract p . ruleBody

insideGoal :: Goal Var -> Set Var
insideGoal = Set.fromList . toList

-- | Variables inside a goal, but not in a negated context
{- An occurrence of a variable is in a negated context if it is in a negation,
   in a universal quantification, in the condition of an if-then-else,
   in an inequality, or in a lambda expression. -}
insideNonneg :: Goal Var -> Set Var
insideNonneg (Atom a) = Set.fromList $ toList a
insideNonneg (Conj gs) = Set.unions $ insideNonneg <$> gs
insideNonneg (Disj gs) = Set.unions $ insideNonneg <$> gs
insideNonneg (Ifte _ t e) = insideNonneg t `Set.union` insideNonneg e
insideNonneg (Anon name _ _) = Set.singleton name

-- | Variables accessible from parent/sibling contexts (not in a parallel goal)
{- Two goals are parallel if they are different disjuncts of the same disjunction,
   or if one is the “else” part of an if-then-else and
   the other goal is either the “then” part or the condition of the if-then-else,
   or if they are the goals of disjoint (distinct and non-overlapping) lambda expressions. -}
outside :: Path -> Goal Var -> Set Var
outside [] _ = Set.empty
outside (c:ps) (Conj gs) =
  Set.unions (insideGoal <$> dropIndex c gs) `Set.union` outside ps (gs !! c)
outside (d:ps) (Disj gs) = outside ps (gs !! d)
outside (0:ps) (Ifte c t _) = insideGoal t `Set.union` outside ps c
outside (1:ps) (Ifte c t _) = insideGoal c `Set.union` outside ps t
outside (2:ps) (Ifte _ _ e) = outside ps e
outside (0:ps) (Anon _ vs g) = Set.fromList vs `Set.union` outside ps g
outside _ _ = error "invalid path"

nonlocals :: Path -> Rule Var Var -> Set Var
nonlocals p r@(Rule _ vars body) = inside p r `Set.intersection` out
  where
    out = Set.fromList vars `Set.union` outside p body

locals :: Path -> Rule Var Var -> Set Var
locals p r@(Rule _ vars body) = inside p r Set.\\ out
  where
    out = Set.fromList vars `Set.union` outside p body

extract :: Path -> Goal v -> Goal v
extract p g = foldl f g p
  where
    f :: Goal v -> Int -> Goal v
    f Atom {} _ = error $ "invalid path " ++ show p
    f g' i = subgoals g' !! i

extendPath :: Path -> Rule u v -> [Path]
extendPath p r =
  [p ++ [i] | i <- take (length . subgoals . extract p $ ruleBody r) [0 ..]]
