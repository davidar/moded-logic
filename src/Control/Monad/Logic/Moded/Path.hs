module Control.Monad.Logic.Moded.Path
  ( Path
  , inside
  , nonlocals
  , locals
  , extract
  , extendPath
  ) where

import Control.Monad.Logic.Moded.AST (Goal(..), Rule(..), Var, body, subgoals)
import Data.Foldable (Foldable(toList))
import qualified Data.Set as Set
import Data.Set (Set)

type Path = [Int]

dropIndex :: Int -> [a] -> [a]
dropIndex i xs = h ++ drop 1 t
  where
    (h, t) = splitAt i xs

-- | Variables inside a goal
inside :: (Ord v) => Path -> Rule u v -> Set v
inside p = Set.fromList . toList . extract p . body

-- | Variables accessible from parent/sibling contexts
outside :: Path -> Goal Var -> Set Var
outside [] g = Set.empty
outside (c:ps) (Conj gs) =
  Set.fromList (dropIndex c gs >>= toList) `Set.union` outside ps (gs !! c)
outside (d:ps) (Disj gs) = outside ps (gs !! d)
outside (0:ps) (Ifte c t e) = Set.fromList (toList t) `Set.union` outside ps c
outside (1:ps) (Ifte c t e) = Set.fromList (toList c) `Set.union` outside ps t
outside (2:ps) (Ifte c t e) = outside ps e

nonlocals :: Path -> Rule Var Var -> Set Var
nonlocals p r@(Rule _ vars body) = inside p r `Set.intersection` out
  where
    out = Set.fromList vars `Set.union` outside p body

locals :: Path -> Rule Var Var -> Set Var
locals p r@(Rule _ vars body) = inside p r Set.\\ out
  where
    out = Set.fromList vars `Set.union` outside p body

extract :: Path -> Goal v -> Goal v
extract = flip . foldl $ \g i -> subgoals g !! i

extendPath :: Path -> Rule u v -> [Path]
extendPath p r =
  [p ++ [i] | i <- take (length . subgoals . extract p $ body r) [0 ..]]
