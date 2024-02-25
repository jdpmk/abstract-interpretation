--
-- Abstract domains.
--


module Domain where

import qualified Data.List as List

import Ast
import Util

--
-- Typeclass representing a partial order.
--
-- We use le, eq, and ge to avoid ambiguity with functions such as (<=) from
-- the Data.Ord typeclass.
--
-- See:
-- * https://en.wikipedia.org/wiki/Partially_ordered_set
--
class PartialOrd a where
    -- Less-than-or-equal-to relation.
    le :: a -> a -> Bool
    -- Equal-to relation.
    eq :: a -> a -> Bool
    eq x y = le x y && le y x
    -- Greater-than-or-equal-to relation.
    ge :: a -> a -> Bool
    ge x y = not (le x y) || eq x y

--
-- Typeclass representing a lattice.
--
-- See:
-- * https://en.wikipedia.org/wiki/Lattice_(order)
--
class PartialOrd a => Lattice a where
    -- Join, or least upper bound.
    join :: a -> a -> a
    -- Meet, or greatest lower bound.
    meet :: a -> a -> a

--
-- Typeclass representing an abstract domain. The functions below must be
-- implemented for abstract interpretation over a given lattice.
--
class (Eq a, Lattice a) => AbstractDomain a where
    aEvalAExp :: Lattice a => AExp -> IEnv a -> AbstractValueOrErr a
    aEvalBExp :: Lattice a => BExp -> IEnv a -> Bool -> IEnvOrErr a
    aEvalCommand :: (Show a, Lattice a) => Command -> State a -> StateOrErr a

--
-- State of the abstract interpreter at a given command.
--
-- Encapsulates the abstract environment, output to be logged at this step
-- of execution, and the indentation level to be used when logging.
--
data State a = State
    { env    :: IEnv a
    , output :: String
    , indent :: Int
    }

initialState :: (AbstractDomain a) => State a
initialState = State { env    = []
                        , output = ""
                        , indent = 0
                        }

--
-- Some useful type aliases.
--
type AbstractValueOrErr a = Either String a
type IEnvOrErr a = Either String (IEnv a)
type StateOrErr a = Either String (State a)

--
-- Helpers for environments of lattice elements.
--

--
-- Given two abstract environments of lattice elements:
-- * when identifier x is in both environments    => f env1[x] env2[x]
-- * otherwise, when x is in just one environment => env[x]
--
mergeEnv :: Lattice a => (a -> a -> a) -> IEnv a -> IEnv a -> IEnv a
mergeEnv f env1 env2 = foldr (mergeMapping f env1) [] env2
  where
    mergeMapping :: Lattice a
                 => (a -> a -> a)
                 -> IEnv a
                 -> (Ident, a)
                 -> IEnv a
                 -> IEnv a
    mergeMapping f env1 (var, aval2) acc =
        let joined = case getEnv env1 var of
                         Left _ -> aval2
                         Right aval1 -> f aval1 aval2
        in (var, joined):acc

joinEnv :: Lattice a => IEnv a -> IEnv a -> IEnv a
joinEnv = mergeEnv join

meetEnv :: Lattice a => IEnv a -> IEnv a -> IEnv a
meetEnv = mergeEnv meet

-- TODO: Maybe this can be more efficient but it's concise and intuitive.
equalEnv :: (Eq a, Lattice a) => IEnv a -> IEnv a -> Bool
equalEnv env1 env2 = contains env1 env2 && contains env2 env1
  where
    contains a b = List.intersect a b == a
