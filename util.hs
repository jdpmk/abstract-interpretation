--
-- Utilities.
--


module Util where

import qualified Data.List as List

-- An environment mapping keys to values, implemented as an associative array.
type Env a b = [(a, b)]

getEnv :: (Show a, Eq a) => Env a b -> a -> Either String b
getEnv [] k = Left $ "unknown " ++ show k
getEnv ((x, v):rest) k = if x == k then Right v else getEnv rest k

putEnv :: Eq a => Env a b -> a -> b -> Env a b
putEnv env k v = (k, v):(filter (\(x, _) -> x /= k) env)

showEnv :: (Show a, Show b) => Env a b -> String
showEnv env =
    "{ " ++ (List.intercalate " ; " $ map mapping env) ++ " }"
  where
    mapping (var, a) = show var ++ " -> " ++ show a

-- A wrapper around an environment keyed on identifiers, the primary use case
-- for environments in this program.
type Ident = String
type IEnv a = Env Ident a

-- Indentation width
width :: Int
width = 4
