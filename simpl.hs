--
-- Simple IMperative Programming Language
-- ~      ~~         ~           ~
-- 
-- A simple programming language consisting of basic imperative constructs,
-- including loops, conditionals, and arithmetic and boolean expressions.


import Control.Monad
import Data.Maybe


-- Utilities.

type Env a b = [(a, b)]

getEnv :: (Show a, Eq a) => Env a b -> a -> Either String b
getEnv [] k = Left $ "unknown variable: " ++ show k
getEnv ((x, v):rest) k = if x == k then Right v else getEnv rest k

putEnv :: (Eq a) => Env a b -> a -> b -> Env a b
putEnv env k v = (k, v):(filter (\(x, _) -> x /= k) env)

type IEnv a = Env Ident a


-- Abstract syntax tree.

type Ident = String

data AExp
    = ALiteral Int
    | Variable Ident
    | Add AExp AExp
    | Sub AExp AExp
    | Mult AExp AExp
    | Div AExp AExp
    | Mod AExp AExp
    deriving Show

data BExp
    = BLiteral Bool
    | Not BExp
    | Or BExp BExp
    | And BExp BExp
    | Eq AExp AExp
    | Lt AExp AExp
    | Gt AExp AExp
    deriving Show

data Command
    = Skip
    | Seq Command Command
    | If BExp Command Command
    | While BExp Command
    | Assign Ident AExp
    | Print AExp
    deriving Show

type Program = Command


-- Concrete interpreter.

type CEnv = IEnv Int

evalAExp :: AExp -> CEnv -> Either String Int
evalAExp e env = case e of
    ALiteral val ->
        Right val
    Variable var ->
        getEnv env var
    Add e1 e2 -> do
        e1' <- evalAExp e1 env
        e2' <- evalAExp e2 env
        Right $ e1' + e2'
    Sub e1 e2 -> do
        e1' <- evalAExp e1 env
        e2' <- evalAExp e2 env
        Right $ e1' - e2'
    Mult e1 e2 -> do
        e1' <- evalAExp e1 env
        e2' <- evalAExp e2 env
        Right $ e1' * e2'
    Div e1 e2 -> do
        e1' <- evalAExp e1 env
        e2' <- evalAExp e2 env
        Right $ div e1' e2'
    Mod e1 e2 -> do
        e1' <- evalAExp e1 env
        e2' <- evalAExp e2 env
        Right $ mod e1' e2'

evalBExp :: BExp -> CEnv -> Either String Bool
evalBExp e env = case e of
    BLiteral b ->
        Right b
    Not b -> do
        b' <- evalBExp b env
        Right $ not b'
    Or b1 b2 -> do
        b1' <- evalBExp b1 env
        if b1' then Right True else evalBExp b2 env
    And b1 b2 -> do
        b1' <- evalBExp b1 env
        if b1' then evalBExp b2 env else Right False
    Eq a1 a2 -> do
        a1' <- evalAExp a1 env
        a2' <- evalAExp a2 env
        Right $ a1' == a2'
    Lt a1 a2 -> do
        a1' <- evalAExp a1 env
        a2' <- evalAExp a2 env
        Right $ a1' < a2'
    Gt a1 a2 -> do
        a1' <- evalAExp a1 env
        a2' <- evalAExp a2 env
        Right $ a1' > a2'

-- TODO: Find a better way to handle IO (Either ...).
evalCommand :: Command -> CEnv -> IO (Either String CEnv)
evalCommand c env = case c of
    Skip ->
        return $ Right env
    Seq c1 c2 -> do
        err_env' <- evalCommand c1 env
        case err_env' of
            Right env' -> evalCommand c2 env'
            left -> return left
    If guard c1 c2 ->
        case evalBExp guard env of
            Right guard' ->
                if guard' then evalCommand c1 env else evalCommand c2 env
            Left error ->
                return $ Left error
    While cond body ->
        case evalBExp cond env of
            Right cond' ->
                if cond' then do
                    err_env' <- evalCommand body env
                    case err_env' of
                        Right env' -> evalCommand c env'
                        left -> return left
                else return $ Right env
            Left error -> return $ Left error
    Assign var e ->
        return $ do
            e' <- evalAExp e env
            Right $ putEnv env var e'
    Print e ->
        case evalAExp e env of
            Right e' -> do
                putStrLn $ show e'
                return $ Right env
            Left error ->
                return $ Left error

evalProgram :: Program -> IO (Maybe String)
evalProgram p = do
    env' <- evalCommand p []
    return $ case env' of
        Left error -> Just error
        Right _    -> Nothing


-- Abstract domains.

--
-- Typeclass representing a partial order.
--
-- We use le, eq, and ge to avoid ambiguity with functions such as (<=) from
-- the Data.Ord typeclass.
--
-- See:
-- * https://en.wikipedia.org/wiki/Partially_ordered_set
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
class PartialOrd a => Lattice a where
    -- Join, or least upper bound.
    join :: a -> a -> a
    -- Meet, or greatest lower bound.
    meet :: a -> a -> a

--
-- Abstract domain of signs.
--
--  .----- Top -----.
--  |       |       |
-- Neg    Zero     Pos
--  |       |       |
--  '----- Bot -----'
--
data Sign = STop | SPos | SZero | SNeg | SBot deriving Show

instance PartialOrd Sign
  where
    le x y = case (x, y) of
        (_, STop) -> True
        (SBot, _) -> True
        (SPos, SPos) -> True
        (SZero, SZero) -> True
        (SNeg, SNeg) -> True
        (_, _)    -> False

-- TODO: Can we enforce commutativity within the typeclass?
instance Lattice Sign
  where
    join x y = case (x, y) of
        (x, y) | eq x y -> x
        (_, STop)       -> STop
        (STop, _)       -> STop
        (SBot, x)       -> x
        (x, SBot)       -> x
        (_, _)          -> STop

    meet x y = case (x, y) of
        (x, y) | eq x y -> x
        (x, STop)       -> x
        (STop, x)       -> x
        (SBot, _)       -> SBot
        (_, SBot)       -> SBot
        (_, _)          -> SBot


class Lattice a => AbstractDomain a where
    aEvalAExp :: (Lattice a) => AExp -> IEnv a -> Either String a
    aEvalCommand :: (Lattice a) => Command -> IEnv a -> Either String (IEnv a)

instance AbstractDomain Sign where
    aEvalAExp e env = case e of
        ALiteral val ->
            Right $ if val < 0 then SNeg
                    else if val == 0 then SZero
                    else SPos
        Variable var ->
            getEnv env var
        Add e1 e2 -> do
            a1 <- aEvalAExp e1 env
            a2 <- aEvalAExp e2 env
            Right $ case (a1, a2) of
                (SBot, _)    -> SBot
                (_, SBot)    -> SBot
                (SZero, x)   -> x
                (x, SZero)   -> x
                (SPos, SPos) -> SPos
                (_, _)       -> STop
        Sub e1 e2 -> do
            a1 <- aEvalAExp e1 env
            a2 <- aEvalAExp e2 env
            Right $ case (a1, a2) of
                (SBot, _)  -> SBot
                (_, SBot)  -> SBot
                (SZero, SPos) -> SNeg
                (SZero, SNeg) -> SPos
                (x, SZero) -> x
                (SNeg, SPos) -> SNeg
                (SPos, SNeg) -> SPos
                (_, _) -> STop
        Mult e1 e2 -> do
            a1 <- aEvalAExp e1 env
            a2 <- aEvalAExp e2 env
            Right $ case (a1, a2) of
                (SBot, _)    -> SBot
                (_, SBot)    -> SBot
                (SZero, _)   -> SZero
                (_, SZero)   -> SZero
                (SPos, SPos) -> SPos
                (SNeg, SNeg) -> SPos
                (SPos, SNeg) -> SNeg
                (SNeg, SPos) -> SNeg
                (_, _)       -> STop
        Div e1 e2 -> do
            a1 <- aEvalAExp e1 env
            a2 <- aEvalAExp e2 env
            Right $ case (a1, a2) of
                (SBot, _)    -> SBot
                (_, SBot)    -> SBot
                (SZero, _)   -> SZero
                (_, SZero)   -> SBot  -- Division by zero!
                (SPos, SPos) -> SPos
                (SNeg, SNeg) -> SPos
                (SPos, SNeg) -> SNeg
                (SNeg, SPos) -> SNeg
                (_, _)       -> STop
        Mod e1 e2 -> do
            a1 <- aEvalAExp e1 env
            a2 <- aEvalAExp e2 env
            Right $ case (a1, a2) of
                (SBot, _)    -> SBot
                (_, SBot)    -> SBot
                (SZero, _)   -> SZero
                (_, SZero)   -> SBot  -- Division by zero!
                (SPos, SPos) -> SPos
                (SNeg, SNeg) -> SPos
                (SPos, SNeg) -> SNeg  -- TODO: Revisit these semantics.
                (SNeg, SPos) -> SNeg  -- TODO: Revisit these semantics.
                (_, _)       -> STop

    aEvalCommand c env = case c of
        Skip ->
            Right env
        Seq c1 c2 -> do
            env'  <- aEvalCommand c1 env
            env'' <- aEvalCommand c2 env'
            Right env''
        If _ c1 c2 -> do
            env1'  <- aEvalCommand c1 env
            env2'  <- aEvalCommand c1 env
            Right $ joinEnv env1' env2'
        While _ _ ->
            undefined
        Assign var e -> do
            a <- aEvalAExp e env
            Right $ putEnv env var a
        Print _ ->
            Right env
      where
        joinEnv :: (Lattice a) => IEnv a -> IEnv a -> IEnv a
        joinEnv env1 env2 = foldr (joinMapping env1) [] env2

        joinMapping :: (Lattice a) => IEnv a -> (Ident, a) -> IEnv a -> IEnv a
        joinMapping env1 (var, aval) acc =
            let joined = case getEnv env1 var of
                              Left _ -> aval
                              Right aval1 -> Main.join aval1 aval
            in (var, joined):acc

signEvalProgram :: Program -> IO (Maybe (IEnv Sign))
signEvalProgram p = do
    let env' = aEvalCommand p ([] :: IEnv Sign)
    return $ case env' of
        Left _    -> Nothing
        Right env -> Just env

main :: IO ()
main = do
    let commands = [ Assign "x" (ALiteral 0)
                   , If (Lt (Variable "x") (ALiteral 0))
                        (Assign "x" (Mult (Variable "x") (ALiteral (-1))))
                        (Skip)
                   ]
    let p = foldr (Seq) Skip commands
    env <- signEvalProgram p
    when (isJust env) $ putStrLn $ show $ fromJust env

main2 :: IO ()
main2 = do
    -- Hypothetical syntax:
    --
    -- x := 42;
    -- while !(x = 1) do
    --     print x;
    --     if x % 2 = 0 then
    --         x := x / 2;
    --     else
    --         x := 3 * x + 1;
    -- end
    -- print x;
    let commands = 
         [ Assign "x" (ALiteral 42)
         , While (Not (Eq (Variable "x") (ALiteral 1)))
                 (Seq (Print (Variable "x"))
                      (If (Eq (Mod (Variable "x") (ALiteral 2)) (ALiteral 0))
                          (Assign "x" (Div (Variable "x") (ALiteral 2)))
                          (Assign "x" (Add (Mult (ALiteral 3) (Variable "x"))
                                             (ALiteral 1)))))
         , Print (Variable "x")
         ]
    let p = foldr (Seq) Skip commands
    -- Output:
    -- 42
    -- 21
    -- 64
    -- 32
    -- 16
    -- 8
    -- 4
    -- 2
    -- 1
    error <- evalProgram p
    when (isJust error) $ putStrLn (fromJust error)
