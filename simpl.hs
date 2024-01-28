--
-- Simple IMperative Programming Language
-- ~      ~~         ~           ~
-- 
-- A simple programming language consisting of basic imperative constructs,
-- including loops, conditionals, and arithmetic and boolean expressions.


import Control.Monad
import Data.Maybe


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

type Env = [(Ident, Int)]

getEnv :: Env -> Ident -> Either String Int
getEnv [] var = Left $ "unknown variable: " ++ var
getEnv ((x,v):rest) var = if x == var then Right v else getEnv rest var

putEnv :: Env -> Ident -> Int -> Env
putEnv env var val = (var,val):env

evalAExp :: AExp -> Env -> Either String Int
evalAExp exp env = case exp of
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

evalBExp :: BExp -> Env -> Either String Bool
evalBExp exp env = case exp of
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
evalCommand :: Command -> Env -> IO (Either String Env)
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

main :: IO ()
main = do
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
