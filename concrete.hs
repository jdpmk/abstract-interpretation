--
-- Concrete interpreter.
--


module Concrete where

import Ast
import Util

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
    Input var -> do
        input <- getLine
        let input_as_int = read input :: Int
        return $ Right $ putEnv env var input_as_int
    Print e ->
        case evalAExp e env of
            Right e' -> do
                putStrLn $ show e'
                return $ Right env
            Left error ->
                return $ Left error
    Invariant _ ->
        return $ Right env

evalProgram :: Program -> IO (Maybe String)
evalProgram p = do
    env' <- evalCommand p []
    return $ case env' of
        Left error -> Just error
        Right _    -> Nothing
