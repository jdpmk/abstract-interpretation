--
-- Abstract syntax tree for simpl (Simple IMperative Programming Language).
--                                 ~      ~~         ~           ~
--
--   simpl is a programming language consisting of basic imperative constructs,
--   including loops, conditionals, and arithmetic and boolean expressions.
--


module Ast where

import Util

data AExp
    = ALiteral Int
    | Variable Ident
    | Add AExp AExp
    | Sub AExp AExp
    | Mult AExp AExp
    | Div AExp AExp
    | Mod AExp AExp

instance Show AExp where
    show e = case e of
        ALiteral val ->
            show val
        Variable var ->
            var
        Add e1 e2 ->
            show e1 ++ " + " ++ show e2
        Sub e1 e2 ->
            show e1 ++ " - " ++ show e2
        Mult e1 e2 ->
            show e1 ++ " * " ++ show e2
        Div e1 e2 ->
            show e1 ++ " / " ++ show e2
        Mod e1 e2 ->
            show e1 ++ " % " ++ show e2

data BExp
    = BLiteral Bool
    | Not BExp
    | Or BExp BExp
    | And BExp BExp
    | Eq AExp AExp
    | Lt AExp AExp
    | Gt AExp AExp

instance Show BExp where
    show e = case e of
        BLiteral b ->
            if b then "true" else "false"
        Not b ->
            "!(" ++ show b ++ ")"
        Or e1 e2 ->
            "(" ++ show e1 ++ " || " ++ show e2 ++ ")"
        And e1 e2 ->
            "(" ++ show e1 ++ " && " ++ show e2 ++ ")"
        Eq e1 e2 ->
            show e1 ++ " = " ++ show e2
        Lt e1 e2 ->
            show e1 ++ " < " ++ show e2
        Gt e1 e2 ->
            show e1 ++ " > " ++ show e2

data Command
    = Skip
    | Seq Command Command
    | If BExp Command Command
    | While BExp Command
    | Assign Ident AExp
    | Input Ident
    | Print AExp
    | Invariant BExp

instance Show Command where
    show c =
        aux c 0
      where
        aux c d = let ws = replicate d ' ' in case c of
            Skip ->
                ""
            Seq c1 c2 ->
                aux c1 d ++ "\n"
             ++ aux c2 d 
            If guard c1 c2 ->
                ws ++ "if " ++ show guard ++ " then\n"
             ++ aux c1 (d + width) ++ "\n"
             ++ ws ++ "else\n"
             ++ aux c2 (d + width) ++ "\n"
             ++ ws ++ "end"
            While cond body ->
                ws ++ "while " ++ show cond ++ " do\n"
             ++ aux body (d + width) ++ "\n"
             ++ ws ++ "done"
            Assign var e ->
                ws ++ var ++ " := " ++ show e ++ ";"
            Input var ->
                ws ++ var ++ " := input();"
            Print e ->
                ws ++ "print " ++ show e ++ ";"
            Invariant e ->
                ws ++ "invariant " ++ show e ++ ";"

type Program = Command
