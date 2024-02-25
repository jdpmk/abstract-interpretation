--
-- Main entry point.
--


module Main where

import qualified Control.Monad as Monad
import qualified Data.Maybe as Maybe

import Ast
import Concrete
import Domain
import Sign

abstractMain :: IO ()
abstractMain = do
    --
    -- x := y;  | ERROR: unknown "y"
    --
    evaluate [ Assign "x" (Variable "y")
             ]

    --
    -- x := 1;  | x -> SP
    --
    evaluate [ Assign "x" (ALiteral 1)
             ]

    --
    -- x := -1;  | x -> SN
    -- y := 1;   | x -> SN ; y -> SP
    -- x := y;   | x -> SP ; y -> SP
    --
    evaluate [ Assign "x" (ALiteral (-1))
             , Assign "y" (ALiteral (1))
             , Assign "x" (Variable "y")
             ]

    --
    -- x := input()    | x -> ST
    -- if x >= 0 then  | x -> SZP
    --     skip;       | x -> SZP
    -- else            | x -> SN
    --     x := 1;     | x -> SP
    -- end             | x -> SZP
    --
    evaluate [ Input "x"
             , If (Or (Gt (Variable "x") (ALiteral 0))
                      (Eq (Variable "x") (ALiteral 0)))
                  (Skip)
                  (Assign "x" (ALiteral 1))
             ]

    --
    -- x := input()      | x -> ST
    -- if x < 0 then     | x -> SN
    --     x := x * -1;  | x -> SP
    -- else              | x -> SZP
    --     x := x + 1;   | x -> SP
    -- end               | x -> SP
    --
    evaluate [ Input "x"
             , If (Lt (Variable "x") (ALiteral 0))
                  (Assign "x" (Mult (Variable "x") (ALiteral (-1))))
                  (Assign "x" (Add (Variable "x") (ALiteral 1)))
             ]

    --
    -- Example program, where we verify that a division-by-0 will not occur.
    -- The outputs for analyzing the programs below can be found in the README
    -- example.
    --
    evaluate [ Input "x"
             , If (Gt (Variable "x") (ALiteral 0))
                  (Assign "x" (Mult (Variable "x") (ALiteral (-2))))
                  (If (Lt (Variable "x") (ALiteral 0))
                      (Assign
                              "x" (Mult (Variable "x") (ALiteral (-5))))
                      (Assign
                              "x" (Add (Variable "x") (ALiteral 1))))
             , Invariant (Not (Eq (Variable "x") (ALiteral 0)))
             , Assign "y" (Div (ALiteral 1) (Variable "x"))
             ]

    --
    -- Example program, equivalent to the above, where the Sign domain is not
    -- precise enough to determine that a division-by-0 will certainly not
    -- occur.
    --
    evaluate [ Input "x"
             , If (Gt (Variable "x") (ALiteral 0))
                  (Seq (Assign
                               "a" (Mult (Variable "x") (ALiteral 3)))
                       (Assign
                               "x" (Sub (Variable "x") (Variable "a"))))
                  (If (Lt (Variable "x") (ALiteral 0))
                      (Seq (Assign
                                   "b" (Mult (Variable "x") (ALiteral 6)))
                           (Assign
                                   "x" (Sub (Variable "x") (Variable "b"))))
                      (Assign "x" (ALiteral 1)))
             , Invariant (Not (Eq (Variable "x") (ALiteral 0)))
             , Assign "y" (Div (ALiteral 1) (Variable "x"))
             ]

    --
    -- x := input()      | x -> ST            | one more iteration for
    -- i := 0            | x -> ST ; i -> SZ  | fixed-point convergence
    -- while (i < x) do  | x -> ST ; i -> SZ  | x -> ST ; i -> SP
    --     print x;      | x -> ST ; i -> SZ  | x -> ST ; i -> SP
    --     i := i + 1;   | x -> ST ; i -> SP  | x -> ST ; i -> SP
    -- done              | x -> ST ; i -> SZP |
    --
    evaluate [ Input "x"
             , Assign "i" (ALiteral 0)
             , While (Lt (Variable "i") (Variable "x"))
                     (Seq (Print (Variable "x"))
                          (Assign "i" (Add (Variable "i") (ALiteral 1))))
             ]

    --
    -- x := 5           | x -> SP
    -- while x > 0 do   | x -> SP
    --     x := x - 1;  | x -> ST
    -- done             | x -> ST
    --
    evaluate [ Assign "x" (ALiteral 5)
             , While (Gt (Variable "x") (ALiteral 0))
                     (Assign "x" (Sub (Variable "x") (ALiteral 1)))
             ]

    --
    -- x := input()      | x -> ST
    -- if !(x = 1) then  | x -> ST
    --     x := x        | x -> ST
    -- else              | x -> SP
    --     skip          | x -> SP
    -- end               | x -> ST
    --
    evaluate [ Input "x"
             , If (Not (Eq (Variable "x") (ALiteral 1)))
                  (Assign "x" (Variable "x"))
                  (Skip)
             ]
  where
    evaluate commands = do
        let p = foldr Seq Skip commands
        putStrLn "Program:"
        putStrLn $ show p

        putStrLn "Abstract interpretation:"
        case signEvalProgram p of
            Right s ->
                putStrLn $ output s
            Left error -> do
                putStrLn error
        putStrLn $ "\n" ++ replicate 70 '#' ++ "\n"

concreteMain :: IO ()
concreteMain = do
    --
    -- x := input();
    -- while !(x = 1) do
    --     print x;
    --     if x % 2 = 0 then
    --         x := x / 2;
    --     else
    --         x := 3 * x + 1;
    --     end
    -- end
    -- print x;
    --
    let commands =
         [ Input "x"
         , While (Not (Eq (Variable "x") (ALiteral 1)))
                 (Seq (Print (Variable "x"))
                      (If (Eq (Mod (Variable "x") (ALiteral 2))
                                       (ALiteral 0))
                          (Assign
                                  "x" (Div (Variable "x") (ALiteral 2)))
                          (Assign
                                  "x" (Add (Mult (ALiteral 3) (Variable "x"))
                                           (ALiteral 1)))))
         , Print (Variable "x")
         ]
    let p = foldr Seq Skip commands
    -- Input:
    -- 42
    --
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
    Monad.when (Maybe.isJust error) $ putStrLn (Maybe.fromJust error)

main :: IO ()
main = abstractMain
