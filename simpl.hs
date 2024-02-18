--
-- Abstract interpretation for simpl (Simple IMperative Programming Language)
--                                    ~      ~~         ~           ~
-- 
-- simpl is a programming language consisting of basic imperative constructs,
-- including loops, conditionals, and arithmetic and boolean expressions.
--


import qualified Control.Monad as Monad
import qualified Data.Either as Either
import qualified Data.List as List
import qualified Data.Maybe as Maybe


-- Utilities.

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

width :: Int
width = 4


-- Abstract syntax tree.

data Info = Info
    { label :: Int
    } deriving Show

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
    = Skip Info
    | Seq Command Command
    | If Info BExp Command Command
    | While Info BExp Command
    | Assign Info Ident AExp
    | Input Info Ident
    | Print Info AExp
    | Invariant Info BExp

instance Show Command where
    show c =
        aux c 0
      where
        aux c d = let ws = replicate d ' ' in case c of
            Skip _ ->
                ""
            Seq c1 c2 ->
                aux c1 d ++ "\n"
             ++ aux c2 d 
            If _ guard c1 c2 ->
                ws ++ "if " ++ show guard ++ " then\n"
             ++ aux c1 (d + width) ++ "\n"
             ++ ws ++ "else\n"
             ++ aux c2 (d + width) ++ "\n"
             ++ ws ++ "end"
            While _ _ _ ->
                undefined
            Assign _ var e ->
                ws ++ var ++ " := " ++ show e ++ ";"
            Input _ var ->
                ws ++ var ++ " := input();"
            Print _ e ->
                ws ++ "print " ++ show e ++ ";"
            Invariant _ e ->
                ws ++ "invariant " ++ show e ++ ";"

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
    Skip _ ->
        return $ Right env
    Seq c1 c2 -> do
        err_env' <- evalCommand c1 env
        case err_env' of
            Right env' -> evalCommand c2 env'
            left -> return left
    If _ guard c1 c2 ->
        case evalBExp guard env of
            Right guard' ->
                if guard' then evalCommand c1 env else evalCommand c2 env
            Left error ->
                return $ Left error
    While _ cond body ->
        case evalBExp cond env of
            Right cond' ->
                if cond' then do
                    err_env' <- evalCommand body env
                    case err_env' of
                        Right env' -> evalCommand c env'
                        left -> return left
                else return $ Right env
            Left error -> return $ Left error
    Assign _ var e ->
        return $ do
            e' <- evalAExp e env
            Right $ putEnv env var e'
    Input _ var -> do
        input <- getLine
        let input_as_int = read input :: Int
        return $ Right $ putEnv env var input_as_int
    Print _ e ->
        case evalAExp e env of
            Right e' -> do
                putStrLn $ show e'
                return $ Right env
            Left error ->
                return $ Left error
    Invariant _ _ ->
        return $ Right env

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
-- Abstract domain of signs.
--
-- The domain of signs is simple: we map variables (numbers) to a value
-- indicating their sign. We also have compound states to indicate the possible
-- presence of multiple signs, such as SZP for zero or positive.
--
-- A useful application of this abstract domain is proving the absence of a
-- division-by-0.
--
data Sign = ST | SZP | SNP | SNZ | SP | SZ | SN | SB deriving Show

instance PartialOrd Sign where
    le x y = case (x, y) of
        -- ST is at least as precise as anything else
        (_, ST)    -> True
        -- Anything else is at least as precise as SB
        (SB, _)    -> True

        -- le x x
        (SZP, SZP) -> True
        (SNP, SNP) -> True
        (SNZ, SNZ) -> True
        (SP, SP)   -> True
        (SZ, SZ)   -> True
        (SN, SN)   -> True

        -- States which SZP is at least as precise
        (SP, SZP) -> True
        (SZ, SZP) -> True

        -- States which SNP is at least as precise
        (SP, SNP) -> True
        (SN, SNP) -> True

        -- States which SNZ is at least as precise
        (SZ, SNZ) -> True
        (SN, SNZ) -> True

        -- Incomparable states, e.g. SN, SZ
        (_, _)     -> False

-- TODO: Can we enforce commutativity within the typeclass?
instance Lattice Sign where
    join x y = case (x, y) of
        (x, y) | eq x y -> x

        (_, ST) -> ST
        (ST, _) -> ST
        (SB, x) -> x
        (x, SB) -> x

        (SZ, SP) -> SZP
        (SP, SZ) -> SZP

        (SN, SP) -> SNP
        (SP, SN) -> SNP

        (SN, SZ) -> SNZ
        (SZ, SN) -> SNZ

        (SZP, SZ) -> SZP
        (SZP, SP) -> SZP
        (SZ, SZP) -> SZP
        (SP, SZP) -> SZP

        (SNP, SN) -> SNP
        (SNP, SP) -> SNP
        (SN, SNP) -> SNP
        (SP, SNP) -> SNP

        (SNZ, SN) -> SNZ
        (SNZ, SZ) -> SNZ
        (SN, SNZ) -> SNZ
        (SZ, SNZ) -> SNZ

        (_, _) -> ST

    meet x y = case (x, y) of
        (x, y) | eq x y -> x

        (x, ST) -> x
        (ST, x) -> x
        (SB, _) -> SB
        (_, SB) -> SB

        (SZP, SNP) -> SP
        (SNP, SZP) -> SP

        (SZP, SNZ) -> SZ
        (SNZ, SZP) -> SZ

        (SNP, SNZ) -> SN
        (SNZ, SNP) -> SN

        (SZP, SZ) -> SZ
        (SZP, SP) -> SP
        (SZ, SZP) -> SZ
        (SP, SZP) -> SP

        (SNP, SN) -> SN
        (SNP, SP) -> SP
        (SN, SNP) -> SN
        (SP, SNP) -> SP

        (SNZ, SN) -> SN
        (SNZ, SZ) -> SZ
        (SN, SNZ) -> SN
        (SZ, SNZ) -> SZ

        (_, _) -> SB


-- Abstract interpreter.

data State a = State
    { env     :: IEnv a
    , output  :: String
    , indent  :: Int
    }

type StateOrErr a = Either String (State a)
type IEnvOrErr a = Either String (IEnv a)

class Lattice a => AbstractDomain a where
    -- TODO: AbstractValueOrErr
    aEvalAExp :: Lattice a => AExp -> IEnv a -> Either String a
    aEvalBExp :: Lattice a => BExp -> IEnv a -> Bool -> IEnvOrErr a
    aEvalCommand :: (Show a, Lattice a) => Command -> State a -> StateOrErr a

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

instance AbstractDomain Sign where
    aEvalAExp e env = case e of
        -- Evaluation of a literal is simple: from its value, we can easily
        -- deduce whether the literal is negative, zero, or positive.
        ALiteral val ->
            Right $ if val < 0 then SN
                    else if val == 0 then SZ
                    else SP
        -- We look up variables in the current abstract environment.
        Variable var ->
            getEnv env var
        -- For binary arithmetic operations, we can deduce the sign of the
        -- result in many cases. For instance, we know that:
        -- * the addition of any two positive numbers is always positive
        -- * the subtraction of a positive number from a negative number is
        --   always negative
        -- * the addition of a non-negative number and a positive number is
        --   always positive,
        -- and so on. Zero is also a nice "identity" in many cases.
        Add e1 e2 -> do
            a1 <- aEvalAExp e1 env
            a2 <- aEvalAExp e2 env
            Right $ case (a1, a2) of
                (SB, _) -> SB
                (_, SB) -> SB

                (SZ, x) -> x
                (x, SZ) -> x

                (SZP, SZP) -> SZP
                (SZP, SP)  -> SP
                (SP, SZP)  -> SP
                (SP, SP)   -> SP

                (SNZ, SNZ) -> SNZ
                (SNZ, SN)  -> SN
                (SN, SNZ)  -> SN
                (SN, SN)   -> SN

                (_, _) -> ST
        Sub e1 e2 -> do
            a1 <- aEvalAExp e1 env
            a2 <- aEvalAExp e2 env
            Right $ case (a1, a2) of
                (SB, _) -> SB
                (_, SB) -> SB

                (x, SZ) -> x

                (SZ, SP)  -> SN
                (SZ, SN)  -> SP
                (SZ, SZP) -> SNZ
                (SZ, SNZ) -> SZP
                (SZ, SNP) -> SNP

                (_, _) -> ST
        Mult e1 e2 -> do
            a1 <- aEvalAExp e1 env
            a2 <- aEvalAExp e2 env
            Right $ case (a1, a2) of
                (SB, _) -> SB
                (_, SB) -> SB

                (SZ, _) -> SZ
                (_, SZ) -> SZ

                (SP, SP) -> SP
                (SN, SN) -> SP
                (SP, SN) -> SN
                (SN, SP) -> SN

                (SZP, SZP) -> SZP
                (SZP, SNZ) -> SNZ
                (SNZ, SZP) -> SNZ

                (SP, SNP) -> SNP
                (SNP, SP) -> SNP
                (SN, SNP) -> SNP
                (SNP, SN) -> SNP
                (SNP, SNP) -> SNP

                (_, _) -> ST
        Div e1 e2 -> do
            a1 <- aEvalAExp e1 env
            a2 <- aEvalAExp e2 env
            Right $ case (a1, a2) of
                (SB, _) -> SB
                (_, SB) -> SB

                -- Possible division by zero.
                -- "le SZ x" means "any state which may be zero".
                (_, x) | le SZ x -> SB

                (SZ, _) -> SZ

                (x, SP) -> x

                (SP, SN)  -> SN
                (SN, SN)  -> SP
                (SZP, SN) -> SNZ
                (SNP, SN) -> SNP
                (SNZ, SN) -> SZP

                (SP, SNP) -> SNP
                (SN, SNP) -> SNP
                (SNP, SNP) -> SNP

                (_, _) -> ST
        Mod e1 e2 -> do
            a1 <- aEvalAExp e1 env
            a2 <- aEvalAExp e2 env
            Right $ case (a1, a2) of
                (SB, _) -> SB
                (_, SB) -> SB

                -- Possible division by zero.
                -- "le SZ x" means "any state which may be zero".
                (_, x) | le SZ x -> SB

                (SZ, _) -> SZ

                (x, SP) -> x

                -- TODO: Revisit these semantics.
                (SP, SN) -> SN
                (SN, SN) -> SP
                (SZP, SN) -> SNZ
                (SNP, SN) -> SNP
                (SNZ, SN) -> SZP

                (_, _) -> ST

    aEvalBExp e env flipped = case e of
        BLiteral b ->
            Right env
        Not e ->
            aEvalBExp e env (not flipped)
        Or e1 e2 -> do
            env1 <- aEvalBExp e1 env flipped
            env2 <- aEvalBExp e2 env flipped
            Right $ (if flipped then meetEnv else joinEnv) env1 env2
        And e1 e2 -> do
            env1 <- aEvalBExp e1 env flipped
            env2 <- aEvalBExp e2 env flipped
            Right $ (if flipped then joinEnv else meetEnv) env1 env2
        -- TODO: Assumption for the comparisons below is that variables are
        -- always on the LHS of the operator.
        Eq e1 e2 -> do
            a1 <- aEvalAExp e1 env
            a2 <- aEvalAExp e2 env
            Right $ case e1 of
                Variable var -> putEnv env var (deduceEqual a2 flipped)
                _            -> env
        Lt e1 e2 ->
            if flipped then
                let neg_exp = Or (Gt e1 e2) (Eq e1 e2)
                in aEvalBExp neg_exp env (not flipped)
            else do
                a1 <- aEvalAExp e1 env
                a2 <- aEvalAExp e2 env
                Right $ case e1 of
                    Variable var -> putEnv env var (deduceLess a2)
                    _            -> env
        Gt e1 e2 ->
            if flipped then
                let neg_exp = Or (Lt e1 e2) (Eq e1 e2)
                in aEvalBExp neg_exp env (not flipped)
            else do
                a1 <- aEvalAExp e1 env
                a2 <- aEvalAExp e2 env
                Right $ case e1 of
                    Variable var -> putEnv env var (deduceGreater a2)
                    _            -> env
      where
        deduceLess :: Sign -> Sign
        deduceLess a = case a of
            SZ  -> SN
            SP  -> ST
            SZP -> ST
            SNZ -> SN
            _   -> a
        deduceGreater :: Sign -> Sign
        deduceGreater a = case a of
            SZ  -> SP
            SN  -> ST
            SNZ -> ST
            SZP -> SP
            _   -> a
        deduceEqual :: Sign -> Bool -> Sign
        deduceEqual a flipped =
            if not flipped then a
            else case a of
                ST -> SB  -- TODO
                SZP -> SN
                SNP -> SZ
                SNZ -> SP
                SP -> SNZ
                SZ -> SNP
                SN -> SZP
                SB -> SB  -- TODO

    aEvalCommand c s = case c of
        Skip i ->
            -- Special case: 
            Right $ s { output = "" }
        Seq c1 c2 -> do
            s1 <- aEvalCommand c1 s
            s2 <- aEvalCommand c2 s1
            Right $ s2 { output = (output s1)
                               ++ (output s2) }
        If _ guard c1 c2 -> do
            let env0 = env s
            env_when_sat   <- aEvalBExp guard env0 False
            env_when_unsat <- aEvalBExp (Not guard) env0 False
            let env_then = meetEnv env0 env_when_sat
            let env_else = meetEnv env0 env_when_unsat

            let si = s { indent = width + indent s }
            st <- aEvalCommand c1 $ si { env = env_then }
            se <- aEvalCommand c2 $ si { env = env_else }

            let env_if = joinEnv (env st) (env se)
            let ws = replicate (indent s) ' '
            let nws = replicate (width + indent s) ' '

            Right $ s { env = env_if
                      , output = ws ++ "if " ++ show guard ++ " then\n"
                              ++ nws ++ showEnv env_then ++ "\n"
                              ++ output st
                              ++ ws ++ "else\n"
                              ++ nws ++ showEnv env_else ++ "\n"
                              ++ output se
                              ++ ws ++ "end\n"
                              ++ ws ++ showEnv env_if ++ "\n"
                      }
        While _ _ _ ->
            undefined
        Assign _ var e -> do
            let env0 = env s
            a <- aEvalAExp e env0
            Right $ log c s { env = putEnv env0 var a }
        Print _ _ ->
            Right $ s
        Input _ var ->
            let env0 = env s in
            Right $ log c s { env = putEnv env0 var ST }
        Invariant i e -> do
            let env0 = env s
            env_when_sat <- aEvalBExp e env0 False
            let env_inv = meetEnv env0 env_when_sat
            let mismatches = collectMismatches env0 env_inv
            if null mismatches then
                Right $ log c s { env = env_inv }
            else
                let instances = unlines (map reportMismatch mismatches) in
                let error = "\n" ++ show c ++ "\n"
                         ++ "ERROR: unsatisfied invariant:\n"
                         ++ instances ++ "\n"
                in Right $ s { output = error }
          where
            reportMismatch (var, inv_aval, env_aval) =
                "requires: " ++ show var ++ " -> " ++ show inv_aval ++ "\n"
             ++ "found:    " ++ show var ++ " -> " ++ show env_aval
            mappingsFrom env (var, inv_aval) acc =
                let env_aval = case getEnv env var of
                                  Left _ -> inv_aval
                                  Right env_aval -> env_aval
                in if le env_aval inv_aval then acc
                   else (var, inv_aval, env_aval):acc
            collectMismatches env env_inv = foldr (mappingsFrom env) [] env_inv
      where
        log :: Command -> State Sign -> State Sign
        log c s =
            let ws = replicate (indent s) ' ' in
            s { output = ws ++ show c ++ "\n"
                      ++ ws ++ showEnv (env s) ++ "\n" }

initialState :: (AbstractDomain a) => State a
initialState = State { env     = []
                     , output  = ""
                     , indent  = 0
                     }

signEvalProgram :: Program -> StateOrErr Sign
signEvalProgram p = aEvalCommand p initialState

abstractMain :: IO ()
abstractMain = do
    --
    -- x := y;   | ERROR: unknown "y"
    --
    evaluate [ Assign (Info 1) "x" (Variable "y")
             ]

    --
    -- x := 1;   | x -> SP
    --
    evaluate [ Assign (Info 1) "x" (ALiteral 1)
             ]

    --
    -- x := -1;  | x -> SN
    -- y := 1;   | x -> SN ; y -> SP
    -- x := y;   | x -> SP ; y -> SP
    --
    evaluate [ Assign (Info 1) "x" (ALiteral (-1))
             , Assign (Info 2) "y" (ALiteral (1))
             , Assign (Info 3) "x" (Variable "y")
             ]

    --
    -- x := input()      | x -> ST
    -- if x >= 0 then    | x -> SZP
    --     skip;         | x -> SZP
    -- else              | x -> SN
    --     x := 1;       | x -> SP
    -- end               | x -> SZP
    --
    evaluate [ Input (Info 1) "x"
             , If (Info 2) (Or (Gt (Variable "x") (ALiteral 0))
                               (Eq (Variable "x") (ALiteral 0)))
                  (Skip (Info 3))
                  (Assign (Info 4) "x" (ALiteral 1))
             ]

    --
    -- x := input()      | x -> ST
    -- if x < 0 then     | x -> SN
    --     x := x * -1;  | x -> SP
    -- else              | x -> SZP
    --     x := x + 1;   | x -> SP
    -- end               | x -> SP
    --
    evaluate [ Input (Info 1) "x"
             , If (Info 2) (Lt (Variable "x") (ALiteral 0))
                  (Assign (Info 3) "x" (Mult (Variable "x") (ALiteral (-1))))
                  (Assign (Info 4) "x" (Add (Variable "x") (ALiteral 1)))
             ]

    -- Example program, where we verify that a division-by-0 will not occur.
    evaluate [ Input (Info 1) "x"
             , If (Info 2) (Gt (Variable "x") (ALiteral 0))
                  (Assign (Info 3) "x" (Mult (Variable "x") (ALiteral (-2))))
                  (If (Info 4) (Lt (Variable "x") (ALiteral 0))
                      (Assign (Info 5)
                              "x" (Mult (Variable "x") (ALiteral (-5))))
                      (Assign (Info 6)
                              "x" (Add (Variable "x") (ALiteral 1))))
             , Invariant (Info 7) (Not (Eq (Variable "x") (ALiteral 0)))
             , Assign (Info 8) "y" (Div (ALiteral 1) (Variable "x"))
             ]

    -- Example program, equivalent to the above, where the Sign domain is not
    -- precise enough to determine that a division-by-0 will certainly not
    -- occur.
    evaluate [ Input (Info 1) "x"
             , If (Info 2) (Gt (Variable "x") (ALiteral 0))
                  (Seq (Assign (Info 3)
                               "a" (Mult (Variable "x") (ALiteral 3)))
                       (Assign (Info 4)
                               "x" (Sub (Variable "x") (Variable "a"))))
                  (If (Info 5) (Lt (Variable "x") (ALiteral 0))
                      (Seq (Assign (Info 6)
                                   "b" (Mult (Variable "x") (ALiteral 6)))
                           (Assign (Info 7)
                                   "x" (Sub (Variable "x") (Variable "b"))))
                      (Assign (Info 8) "x" (ALiteral 1)))
             , Invariant (Info 9) (Not (Eq (Variable "x") (ALiteral 0)))
             , Assign (Info 10) "y" (Div (ALiteral 1) (Variable "x"))
             ]
  where
    evaluate commands = do
        let p = foldr (Seq) (Skip (Info 0)) commands
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
         [ Input (Info 0) "x"
         , While (Info 0) (Not (Eq (Variable "x") (ALiteral 1)))
                 (Seq (Print (Info 0) (Variable "x"))
                      (If (Info 0) (Eq (Mod (Variable "x") (ALiteral 2))
                                       (ALiteral 0))
                          (Assign (Info 0)
                                  "x" (Div (Variable "x") (ALiteral 2)))
                          (Assign (Info 0)
                                  "x" (Add (Mult (ALiteral 3) (Variable "x"))
                                           (ALiteral 1)))))
         , Print (Info 0) (Variable "x")
         ]
    let p = foldr Seq (Skip (Info 0)) commands
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
