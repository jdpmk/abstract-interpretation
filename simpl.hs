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

putEnv :: (Eq a) => Env a b -> a -> b -> Env a b
putEnv env k v = (k, v):(filter (\(x, _) -> x /= k) env)

-- A wrapper around an environment keyed on identifiers, the primary use case
-- for environments in this program.
type Ident = String
type IEnv a = Env Ident a


-- Abstract syntax tree.

data Info = Info
    { label :: Int
    }

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

-- TODO: Add static assertions that are checked during abstract interpretation.
data Command
    = Skip Info
    | Seq Command Command
    | If Info BExp Command Command
    | While Info BExp Command
    | Assign Info Ident AExp
    | Print Info AExp
    | Input Info Ident
    deriving Show

data Interpretation a
    = ISkip Info (IEnv a)
    | ISeq (Interpretation a) (Interpretation a) (IEnv a)
    | IIf Info BExp
          (IEnv a) (Interpretation a)
          (IEnv a) (Interpretation a)
          (IEnv a)
    | IWhile Info BExp (Interpretation a) (IEnv a)
    | IAssign Info Ident AExp (IEnv a)
    | IPrint Info AExp (IEnv a)
    | IInput Info Ident (IEnv a)

instance (AbstractDomain a, Show a) => Show (Interpretation a) where
    show c = aux c 0
      where
        indent_width = 4
        getIndent d = replicate d ' '

        showEnv env d =
            getIndent d ++
            "{ " ++ (List.intercalate " ; " $ map mapping env) ++ " }" ++ "\n"
              where
                mapping (var, a) = show var ++ " -> " ++ show a

        aux c d =
            let indent = getIndent d in
            case c of
                ISkip i env ->
                    ""
                ISeq c1 c2 env ->
                    aux c1 d ++
                    aux c2 d
                IIf i guard env_sat c1 env_unsat c2 env ->
                    indent ++ "if " ++ show guard ++ " then\n" ++
                    showEnv env_sat (d + indent_width) ++
                    aux c1 (d + indent_width) ++
                    indent ++ "else\n" ++
                    showEnv env_unsat (d + indent_width) ++
                    aux c2 (d + indent_width) ++
                    indent ++ "end\n" ++
                    showEnv env d
                IWhile _ _ _ _ ->
                    undefined
                IAssign i var e env ->
                    indent ++ var ++ " := " ++ show e ++ "\n" ++
                    showEnv env d
                IPrint i e env ->
                    indent ++ show e ++ "\n" ++
                    showEnv env d
                IInput i var env ->
                    indent ++ var ++ " := input()\n" ++
                    showEnv env d


type Program = Command

getState :: (AbstractDomain a) => Interpretation a -> IEnv a
getState c = case c of
    ISkip _ e -> e
    ISeq _ _ e -> e
    IIf _ _ _ _ _ _ e -> e
    IWhile _ _ _ e -> e
    IAssign _ _ _ e -> e
    IPrint _ _ e -> e
    IInput _ _ e -> e

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
    Print _ e ->
        case evalAExp e env of
            Right e' -> do
                putStrLn $ show e'
                return $ Right env
            Left error ->
                return $ Left error
    Input _ var -> do
        input <- getLine
        let input_as_int = read input :: Int
        return $ Right $ putEnv env var input_as_int

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
        (_, ST)    -> True
        (SB, _)    -> True
        (SZP, SZP) -> True
        (SNP, SNP) -> True
        (SNZ, SNZ) -> True
        (SZ, SZP)  -> True
        (SP, SZP)  -> True
        (SN, SNP)  -> True
        (SP, SNP)  -> True
        (SN, SNZ)  -> True
        (SZ, SNZ)  -> True
        (SP, SP)   -> True
        (SZ, SZ)   -> True
        (SN, SN)   -> True
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

mergeEnv :: (Lattice a) => (a -> a -> a) -> IEnv a -> IEnv a -> IEnv a
mergeEnv f env1 env2 = foldr (mergeMapping f env1) [] env2
  where
    mergeMapping :: (Lattice a)
                 => (a -> a -> a)
                 -> IEnv a
                 -> (Ident, a)
                 -> IEnv a
                 -> IEnv a
    mergeMapping f env1 (var, aval) acc =
        let joined = case getEnv env1 var of
                         Left _ -> aval
                         Right aval1 -> f aval1 aval
        in (var, joined):acc

joinEnv :: (Lattice a) => IEnv a -> IEnv a -> IEnv a
joinEnv = mergeEnv join

meetEnv :: (Lattice a) => IEnv a -> IEnv a -> IEnv a
meetEnv = mergeEnv meet

type IEnvOrErr a = Either String (IEnv a)
type InterpretationOrErr a = Either String (Interpretation a)

class Lattice a => AbstractDomain a where
    aEvalAExp :: (Lattice a) => AExp -> IEnv a -> Either String a
    aEvalBExp :: (Lattice a) => BExp -> IEnv a -> Bool -> IEnvOrErr a
    aEvalCommand :: (Lattice a) => Command -> IEnv a -> InterpretationOrErr a

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
        -- A literal boolean expression will not affect the abstract
        -- environment.
        BLiteral _ ->
            Right env
        -- We toggle the flipped flag when performing negation. Effectively,
        -- this is used to emulate DeMorgan's law "locally" at the other
        -- binary operations (e.g. Or, Lt, etc).
        Not b ->
            aEvalBExp b env (not flipped)
        -- When performing conjunction/disjunction, we evaluate the
        -- subexpressions, and then perform either the meet or join of the
        -- resulting environments.
        --
        -- For disjunction, we broaden the possible values that can be taken
        -- on, for example, in "x > 5 || x = 0". In this case, "x" is SP when
        -- it is greater than 5, or SZ, when it is equal to 0. So, taking the
        -- join of SP and SZ yields SZP, which is the most precise abstract
        -- value we can use here, i.e., after this condition we know that "x"
        -- must be zero or positive.
        --
        -- Conjunction is similar, but we narrow the possible values that can
        -- be taken on, for example, in "x >= 0 && x = 0". In this case, "x"
        -- may be SZP when greater than or equal to 0, and SZ when equal to 0.
        -- Taking the meet of these abstract values yields is SZ, which is the
        -- most precise abstract value we can use here. This also makes sense
        -- logically: x >= 0 && x = 0 implies x = 0.
        Or b1 b2 -> do
            env1 <- aEvalBExp b1 env flipped
            env2 <- aEvalBExp b2 env flipped
            Right $ (if flipped then meetEnv else joinEnv) env1 env2
        And b1 b2 -> do
            env1 <- aEvalBExp b1 env flipped
            env2 <- aEvalBExp b2 env flipped
            Right $ (if flipped then joinEnv else meetEnv) env1 env2
        -- Boolean comparison operators provide a chance to further refine
        -- our abstract environment. For instance, suppose we have a boolean
        -- guard like:
        --
        --   if x = 0 then
        --       ...
        --
        -- The evaluation of the "x" will result in its current abstract value.
        -- We can discard this. The evaluation of the literal '0' will result
        -- in SZ. We want to detect this and update our abstract state for
        -- "x". In this case, we map "x" to SZ.
        --
        -- Technically, the guard can also be written as:
        --
        --   if 0 = x then
        --       ...
        --
        -- so we need to check whether EITHER side is a variable, not just the
        -- left-hand side.
        Eq e1 e2 -> do
            a1 <- aEvalAExp e1 env
            a2 <- aEvalAExp e2 env
            Right $ case e1 of
                Variable var -> putEnv env var (deduceEq a2 flipped)
                -- TODO: We should also check if e2 is a variable. Suppose the
                -- guard is: if x = y. "y" may have a more precise abstract
                -- mapping that we want to update "x" with.
                _  -> case e2 of
                    Variable var -> putEnv env var (deduceEq a1 flipped)
                    _  -> env
        Lt e1 e2 ->
            if flipped then
                aEvalBExp (Or (Gt e1 e2) (Eq e1 e2)) env (not flipped)
            else do
                a1 <- aEvalAExp e1 env
                a2 <- aEvalAExp e2 env
                Right $ case e1 of
                    Variable var ->
                        putEnv env var (deduceLess a2)
                    _  -> case e2 of
                        Variable var -> putEnv env var (deduceGreater a1)
                        _  -> env
        Gt e1 e2 ->
            if flipped then
                aEvalBExp (Or (Lt e1 e2) (Eq e1 e2)) env (not flipped)
            else do
                a1 <- aEvalAExp e1 env
                a2 <- aEvalAExp e2 env
                Right $ case e1 of
                    Variable var ->
                        putEnv env var (deduceGreater a2)
                    _  -> case e2 of
                        Variable var -> putEnv env var (deduceLess a1)
                        _  -> env
      where
        -- These are used to deduce an abstract value for a variable under
        -- certain conditions. For example,
        --
        --   if x < 0: then, 0 -> SZ, and we can deduce x should be SN
        --   if x > 0: then, 0 -> SZ, and we can deduce x should be SP
        --
        -- A more interesting case,
        --
        --   if x > y: suppose, y -> SZP, and we can deduce x should be SP
        --
        -- This doesn't work all the time, for example,
        --
        --   if x < 5: then, 5 -> SP, but we can't assign anything more precise
        --   than ST to "x". It could be negative, zero, or positive.
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
        deduceEq :: Sign -> Bool -> Sign
        deduceEq a flipped =
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

    aEvalCommand c env = case c of
        Skip i ->
            Right (ISkip i env)
        Seq c1 c2 -> do
            interp'  <- aEvalCommand c1 env
            interp'' <- aEvalCommand c2 (getState interp')
            Right $ ISeq interp' interp'' (getState interp'')
        -- Our abstract interpreter differs from our concrete interpreter in
        -- the fact that we are interested in exploring both branches of
        -- conditionals, not just the one for which the guard is satisfied.
        -- So we must evaluate the guard and its negation, and evaluate each
        -- branch with its respective environment, exhausting cases in which
        -- the guard was satisfied and unsatisfied. After evaluating both
        -- branches, we perform the join of the resulting environments.
        --
        -- Intuitively, this is like the "summation" of all the information we
        -- have gathered from the branches. Suppose two different executions of
        -- the program result in two different branches taken. We want to
        -- obtain an abstract value which encapsulates both (all) executions.
        If i guard c1 c2 -> do
            env_sat <- aEvalBExp guard env False
            env_unsat <- aEvalBExp (Not guard) env False

            let env_sat' = meetEnv env env_sat
            let env_unsat' = meetEnv env env_unsat

            interp1 <- aEvalCommand c1 env_sat'
            interp2 <- aEvalCommand c2 env_unsat'
            Right $ IIf i guard env_sat' interp1 env_unsat' interp2
                    (joinEnv (getState interp1) (getState interp2))
        -- TODO: Implement while.
        While _ _ _ ->
            undefined
        Assign i var e -> do
            a <- aEvalAExp e env
            Right $ IAssign i var e (putEnv env var a)
        Print i e ->
            Right $ IPrint i e env
        -- User input is entirely arbitrary (i.e. it could be negative, zero,
        -- or positive).
        Input i var ->
            Right $ IInput i var (putEnv env var ST)

-- Interprets a program over the abstract domain of signs, returning the final
-- state of the abstract environment.
-- TODO: Return [IEnvOrError Sign], i.e. the state of the abstract interpreter
-- at each step of the program.
signEvalProgram :: Program -> InterpretationOrErr Sign
signEvalProgram p = aEvalCommand p []


abstractMain :: IO ()
abstractMain = do
    --
    -- x := -1;  | x -> SN
    -- x := y;   | ERROR: "y" is unknown
    --
    evaluate [ Assign (Info 1) "x" (ALiteral (-1))
             , Assign (Info 2) "x" (Variable "y")
             ]

    --
    -- x := -1;      | x -> SN
    -- x := x * -1;  | x -> SP
    --
    evaluate [ Assign (Info 1) "x" (ALiteral (-1))
             , Assign (Info 2) "x" (Mult (Variable "x") (ALiteral (-1)))
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

    --
    -- x := input()      | x -> ST
    -- if !(x = 0) then  | x -> SNP
    --     x := x - 1;   | x -> ST
    -- else              | x -> SZ
    --     x := x + 1;   | x -> SP
    -- end               | x -> ST
    --
    evaluate [ Input (Info 1) "x"
             , If (Info 2) (Not (Eq (Variable "x") (ALiteral 0)))
                  (Assign (Info 3) "x" (Sub (Variable "x") (ALiteral (1))))
                  (Assign (Info 4) "x" (Add (Variable "x") (ALiteral (1))))
             ]

    --
    -- x := input()             | x -> ST
    -- if x >= 0 && x = 0 then  | x -> SZ
    --     x := x - 1;          | x -> SN
    -- else                     | x -> SNP
    --     skip;                | x -> SNP
    -- end                      | x -> SNP
    --
    evaluate [ Input (Info 1) "x"
             , If (Info 2) (And (Or (Gt (Variable "x") (ALiteral 0))
                                    (Eq (Variable "x") (ALiteral 0)))
                                (Eq (Variable "x") (ALiteral 0)))
                  (Assign (Info 3) "x" (Sub (Variable "x") (ALiteral (1))))
                  (Skip (Info 4))
             ]

    --
    -- x := input()             | x -> ST
    -- if x >= 0 && x = 0 then  | x -> SZ
    --     x := x - 1;          | x -> SN
    -- else                     | x -> SNP
    --     skip;                | x -> SNP
    -- end                      | x -> SNP
    --
    evaluate [ Input (Info 1) "x"
             , If (Info 2) (And (Or (Gt (Variable "x") (ALiteral 0))
                                (Eq (Variable "x") (ALiteral 0)))
                           (Eq (Variable "x") (ALiteral 0)))
                  (Assign (Info 3) "x" (Sub (Variable "x") (ALiteral (1))))
                  (Skip (Info 4))
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
             , Assign (Info 7) "y" (Div (ALiteral 1) (Variable "x"))
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
             , Assign (Info 9) "y" (Div (ALiteral 1) (Variable "x"))
             ]
  where
    separator = putStrLn ""
    evaluate commands = do
        separator
        let p = foldr (Seq) (Skip (Info 0)) commands
        case signEvalProgram p of
            Right interp ->
                putStrLn $ show interp
            Left error ->
                putStrLn $ "Error: " ++ error
        separator

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
