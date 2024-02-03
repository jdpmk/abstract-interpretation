--
-- Abstract interpretation for simpl (Simple IMperative Programming Language)
--                                    ~      ~~         ~           ~
-- 
-- simpl is a programming language consisting of basic imperative constructs,
-- including loops, conditionals, and arithmetic and boolean expressions.
--
-- Joydeep Mukherjee, 2024
--


import qualified Control.Monad as Monad
import qualified Data.Maybe as Maybe
import qualified Data.Either as Either


-- Utilities.

-- An environment mapping keys to values, implemented as an associative array.
type Env a b = [(a, b)]

getEnv :: (Show a, Eq a) => Env a b -> a -> Either String b
getEnv [] k = Left $ "unknown key: " ++ show k
getEnv ((x, v):rest) k = if x == k then Right v else getEnv rest k

putEnv :: (Eq a) => Env a b -> a -> b -> Env a b
putEnv env k v = (k, v):(filter (\(x, _) -> x /= k) env)

-- A wrapper around an environment keyed on identifiers, the primary use case
-- for environments in this program.
type Ident = String
type IEnv a = Env Ident a


-- Abstract syntax tree.

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
-- The domain of signs is simple: we map variables (numbers) to a value
-- indicating their sign. An application of this abstract domain is proving
-- the absence of a division-by-0.
--
--  .----- Top -----.
--  |       |       |
-- Neg    Zero     Pos
--  |       |       |
--  '----- Bot -----'
--
data Sign = STop | SPos | SZero | SNeg | SBot deriving Show

instance PartialOrd Sign where
    le x y = case (x, y) of
        (_, STop)      -> True
        (SBot, _)      -> True
        (SPos, SPos)   -> True
        (SZero, SZero) -> True
        (SNeg, SNeg)   -> True
        (_, _)         -> False

-- TODO: Can we enforce commutativity within the typeclass?
instance Lattice Sign where
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


-- Abstract interpreter.

mergeEnv :: (Lattice a) => (a -> a -> a) -> IEnv a -> IEnv a -> IEnv a
mergeEnv f env1 env2 = foldr (mergeMapping f env1) [] env2
  where
    mergeMapping :: (Lattice a)
                 => (a -> a -> a) -> IEnv a -> (Ident, a) -> IEnv a -> IEnv a
    mergeMapping f env1 (var, aval) acc =
        let joined = case getEnv env1 var of
                            Left _ -> aval
                            Right aval1 -> f aval1 aval
        in (var, joined):acc

joinEnv :: (Lattice a) => IEnv a -> IEnv a -> IEnv a
joinEnv = mergeEnv join

meetEnv :: (Lattice a) => IEnv a -> IEnv a -> IEnv a
meetEnv = mergeEnv meet

type IEnvOrError a = Either String (IEnv a)
class Lattice a => AbstractDomain a where
    aEvalAExp :: (Lattice a) => AExp -> IEnv a -> Either String a
    aEvalBExp :: (Lattice a) => BExp -> IEnv a -> Bool -> IEnvOrError a
    aEvalCommand :: (Lattice a) => Command -> IEnv a -> IEnvOrError a

instance AbstractDomain Sign where
    aEvalAExp e env = case e of
        -- Evaluation of a literal is simple: from the value, we can easily
        -- deduce whether the literal is negative, zero, or positive.
        ALiteral val ->
            Right $ if val < 0 then SNeg
                    else if val == 0 then SZero
                    else SPos
        -- We look up variables in the current abstract environment.
        Variable var ->
            getEnv env var
        -- For binary arithmetic operations, we can deduce the sign of the
        -- result in many cases. For instance, we know that the addition of
        -- any two positive numbers is always positive, the subtraction of
        -- a positive number from a negative number is always negative, and so
        -- on. Zero is also a nice "identity" in many cases.
        --
        -- However this isn't perfect. For instance, we don't know for certain
        -- what the resulting sign of the addition of a positive and negative
        -- number is. Depending on the magnitude of the numbers, the result
        -- could be negative, zero, or positive. In such cases, we use STop.
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
                (_, STop)    -> SBot  -- Possible (not certain) division by 0
                (_, SZero)   -> SBot  -- Division by 0
                (SZero, _)   -> SZero
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
                (_, STop)    -> SBot  -- Possible (not certain) division by 0
                (_, SZero)   -> SBot  -- Division by 0
                (SZero, _)   -> SZero
                (SPos, SPos) -> SPos
                (SNeg, SNeg) -> SPos
                (SPos, SNeg) -> SNeg  -- TODO: Revisit these semantics.
                (SNeg, SPos) -> SNeg  -- TODO: Revisit these semantics.
                (_, _)       -> STop

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
        -- on, for example, in "x > 5 || x = 0". In this case, "x" may be SPos
        -- when it is greater than 5, or SZero, when it is equal to 0. So,
        -- taking the join of SPos and SZero yields STop, which is the most
        -- precise abstract value we can use here.
        --
        -- Conjunction is similar, but we narrow the possible values that can
        -- be taken on, for example, in "x >= 0 && x = 0". In this case, "x"
        -- may be STop when greater than or equal to 0, and SZero when equal
        -- to 0. Taking the meet of these abstract values yields is SZero,
        -- which is the most precise abstract value we can use here. This also
        -- makes sense logically: x >= 0 && x = 0 implies x = 0.
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
        -- in SZero. We want to detect this and update our abstract state for
        -- "x". In this case, we map "x" to SZero.
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
            a2 <- aEvalAExp e1 env
            Right $ case e1 of
                Variable var -> putEnv env var a2
                -- TODO: We should also check if e2 is a variable. Suppose the
                -- guard is: if x = y. "y" may have a more precise abstract
                -- mapping that we want to update "x" with.
                _  -> case e2 of
                    Variable var -> putEnv env var a1
                    _  -> env
        Lt e1 e2 ->
            if flipped then
                aEvalBExp (Or (Gt e1 e2) (Eq e1 e2)) env (not flipped)
            else do
                a1 <- aEvalAExp e1 env
                a2 <- aEvalAExp e1 env
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
                a2 <- aEvalAExp e1 env
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
        --   if x < 0: then, 0 -> SZero, and we can deduce x should be SNeg
        --   if x > 0: then, 0 -> SZero, and we can deduce x should be SPos
        --   if x > 5: then, 5 -> SPos, and we can deduce x should be SPos
        --
        -- This doesn't work all the time, for example,
        --
        --   if x < 5: then, 3 -> SPos, but we can't say anything too precise
        --   about "x". It could be negative, zero, or positive.
        deduceLess :: Sign -> Sign
        deduceLess a = case a of
            SZero -> SNeg
            SPos  -> STop
            _     -> a
        deduceGreater :: Sign -> Sign
        deduceGreater a = case a of
            SZero -> SPos
            SNeg  -> STop
            _     -> a

    aEvalCommand c env = case c of
        Skip ->
            Right env
        Seq c1 c2 -> do
            env'  <- aEvalCommand c1 env
            env'' <- aEvalCommand c2 env'
            Right env''
        -- Our abstract interpreter differs from our concrete interpreter in
        -- the fact that we are interested in exploring both branches of
        -- conditionals, not just the one for which the guard is satisfied.
        -- So we must evaluate the guard and its negation, and evaluate each
        -- branch with its respective environment, exhausting cases in which
        -- the guard was satisfied and unsatisfied. After evaluating both
        -- branches, we perform the join of the resulting environments.
        -- Intuitively, this is like the "summation" of all the information
        -- we have gathered from the branches. Suppose two different executions
        -- of the program result in two different branches taken. We want to
        -- obtain an abstract value which encapsulates both (all) executions.
        If guard c1 c2 -> do
            env_sat <- aEvalBExp guard env False
            env_unsat <- aEvalBExp (Not guard) env False
            env1 <- aEvalCommand c1 env_sat
            env2 <- aEvalCommand c2 env_unsat
            Right $ joinEnv env1 env2
        -- TODO: Implement while.
        While _ _ ->
            undefined
        Assign var e -> do
            a <- aEvalAExp e env
            Right $ putEnv env var a
        Print _ ->
            Right env

signEvalProgram :: Program -> Maybe (IEnv Sign)
signEvalProgram p =
    Either.either (const Nothing) Just $ aEvalCommand p []

abstractMain :: IO ()
abstractMain = do
    --
    -- At the end of the following example, we can statically assert that the
    -- value of "x" is positive.
    --
    -- x := 0;           | x -> STop
    -- if x < 0 then     | x -> SNeg
    --     x := x * -1;  | x -> SPos
    -- else              | x -> STop
    --     x := 1        | x -> SPos
    -- end               | x -> SPos
    --
    evaluate [ Assign "x" (ALiteral 0)
             , If (Lt (Variable "x") (ALiteral 0))
                  (Assign "x" (Mult (Variable "x") (ALiteral (-1))))
                  (Assign "x" (ALiteral 1))
             ]
    --
    -- At the end of the following example, we can statically assert that we
    -- will certainly not have a division by 0.
    --
    -- x := 0;          | x -> SZero
    -- y := 5;          | x -> SZero, y -> SPos
    -- if x > 0 then    | x -> SPos, y -> SPos
    --     y := y / x;  | x -> SPos, y -> SPos
    -- else             | x -> STop, y -> SPos
    --     y := 1       | x -> STop, y -> SPos
    -- end              | x -> STop, y -> SPos
    --
    evaluate [ Assign "x" (ALiteral 0)
             , Assign "y" (ALiteral 5)
             , If (Gt (Variable "x") (ALiteral 0))
                  (Assign "y" (Div (Variable "y") (Variable "x")))
                  (Assign "y" (ALiteral 1))
             ]
    --
    -- We may encounter division by 0 when "x" is 0. At the point where we
    -- perform the division, we should set "y" to SBot. At the end of the
    -- program, we perform the join of SBot and SNeg and "y" is set to SNeg.
    --
    -- x := 0;                | x -> SZero
    -- y := 5;                | x -> SZero, y -> SPos
    -- if x > 0 or x = 0 then | x -> STop, y -> SPos   TODO: maybe here we can
    --                                                 deduce that x = 0?
    --     y := y / x;        | x -> STop, y -> SNeg
    -- else                   | x -> SNeg, y -> SPos
    --     y := -1            | x -> SNeg, y -> SPos
    -- end                    | x -> STop, y -> SPos
    --
    evaluate [ Assign "x" (ALiteral 0)
             , Assign "y" (ALiteral 5)
             , If (Or (Gt (Variable "x") (ALiteral 0))
                      (Eq (Variable "x") (ALiteral 0)))
                  (Assign "y" (Div (Variable "y") (Variable "x")))
                  (Assign "y" (ALiteral (-1)))
             ]
  where
    evaluate commands = do
        let p = foldr (Seq) Skip commands
        let env = signEvalProgram p
        Monad.when (Maybe.isJust env) $ putStrLn $ show $ Maybe.fromJust env

concreteMain :: IO ()
concreteMain = do
    --
    -- x := 42;
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
    Monad.when (Maybe.isJust error) $ putStrLn (Maybe.fromJust error)
