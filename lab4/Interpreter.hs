module Interpreter (interpret, Strategy(..)) where

import Control.Applicative
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Except

import Data.Functor
import Data.Map (Map)
import qualified Data.Map as Map

import Fun.Abs
import Fun.Print

-- | Evaluation strategy.

data Strategy
    = CallByName
    | CallByValue

-- | Error monad.

type Err = Except String

type Sig = Map Ident Exp

data Entry 
    = Clos Exp Env -- For call-by-name
    | Val Value -- For call-by-value

type Env = Map Ident Entry

data Value
    = VInt Integer
    | VClos Ident Exp Env

data Cxt = Cxt
    { cxtStrategy :: Strategy  -- ^ Evaluation strategy (fixed).
    , cxtSig      :: Sig       -- ^ Binds function identifiers to expression.
    , cxtEnv      :: Env       -- ^ Binds local variables to values.
    }

interpret :: Strategy -> Program -> Err Integer
interpret strategy (Prog defs (DMain mainExp)) = do
    let defToSigEntry (DDef f xs e) = (f, foldr EAbs e xs)
    let sig = Map.fromList (map defToSigEntry defs)
    let cxt = Cxt
            { cxtStrategy = strategy
            , cxtSig      = sig
            , cxtEnv      = Map.empty
            }
    v <- eval cxt mainExp  -- without Reader monad

    -- Inspect the result.
    case v of
        VInt i  -> return i
        VClos{} -> fail $ "main should return an integer"
    

newVar :: Cxt -> Ident -> Value -> Err Cxt
newVar cxt id val = return $ (cxt {cxtEnv = Map.insert id (Val val) (cxtEnv cxt)})


eval :: Cxt -> Exp -> Err Value
eval cxt exp = case exp of
    EInt i -> return (VInt i)
    EVar id -> do
        case Map.lookup id (cxtEnv cxt) of
            (Just entry) -> evalEntry cxt entry
            Nothing -> case Map.lookup id (cxtSig cxt) of
                (Just body) -> eval (cxt {cxtEnv = Map.empty}) body
                Nothing -> fail $ "unbound indentifier: " ++ printTree id
    EAbs id exp -> return $ VClos id exp (cxtEnv cxt)
    EAdd exp1 exp2 -> do
        evale1 <- eval cxt exp1
        case evale1 of
            VInt i -> do
                evale2 <- eval cxt exp2
                case evale2 of
                    VInt j -> return $ VInt(i+j)
                    VClos id exp env -> case (cxtStrategy cxt) of
                        CallByValue -> do
                            VInt k <- eval cxt exp
                            return $ VInt(i+k)
                        CallByName -> do
                            VInt h <- (eval cxt) (EVar id)
                            return $ VInt(i+h)
            VClos id exp env -> case (cxtStrategy cxt) of
                CallByValue -> do
                    VInt i <- eval cxt exp
                    evale2 <- eval cxt exp2
                    case evale2 of
                        VInt j -> return $ VInt(i+j)
                        VClos id exp env -> fail $ "Cant add two functions!"
                CallByName -> do
                    VInt h <- (eval cxt) (EVar id)
                    evale2 <- eval cxt exp2
                    case evale2 of
                        VInt f -> return $ VInt(h+f)
                        VClos id exp env -> fail $ "Cant add two functions!"
    ESub exp1 exp2 -> do
        evale1 <- eval cxt exp1
        case evale1 of
            VInt i -> do
                evale2 <- eval cxt exp2
                case evale2 of
                    VInt j -> return $ VInt(i-j)
                    VClos id exp env -> case (cxtStrategy cxt) of
                        CallByValue -> do
                            VInt k <- eval cxt exp
                            return $ VInt(i-k)
                        CallByName -> do
                            VInt h <- (eval cxt) (EVar id)
                            return $ VInt(i-h)
            VClos id exp env -> case (cxtStrategy cxt) of
                CallByValue -> do
                    VInt i <- eval cxt exp
                    evale2 <- eval cxt exp2
                    case evale2 of
                        VInt j -> return $ VInt(i-j)
                        VClos id exp env -> fail $ "Cant sub two functions!"
                CallByName -> do
                    VInt h <- (eval cxt) (EVar id)
                    evale2 <- eval cxt exp2
                    case evale2 of
                        VInt f -> return $ VInt(h-f)
                        VClos id exp env -> fail $ "Cant sub two functions!"
    ELt exp1 exp2 -> do
        VInt i <- eval cxt exp1
        VInt j <- eval cxt exp2
        case i < j of
            True -> return $ VInt 1
            False -> return $ VInt 0
    EIf ifexp thexp elexp -> do
        VInt ife <- eval cxt ifexp
        case ife of
            1 -> eval cxt thexp
            0 -> eval cxt elexp
    EApp fun exp -> do
        vf <- eval cxt fun
        case vf of
            VInt{} -> fail $ "application of a non-function"
            VClos id exp env -> do
                case (cxtStrategy cxt) of
                    CallByValue -> do
                        va <- eval cxt exp
                        eval (cxt {cxtEnv = Map.insert id (Val va) env}) exp
                    CallByName -> do
                        eval (cxt {cxtEnv = Map.insert id (Clos exp(cxtEnv cxt)) env }) exp



evalEntry :: Cxt -> Entry -> Err Value
evalEntry cxt (Val v) = return v
evalEntry cxt (Clos e env) = eval (cxt {cxtEnv = env}) e
