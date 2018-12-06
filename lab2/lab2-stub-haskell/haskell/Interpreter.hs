module Interpreter where


import Control.Applicative    
import Control.Monad.Except    
import Control.Monad
import Control.Monad.Reader
import Control.Monad.State

import Data.Functor
import Data.Map (Map)
import Debug.Trace
import qualified Data.Map as Map

import CPP.Abs
import CPP.Print
import CPP.ErrM

type Eval = ReaderT Sig (StateT Env (ExceptT Val IO))

type Env = [Context]
type Sig = Map Id FunDef
type Context = Map Id Val

data FunDef = FunDef { typ :: Type,funParams :: [Id], funBody :: [Stm] }

data Execute = Go
             | Stop

data Val = VInt Integer
         | VDouble Double
         | VBool Bool
         | VVoid
         deriving Show

interpret :: Program -> IO ()
interpret (PDefs defs) = do
    -- Prepare the signature.
    let sigEntry (DFun typ f args ss) = (f, FunDef typ (map (\ (ADecl _ x) -> x) args) ss)
    let sig = Map.fromList $ map sigEntry defs
    -- Find the entry point ("main" function).
    let ss = maybe (error "no main") funBody $ Map.lookup (Id "main") sig
    -- Run the statements in the initial environment.
    () <$ runExceptT (evalStateT (runReaderT (evalStms ss) sig) emptyEnv)

-- Assuming that the typechecker is OK 
lookupVar :: Id -> Eval Val
lookupVar id = do
    c:cs <- get
    case Map.lookup id c of
        (Just a) -> return a
        otherwise -> do 
            put cs
            val <- lookupVar id
            put (c:cs)
            return val

updateVar :: Id -> Val -> Eval ()
updateVar id val = modify $ (\env -> update env id val)
  where update :: Env -> Id -> Val -> Env
        update [] id val = undefined
        update (x:xs) id val = case Map.lookup id x of
            (Just a) -> (Map.update (return (Just val)) id x) : xs
            otherwise -> x : update xs id val

evalFun :: Id -> [Exp]-> Eval Val
evalFun id exps = do
    sig <- ask
    case Map.lookup id sig of
        (Just a) -> case a of
            (FunDef typ params stms) -> do
                updateParams exps params
                val <- lookupVar (Id "averyspecialname")
                evalStms stms
                popBlock
                lookupVar (Id "averyspecialname")

readInt :: IO Integer
readInt = do
    x <- getLine
    return (read x :: Integer)

readDouble :: IO Double
readDouble = do
    x <- getLine
    return (read x :: Double)


updateParams :: [Exp] -> [Id] -> Eval ()
updateParams [] [] = return ()
updateParams exps params = do
    val <- evalExp (head exps)
    newVar (head params) val
    updateParams (tail exps) (tail params)


evalExp :: Exp -> Eval Val
evalExp x = case x of
    ETrue -> return $ VBool True
    EFalse -> return $ VBool False
    EInt i -> return $ VInt i
    EDouble d -> return $ VDouble d
    EId id -> lookupVar id
    EApp fun exps -> do
        case fun of
            (Id "printInt") -> do
                VInt i <- evalExp $ head exps
                liftIO $ putStrLn $ show i
                return VVoid
            (Id "printDouble") -> do
                VDouble d <- evalExp $ head exps
                liftIO $ putStrLn $ show d
                return VVoid
            (Id "readInt") -> do
                i <- liftIO $ readInt 
                return (VInt i)
            (Id "readDouble") -> do
                d <- liftIO $ readDouble
                return (VDouble d)
            otherwise -> do
                newBlock 
                evalFun fun exps
    EPostIncr id -> do
        val <- lookupVar id
        case val of
            (VInt i) -> do
                updateVar id (VInt (i+1))
                return val
            (VDouble d) -> do
                updateVar id (VDouble (d+1))
                return val
    EPostDecr id -> do
        val <- lookupVar id
        case val of
            (VInt i) -> do
                updateVar id (VInt (i-1))
                return val
            (VDouble d) -> do
                updateVar id (VDouble (d-1))
                return val
    EPreIncr id -> do
        val <- lookupVar id
        case val of
            (VInt i) -> do
                updateVar id (VInt (i+1))
                lookupVar id
            (VDouble d) -> do
                updateVar id (VDouble (d+1))
                lookupVar id
    EPreDecr id -> do
        val <- lookupVar id
        case val of
            (VInt i) -> do
                updateVar id (VInt (i-1))
                lookupVar id
            (VDouble d) -> do
                updateVar id (VDouble (d-1))
                lookupVar id

    EPlus exp1 exp2 -> do
        e1 <- evalExp exp1
        e2 <- evalExp exp2
        case e1 of
            VInt i -> do
                case e2 of
                    VInt j -> do
                        return (VInt(i+j))
            VDouble d -> do
                case e2 of
                    VDouble d1 -> do
                        return(VDouble(d+d1))
    EMinus exp1 exp2 -> do
        e1 <- evalExp exp1
        e2 <- evalExp exp2
        case e1 of
            VInt i -> do
                case e2 of
                    VInt j -> do
                        return (VInt(i-j))
            VDouble d -> do
                case e2 of
                    VDouble d1 -> do
                        return(VDouble(d-d1))
    ETimes exp1 exp2 -> do
        e1 <- evalExp exp1
        e2 <- evalExp exp2
        case e1 of
            VInt i -> do
                case e2 of
                    VInt j -> do
                        return (VInt(i*j))
            VDouble d -> do
                case e2 of
                    VDouble d1 -> do
                        return(VDouble(d*d1))
    EDiv exp1 exp2 -> do
        e1 <- evalExp exp1
        e2 <- evalExp exp2
        case e1 of
            VInt i -> do
                case e2 of
                    VInt j -> do
                        return (VInt(i `div`j))
            VDouble d -> do
                case e2 of
                    VDouble d1 -> do
                        return(VDouble(d/d1))
    ELt exp1 exp2 -> do
        e1 <- evalExp exp1
        e2 <- evalExp exp2
        case e1 of
            VInt i -> do
                case e2 of
                    VInt j -> do
                        return (VBool(i < j))
            VDouble d -> do
                case e2 of
                    VDouble d1 -> do
                        return(VBool(d < d1))
    EGt exp1 exp2 -> do
        e1 <- evalExp exp1
        e2 <- evalExp exp2
        case e1 of
            VInt i -> do
                case e2 of
                    VInt j -> do
                        return (VBool(i > j))
            VDouble d -> do
                case e2 of
                    VDouble d1 -> do
                        return(VBool(d > d1))
    ELtEq exp1 exp2 -> do
        e1 <- evalExp exp1
        e2 <- evalExp exp2
        case e1 of
            VInt i -> do
                case e2 of
                    VInt j -> do
                        return (VBool(i <= j))
            VDouble d -> do
                case e2 of
                    VDouble d1 -> do
                        return(VBool(d <= d1))
    EGtEq exp1 exp2 -> do
        e1 <- evalExp exp1
        e2 <- evalExp exp2
        case e1 of
            VInt i -> do
                case e2 of
                    VInt j -> do
                        return (VBool(i >= j))
            VDouble d -> do
                case e2 of
                    VDouble d1 -> do
                        return(VBool(d >= d1))
    EEq exp1 exp2 -> do
        e1 <- evalExp exp1
        e2 <- evalExp exp2
        case e1 of
            VInt i -> do
                case e2 of
                    VInt j -> do
                        return (VBool(i == j))
            VDouble d -> do
                case e2 of
                    VDouble d1 -> do
                        return(VBool(d == d1))
            VBool b -> do
                case e2 of
                    VBool b1 -> do
                        return(VBool (b == b1))
    ENEq exp1 exp2 -> do
        e1 <- evalExp exp1
        e2 <- evalExp exp2
        case e1 of
            VInt i -> do
                case e2 of
                    VInt j -> do
                        return (VBool (not(i == j)))
            VDouble d -> do
                case e2 of
                    VDouble d1 -> do
                        return(VBool (not(d == d1)))
            VBool b -> do
                case e2 of
                    VBool b1 -> do
                        return(VBool (not(b == b1)))
    EAnd exp1 exp2 -> do
        e1 <- evalExp exp1
        case e1 of
            VBool b -> do
                case b of
                    False -> return (VBool False)
                    True -> do
                        e2 <- evalExp exp2
                        case e2 of
                            VBool b1 -> do
                                return (VBool (b && b1))
    EOr exp1 exp2 -> do
        VBool b1 <- evalExp exp1
        case b1 of
            True -> return (VBool True)
            otherwise ->  do
                VBool b2 <- evalExp exp2 
                return (VBool (b1 || b2))
    EAss id exp -> do
        e1 <- evalExp exp
        updateVar id e1
        lookupVar id


evalStm :: Stm -> Eval Execute
evalStm s = do
    env <- get
    --liftIO $ putStrLn (show env)
    --liftIO $ putStrLn (show s) 
    --liftIO $ putStrLn "\n"
    case s of
        SExp exp -> do
            evalExp exp
            return Go
        SDecls typ ids -> do
            mapM_ (decls typ) ids
            return Go
        SInit typ id exp -> do
            e <- evalExp exp
            newVar id e
            return Go
        SWhile exp stm -> do
            e <- evalExp exp
            newBlock
            case e of
                (VBool True) -> do
                    evalStm stm
                    popBlock
                    evalStm $ SWhile exp stm
                    return Go
                (VBool False) -> do 
                    popBlock
                    return Go
        SBlock stms -> do
            newBlock
            evalStms stms

            --liftIO $ putStrLn "före:"
            --env' <- get
            --liftIO $ putStrLn (show env')

            popBlock
            return Go
        SIfElse exp stm1 stm2 -> do
            e <- evalExp exp
            newBlock
            case e of
                (VBool True) -> do
                    evalStm stm1
                    popBlock
                    return Go
                otherwise -> do
                    evalStm stm2
                    popBlock
                    return Go
        SReturn exp -> do
            val <- evalExp exp
            updateVar (Id "averyspecialname") val
            return Stop
        


evalStms :: [Stm] -> Eval Execute
evalStms [] = return Go
evalStms (s:stms) =  do
    --val <- lookupVar (Id "averyspecialname")
    case s of
        SReturn exp -> do 
             val <- evalExp exp
             updateVar (Id "averyspecialname") val
             return Stop
        otherwise -> do 
            evalStm s
            evalStms stms

newVar :: Id -> Val -> Eval()
newVar id val = do
    (c:cs) <- get
    put (Map.insert id val  c : cs)

emptyEnv :: Env
emptyEnv = [Map.singleton (Id "averyspecialname") VVoid]

newBlock :: Eval ()
newBlock = do
    env <- get
    put $ Map.empty : env


popBlock :: Eval ()
popBlock = do
    env <- get
    put (tail env)

decls :: Type -> Id -> Eval()
decls typ id = case typ of
    Type_int -> do
        newVar id (VInt 0)
    Type_double -> do
        newVar id (VDouble 0)
    Type_bool -> do
        newVar id (VBool False)
