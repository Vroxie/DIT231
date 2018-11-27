module TypeChecker where

import Control.Monad

import Data.Map (Map)
import Data.Foldable
import qualified Data.Map as Map

import CPP.Abs
import CPP.Print
import CPP.ErrM

type Env = (Sig,[Context])
type Sig = Map Id ([Type],Type)
type Context = Map Id Type

typecheck :: Program -> Err ()
typecheck (PDefs defs) = do
                let sig = createSig defs
                let env = newBlock (sig,[])
                lookupMain env
                checkDefNames env defs
                foldlM (\env_X def -> checkDefArgs env_X def ) env defs
                mapM_ (checkDef env) defs

                --return ()

createSig :: [Def] -> Sig
createSig defs = Map.fromList (map defToSig defs)

genDefName :: Def -> Id
genDefName (DFun typ id args stms) = id

genDefNames :: [Def] -> [Id]
genDefNames defs = map genDefName defs ++ [Id "printInt",Id "printDouble",Id "readInt", Id "readDouble"]

checkDefNames :: Env -> [Def] -> Err Env
checkDefNames env [] = return env
checkDefNames env defs | elem (head (genDefNames defs)) (tail (genDefNames defs)) = fail $ "Each function name must be unique!"
                       | otherwise = checkDefNames env (tail defs)

checkDef :: Env -> Def -> Err Env
checkDef env def = case def of
        DFun typ id args stms -> checkStms env typ stms

checkDefArgs :: Env -> Def -> Err Env
checkDefArgs env (DFun typ id args stms) = foldlM (\env_X arg -> checkArg env_X arg ) env args

checkArg :: Env -> Arg -> Err Env
checkArg env (ADecl typ id) = case typ == Type_void of
        True -> fail $ "Arguments with type void is not allowed!"
        False -> return env


defToSig :: Def -> (Id,([Type],Type))
defToSig def = case def of
        DFun typ id args stms -> (id,((map argsToType args),typ))

argsToType :: Arg -> Type
argsToType arg = case arg of
        ADecl typ id -> typ

lookupMain :: Env -> Err Env
lookupMain (sig,context) = do
        let id = Id "main" 
        case Map.lookup id sig of
         (Just a) -> case isIntReturn a of
                True -> return (sig,context)
                False -> fail $ "Your main function has the wrong type! It should be int!"
         otherwise -> fail $ "Missing a main() function!"

isIntReturn :: ([Type],Type) -> Bool
isIntReturn (args,typ) = typ == Type_int

lookupVar :: Env -> Id -> Err Type
lookupVar (sig,[]) id = fail $ "Cannot resolve symbol " ++ (show id)  
lookupVar (sig,context) id = case Map.lookup id (head context) of
        (Just a) -> case noDuplicateVar (sig,context) id of
                True -> return a
                False -> fail $ "Variable with name " ++ (show id) ++ " has already been taken!"
        otherwise -> lookupVar (sig, tail context) id

noDuplicateVar :: Env -> Id -> Bool
noDuplicateVar (_,[]) id = True
noDuplicateVar (sig,context) id = case Map.lookup id (head context) of
        (Just a) -> False 
        otherwise -> noDuplicateVar (sig,tail context) id

noDuplicateFun :: Env -> Id -> Bool
noDuplicateFun (sig,context) id = case Map.lookup id sig of
        (Just a) -> True
        otherwise -> False        

lookupFun :: Env -> Id -> Err ([Type], Type)
lookupFun (sig,context) id = case Map.lookup id sig of
        (Just a) -> return a
        otherwise -> fail $ "Cannot resolve symbol " ++ (show id)

hasVoidasArg :: ([Type],Type) -> Bool
hasVoidasArg ([],_) = False
hasVoidasArg(types,typ) | (head types) == Type_void = True
                        | otherwise = hasVoidasArg ((tail types),typ)

updateVar :: Env -> Id -> Type -> Err Env
updateVar (sig,context) id typ = case updateHelp context id of
        (False,_) -> return $ (sig,(Map.insert id typ (head context)) : (tail context))
        (True, ctx) -> case noDuplicateVar (sig,context) id of
                True -> return $ (sig, ctx)
                False -> fail $ "Variable with name " ++ (show id) ++ " has already been taken!"

updateFun :: Env -> Id -> ([Type], Type) -> Err Env
updateFun (sig,context) id fun = case Map.lookup id sig of
        (Just a) -> return $ ((Map.update (return (Just fun)) id sig),context)
        otherwise -> return $ ((Map.insert id fun sig),context)


updateHelp :: [Context] -> Id -> (Bool,[Context])
updateHelp []  _ = (False,[])
updateHelp context id = case Map.lookup id (head context) of
        (Just a) -> (True,(Map.update (return (Just a) ) id (head context)) : (tail context))
        otherwise -> let (b, ctx) = updateHelp (tail context) id
                     in (b, (head context) : ctx)

newBlock :: Env -> Env
newBlock (sig,context) = (sig, Map.empty : context)

popBlock :: Env -> Env
popBlock (sig,context) = (sig, (tail context))

emptyEnv :: Env
emptyEnv = (Map.empty,[])

--helper :: Eq a, Monad m => [a] -> [m a] -> Bool
--helper xs ys = undefined

checkIncDec :: Env -> Id -> Err Type
checkIncDec env id = do
        a <- lookupVar env id
        case a == Type_int of
                True -> return Type_int
                False -> fail $ (show id) ++ " must be a Integer! Actual type: " ++ (show a)

inferBin :: [Type] -> Env -> Exp -> Exp -> Err Type
inferBin types env exp1 exp2 = do
        typ <- inferExp env exp1
        if elem typ types
                then
                        checkExp env typ exp2
                else
                        fail $ "wrong type of expression " ++ printTree exp1


checkExp :: Env -> Type -> Exp -> Err Type
checkExp env typ exp = do
        typ2 <- inferExp env exp
        if (typ2 == typ) then
                return typ2
         else
                fail $ "type of " ++ printTree exp ++
                       " expected " ++ printTree typ ++
                       " but found " ++ printTree typ2

inferBinComp :: [Type] -> Env -> Exp -> Exp -> Err Type
inferBinComp types env exp1 exp2 = do
        typ <- inferExp env exp1
        if elem typ types
                then
                        checkExpComp env typ exp2
                else
                        fail $ "wrong type of expression " ++ printTree exp1


checkExpComp :: Env -> Type -> Exp -> Err Type
checkExpComp env typ exp = do
        typ2 <- inferExp env exp
        if (typ2 == typ) then
                return Type_bool
         else
                fail $ "type of " ++ printTree exp ++
                       "expected " ++ printTree typ ++
                       "but found " ++ printTree typ2




inferExp :: Env -> Exp -> Err Type
inferExp env x = case x of
        ETrue -> return Type_bool
        EFalse -> return Type_bool
        EInt i -> return Type_int
        EDouble d -> return Type_double
        EId id -> lookupVar env id
        EApp id exp -> do
                (args, ret) <- lookupFun env id
                let inferredExps = map (inferExp env) exp
                let okargs = map Ok args
                case inferredExps == okargs of
                        True -> return ret
                        False -> fail $ "The name of the method is right but the return type is wrong!"

        EPostIncr id -> checkIncDec env id
        EPostDecr id -> checkIncDec env id
        EPreIncr id -> checkIncDec env id
        EPreDecr id -> checkIncDec env id
        ETimes exp1 exp2 -> inferBin [Type_int,Type_double] env exp1 exp2
        EDiv exp1 exp2 -> inferBin [Type_int,Type_double] env exp1 exp2
        EPlus exp1 exp2 -> inferBin [Type_int,Type_double] env exp1 exp2
        EMinus exp1 exp2 -> inferBin [Type_int,Type_double] env exp1 exp2
        ELt exp1 exp2 -> inferBinComp [Type_int,Type_double] env exp1 exp2
        EGt exp1 exp2 -> inferBinComp [Type_int,Type_double] env exp1 exp2
        ELtEq exp1 exp2 -> inferBinComp [Type_int,Type_double] env exp1 exp2
        EGtEq exp1 exp2 -> inferBinComp [Type_int,Type_double] env exp1 exp2
        EEq exp1 exp2   -> inferBin [Type_int,Type_double,Type_bool] env exp1 exp2
        ENEq exp1 exp2  -> inferBin [Type_int,Type_double,Type_bool] env exp1 exp2
        EAnd exp1 exp2  -> inferBin [Type_bool] env exp1 exp2
        EOr  exp1 exp2  -> inferBin [Type_bool] env exp1 exp2
        EAss id exp     -> do
                a <- lookupVar env id
                expErr <- inferExp env exp
                case a == expErr of
                        True -> return a
                        False ->  fail $ "Variable with type " ++ (show a) ++ " cannot be assigned to type " ++ (show expErr)


checkStm :: Env -> Type -> Stm -> Err Env
checkStm env val x = case x of
        SExp exp -> do
                inferExp env exp
                return env
        SDecls typ ids -> case not (typ == Type_void) of
                True -> do
                        declcenv <- foldlM (\env_X id -> updateVar env_X id typ) env ids
                        return declcenv
                False -> fail $ "Cant declare variable with type void!"
        SInit typ id exp -> do
                declsexp <- inferExp env exp
                case declsexp == typ of
                        True -> updateVar env id typ
                        False -> fail $ "Variable with type " ++ (show typ) ++ " cannot be assigned to type " ++ (show declsexp)
        SWhile exp stm -> do
                checkExp env Type_bool exp
                env' <- checkStm (newBlock env) val stm
                return env
        SBlock stms ->  do 
                env' <- checkStms (newBlock env) val stms
                return env
        SIfElse exp stm1 stm2 -> do
                checkExp env Type_bool exp
                env'<- checkStms env val [stm1,stm2]
                return env
        SReturn exp -> do
                rexp <- inferExp env exp
                case rexp == val of
                        True -> return env
                        False -> fail $ "You are returning the type " ++ (show rexp) ++ " when you are supposed to return " ++ (show val)






checkStms :: Env -> Type -> [Stm] -> Err Env
checkStms env typ stms = case stms of
        [] -> return $ env
        x : rest -> do
                env' <- checkStm env typ x
                checkStms env' typ rest