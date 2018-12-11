-- Optional: turn on warnings.
-- {-# OPTIONS_GHC -Wall #-}

{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}

-- | Compiler for C--, producing symbolic JVM assembler.

module Compiler where

import Control.Monad
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.RWS

import Data.Maybe
import Data.Map (Map)
import qualified Data.Map as Map

--import Annotated

import CPP.Abs
import CPP.Print (printTree)
import TypeChecker (FunType(..))


data St = St
  { cxt           :: Cxt   -- ^ Context.
  , limitLocals   :: Int   -- ^ Maximal size for locals encountered.
  , currentStack  :: Int   -- ^ Current stack size.
  , limitStack    :: Int   -- ^ Maximal stack size encountered.
  , nextLabel     :: Label -- ^ Next jump label (persistent part of state)
  }

type Sig = Map Id Fun

-- | Function names bundled with their type
data Fun = Fun { funId :: Id, funFunType :: FunType }
  deriving Show

type Cxt = [Block]
type Block = [(Id, Type)]

newtype Label = L { theLabel :: Int }
  deriving (Eq, Enum, Show)

initSt :: St
initSt = St
  { cxt = [[]]
  , limitLocals   = 0
  , currentStack  = 0
  , limitStack    = 0
  , nextLabel     = L 0
  }
  
type Output = [String]
  
type Compile = RWS Sig Output St


builtin :: [(Id, Fun)]
builtin =
  [ (Id "printInt"   , Fun (Id "Runtime/printInt"   ) $ FunType Type_void [Type_int])
  ]

-- | Entry point.

compile
  :: String  -- ^ Class name.
  -> Program -- ^ Type-annotated program.
  -> String  -- ^ Generated jasmin source file content.
compile name _prg = header
  where
  header :: String
  header = unlines
    [ ";; BEGIN HEADER"
    , ""
    , ".class public " ++ name
    , ".super java/lang/Object"
    , ""
    , ".method public <init>()V"
    , "  .limit locals 1"
    , ""
    , "  aload_0"
    , "  invokespecial java/lang/Object/<init>()V"
    , "  return"
    , ""
    , ".end method"
    , ""
    , ".method public static main([Ljava/lang/String;)V"
    , "  .limit locals 1"
    , "  .limit stack  1"
    , ""
    , "  invokestatic " ++ name ++ "/main()I"
    , "  pop"
    , "  return"
    , ""
    , ".end method"
    , ""
    , ";; END HEADER"
    ]

isByte :: Integer -> Bool
isByte i = (-128) <= i && i <= 127

typeToString :: Type -> String
typeToString typ = case typ of
  Type_int -> "I"
  Type_void -> "V"
  Type_bool -> "Z" 


typelistToString :: [Type] -> String
typelistToString [] = []
typelistToString (Type_int:ts) = "I" ++ typelistToString ts
typelistToString (Type_bool:ts) = "Z" ++ typelistToString ts

class ToJVM a where
  toJVM :: a -> [Char]


instance ToJVM Fun where
  toJVM (Fun f (FunType ret params)) = (show f) ++ "(" ++ typelistToString params ++ ")" ++ (typeToString ret)  


instance ToJVM Label where
  toJVM (L i) = "L" ++ (show i)

instance ToJVM Code where
  toJVM code = case code of
    Store typ addr -> "istore " ++ (show addr)
    Load typ addr -> "iload " ++ (show addr)
    IConst i
     | i >= 0 && i <= 5 -> "iconst_" ++ (show i)
     | i == -1 -> "iconst_m1"
     | isByte i -> "bipush " ++ (show i)
     | otherwise -> "ldc " ++ (show i)
    Pop typ -> "pop"
    Return typ -> 
      case typ of
       Type_int -> "ireturn"
       Type_void -> "return"
    Add typ -> "iadd"
    Sub typ -> "isub"
    Mul typ -> "imul"
    Div typ -> "idiv"
    PostIncr typ addr byte -> "iinc " ++ (show addr) ++ (show byte)
    PreIncr typ addr byte -> "iinc " ++ (show addr) ++ (show byte)
    PostDecr typ addr byte ->"iinc " ++ (show addr) ++ (show byte)
    PreDecr typ addr byte -> "iinc " ++ (show addr) ++ (show byte)
    And typ  -> "iand"
    Or typ  -> "ior"
    Label l -> toJVM l ++ ":"
    Call fun -> "invokestatic " ++ toJVM fun
    Goto l -> "goto " ++ toJVM l
    IfZ l -> "ifeq " ++ toJVM l
    IfLt typ l -> "if_icmplt " ++ toJVM l
    IfGt typ l -> "if_icmpgt " ++ toJVM l
    IfLtEq typ l -> "if_icmple " ++ toJVM l
    IfGtEq typ l -> "if_icmpge " ++ toJVM l
    IfEq typ l -> "if_icmpeq " ++ toJVM l
    IfNEq typ l -> "if_icmpne " ++ toJVM l

newVar :: Id -> Type -> Compile ()
newVar id typ = undefined
  --(St (c:cs) limitL stack limitS nLabel) <- get
  --(id,typ) : c 

blank :: Compile ()
blank = undefined

inNewBlock :: Compile() -> Compile ()
inNewBlock = undefined

lookupVar :: Id -> Compile (Addr,Type)
lookupVar id = do
  (c:cs) <- gets cxt
  stack <- gets limitStack
  case lookup id c of
    (Just a) -> case a of
      typ -> return $ (stack,typ)
    otherwise -> lookupVarhelp cs id (stack-1)

lookupVarhelp :: Cxt -> Id -> Int -> Compile (Addr,Type)
lookupVarhelp (c:cs) id stack = case lookup id c of
  (Just a) -> case a of
    typ -> return $ (stack,typ) 
  otherwise -> lookupVarhelp cs id (stack-1)


compileFun :: Def -> Compile ()
compileFun def@(DFun t f args ss) = do
      -- function header
    tell [ "", ".method public static " ++ toJVM (Fun f $ funType def) ]
    
      -- prepare environment
    lab <- gets nextLabel
    put initSt{ nextLabel = lab }
    mapM_ (\ (ADecl t' x) -> newVar x t') args
    
      -- compile statements
    w <- grabOutput $ do
      mapM_ compileStm ss
    
      -- output limits
    ll <- gets limitLocals
    ls <- gets limitStack
    tell [ "  .limit locals " ++ show ll
         , "  .limit stack  " ++ show ls
         ]
    
      -- output code, indented by 2
    tell $ map (\ s -> if null s then s else "  " ++ s) w
    
      -- function footer
    tell [ "", ".end method"]


compileStm :: Stm -> Compile ()
compileStm s = do

  -- Printing a comment
  let top = stmTop s
  unless (null top) $ do
    tell $ map (";; " ++) $ lines top
    case s of 
      SDecls{} -> return();
      _ -> blank

  -- message for NYI
  let nyi = error $ "TODO: " ++ top

  case s of

    SInit t x e -> do
      compileExp e
      newVar x t
      (a, _) <- lookupVar x
      emit $ Store t a

    SExp  e -> do
      compileExp e
      emit $ Pop Type_int

    SReturn  e -> do
      compileExp e
      emit $ Return Type_int

    SBlock ss -> do
      inNewBlock $ mapM_ compileStm ss

    SWhile e s1 -> do
      start <- newLabel
      done  <- newLabel
      emit $ Label start
      compileExp e
      emit $ IfZ done
      inNewBlock $ compileStm s1
      emit $ Goto start
      emit $ Label done

    SIfElse exp stm1 stm2 -> do
      yes <- newLabel
      done <- newLabel
      compileExp exp
      emit $ IfZ yes
      inNewBlock $ compileStm stm1
      emit $ Goto done
      emit $ Label yes
      inNewBlock $ compileStm stm2
      emit $ Label done



    _ -> nyi


compileExp :: Exp -> Compile ()
compileExp e = do
  -- message for NYI
  let nyi = error $ "TODO: " ++ show e
  case e of
    EInt i -> do
      emit $ IConst i
    ETrue -> emit $ IConst 1
    EFalse -> emit $ IConst 0

    EId x -> do
      (a, t) <- lookupVar x
      emit $ Load t a

    EApp f es -> do
      mapM_ compileExp es
      sig <- ask
      let fun = fromMaybe (error "unbound function") $  Map.lookup f sig
      emit $ Call fun

    EPostIncr id -> do
      (addr,typ) <- lookupVar id
      emit $ Load typ addr
      emit $ PostIncr typ addr 1
    
    EPreIncr id -> do
      (addr,typ) <- lookupVar id
      emit $ PreIncr typ addr 1
      emit $ Load typ addr
    
    EPostDecr id -> do
      (addr,typ) <- lookupVar id
      emit $ Load typ addr
      emit $ PostDecr typ addr (-1)

    EPreDecr id -> do
      (addr,typ) <- lookupVar id
      emit $ PreDecr typ addr (-1)
      emit $ Load typ addr

    EPlus e1 e2 -> do
      compileExp e1
      compileExp e2
      emit $ Add Type_int

    EMinus e1 e2 -> do
      compileExp e1
      compileExp e2
      emit $ Sub Type_int

    ETimes e1 e2 -> do
      compileExp e1
      compileExp e2
      emit $ Mul Type_int
    
    EDiv e1 e2 -> do
      compileExp e1
      compileExp e2
      emit $ Div Type_int

    ELt    e1 e2 -> do
      compileExp e1
      compileExp e2
      yes  <- newLabel
      done <- newLabel
      emit $ IfLt Type_int yes
      emit $ IConst 0
      emit $ Goto done
      emit $ Label yes
      emit $ IConst 1
      emit $ Label done

    EGt e1 e2 -> do
      compileExp e1
      compileExp e2
      yes <- newLabel
      done <- newLabel
      emit $ IfGt Type_int yes
      emit $ IConst 0
      emit $ Goto done
      emit $ Label yes
      emit $ IConst 1
      emit $ Label done

    ELtEq e1 e2 -> do
      compileExp e1
      compileExp e2
      yes <- newLabel
      done <- newLabel
      emit $ IfLtEq Type_int yes
      emit $ IConst 0
      emit $ Goto done
      emit $ Label yes
      emit $ IConst 1
      emit $ Label done

    EGtEq e1 e2 -> do
      compileExp e1
      compileExp e2
      yes <- newLabel
      done <- newLabel
      emit $ IfGtEq Type_int yes
      emit $ IConst 0
      emit $ Goto done
      emit $ Label yes
      emit $ IConst 1
      emit $ Label done
    
    EEq e1 e2 -> do
      compileExp e1
      compileExp e2
      yes <- newLabel
      done <- newLabel
      emit $ IfEq Type_int yes
      emit $ IConst 0
      emit $ Goto done
      emit $ Label yes
      emit $ IConst 1
      emit $ Label done

    ENEq e1 e2 -> do
      compileExp e1
      compileExp e2
      yes <- newLabel
      done <- newLabel
      emit $ IfNEq Type_int yes
      emit $ IConst 0
      emit $ Goto done
      emit $ Label yes
      emit $ IConst 1
      emit $ Label done

    EAnd e1 e2 -> do
      compileExp e1
      compileExp e2
      yes <- newLabel
      done <- newLabel
      emit $ And Type_int
      emit $ IfZ yes
      emit $ IConst 1
      emit $ Goto done
      emit $ Label yes
      emit $ IConst 0
      emit $ Label done
    EOr e1 e2 -> do
      compileExp e1
      compileExp e2
      yes <- newLabel
      done <- newLabel
      emit $ Or Type_int
      emit $ IfZ yes
      emit $ IConst 1
      emit $ Goto done
      emit $ Label yes
      emit $ IConst 0
      emit $ Label done
  
    


    EAss x e1 -> do
      compileExp e1
      (a, t) <- lookupVar x
      emit $ Store t a
      emit $ Load t a

    _ -> nyi


-- * Instructions and emitting

type Addr = Int

data Code
  = Store Type Addr  -- ^ Store stack content of type @Type@ in local variable @Addr@.
  | Load  Type Addr  -- ^ Push stack content of type @Type@ from local variable @Addr@.

  | IConst Integer   -- ^ Put integer constant on the stack.
  | Pop Type         -- ^ Pop something of type @Type@ from the stack.
  | Return Type      -- ^ Return from method of type @Type@.
  
  | PostIncr Type Addr Integer
  | PreIncr Type Addr Integer
  | PostDecr Type Addr Integer
  | PreDecr Type Addr Integer

  | Add Type         -- ^ Add 2 top values of stack.
  | Sub Type         -- ^ Substracts 2 top values of stack
  | Mul Type         -- ^ Mulplicate 2 top values of stack
  | Div Type         -- ^ Divide 2 top values of stack 


  | Call Fun         -- ^ Call function.

  | Label Label      -- ^ Define label.
  | Goto Label       -- ^ Jump to label.
  | IfZ Label        -- ^ If top of stack is 0, jump to label.
  | IfLt Type Label  -- ^ If prev <  top, jump.
  | IfGt Type Label
  | IfLtEq Type Label
  | IfGtEq Type Label
  | IfEq Type Label
  | IfNEq Type Label

  | And Type
  | Or Type

  deriving (Show)

-- | Print a single instruction.  Also update stack limits
emit :: Code -> Compile ()
emit code = do
  tell[toJVM code] 
  case code of
    Store typ addr -> do 
      stack <- gets currentStack
      modify $ \ st -> st {currentStack = (stack-1)}
    Load typ addr -> do
      limit <- gets limitStack
      stack <- gets currentStack
      case limit == stack of
        True -> modify $ \ st -> st {limitStack = (limit+1)}  
      modify $ \ st -> st {currentStack = (stack+1)}
    IConst i -> do
      stack <- gets currentStack
      limit <- gets limitStack
      case limit == stack of
        True -> modify $ \ st -> st {limitStack = (limit+1)}
      modify $ \ st -> st {currentStack = (stack+1)}
    Pop typ -> do
      stack <- gets currentStack
      modify $ \ st -> st {currentStack = (stack-1)}
    Return typ -> do
      current <- gets currentStack 
      modify $ \ st -> st{currentStack = (current-1)}
    otherwise -> return ()


-- * Labels

newLabel :: Compile Label
newLabel = do
  l <- gets nextLabel
  modify $ \ st -> st { nextLabel = succ l }
  return $ l

-- | Print top part of statement (for comments)

stmTop :: Stm -> String
stmTop s =
  case s of
    SWhile e _ -> "while (" ++ printTree e ++ ")"
    SIfElse e _ _  -> "if (" ++ printTree e ++ ")"
    SBlock _   -> ""
    _ -> printTree s


-- * Auxiliary functions

grabOutput :: Compile () -> Compile Output
grabOutput m = do
  r <- ask
  s  <- get
  let ((), s', w) = runRWS m r s
  put s'
  return w

-- * Auxiliary functions

funType :: Def -> FunType
funType (DFun t _ args _) = FunType t $ map (\ (ADecl t' _) -> t') args
    