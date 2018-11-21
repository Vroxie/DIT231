module TypeChecker where

import Control.Monad

import Data.Map (Map)
import qualified Data.Map as Map

import CPP.Abs
import CPP.Print
import CPP.ErrM

type Env = (Sig,[Context])
type Sig = Map Id ([Type],Type)
type Context = Map Id Type

typecheck :: Program -> Err ()
typecheck p = return ()

lookupVar :: Env -> Id -> Err Type
lookupVar (_,[]) id = fail $ "Cannot resolve symbol " ++ (show id)
lookupVar (sig,context) id = case Map.lookup id (head context) of
        (Just a) -> return a
        otherwise -> lookupVar (sig, tail context) id

lookupFun :: Env -> Id -> Err ([Type], Type)
lookupFun (sig,context) id = case Map.lookup id sig of
        (Just a) -> return a
        otherwise -> fail $ "Cannot resolve symbol " ++ (show id)


updateVar :: Env -> Id -> Err Env
updateVar (sig,context) id = case updateHelp context id of
        (False,_) -> fail $ "cannot resolve symbol " ++ (show id)
        (True, ctx) -> return $ (sig, ctx)

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