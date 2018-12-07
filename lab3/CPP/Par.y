-- This Happy file was machine-generated by the BNF converter
{
{-# OPTIONS_GHC -fno-warn-incomplete-patterns -fno-warn-overlapping-patterns #-}
module CPP.Par where
import CPP.Abs
import CPP.Lex
import CPP.ErrM

}

%name pProgram Program
%name pDef Def
%name pListDef ListDef
%name pArg Arg
%name pListArg ListArg
%name pStm Stm
%name pListStm ListStm
%name pExp15 Exp15
%name pExp14 Exp14
%name pExp13 Exp13
%name pExp12 Exp12
%name pExp11 Exp11
%name pExp9 Exp9
%name pExp8 Exp8
%name pExp4 Exp4
%name pExp3 Exp3
%name pExp2 Exp2
%name pExp Exp
%name pExp1 Exp1
%name pExp5 Exp5
%name pExp6 Exp6
%name pExp7 Exp7
%name pExp10 Exp10
%name pListExp ListExp
%name pType Type
%name pListId ListId
-- no lexer declaration
%monad { Err } { thenM } { returnM }
%tokentype {Token}
%token
  '!=' { PT _ (TS _ 1) }
  '&&' { PT _ (TS _ 2) }
  '(' { PT _ (TS _ 3) }
  ')' { PT _ (TS _ 4) }
  '*' { PT _ (TS _ 5) }
  '+' { PT _ (TS _ 6) }
  '++' { PT _ (TS _ 7) }
  ',' { PT _ (TS _ 8) }
  '-' { PT _ (TS _ 9) }
  '--' { PT _ (TS _ 10) }
  '/' { PT _ (TS _ 11) }
  ';' { PT _ (TS _ 12) }
  '<' { PT _ (TS _ 13) }
  '<=' { PT _ (TS _ 14) }
  '=' { PT _ (TS _ 15) }
  '==' { PT _ (TS _ 16) }
  '>' { PT _ (TS _ 17) }
  '>=' { PT _ (TS _ 18) }
  'bool' { PT _ (TS _ 19) }
  'double' { PT _ (TS _ 20) }
  'else' { PT _ (TS _ 21) }
  'false' { PT _ (TS _ 22) }
  'if' { PT _ (TS _ 23) }
  'int' { PT _ (TS _ 24) }
  'return' { PT _ (TS _ 25) }
  'true' { PT _ (TS _ 26) }
  'void' { PT _ (TS _ 27) }
  'while' { PT _ (TS _ 28) }
  '{' { PT _ (TS _ 29) }
  '||' { PT _ (TS _ 30) }
  '}' { PT _ (TS _ 31) }

L_integ  { PT _ (TI $$) }
L_doubl  { PT _ (TD $$) }
L_Id { PT _ (T_Id $$) }


%%

Integer :: { Integer } : L_integ  { (read ( $1)) :: Integer }
Double  :: { Double }  : L_doubl  { (read ( $1)) :: Double }
Id    :: { Id} : L_Id { Id ($1)}

Program :: { Program }
Program : ListDef { CPP.Abs.PDefs (reverse $1) }
Def :: { Def }
Def : Type Id '(' ListArg ')' '{' ListStm '}' { CPP.Abs.DFun $1 $2 $4 (reverse $7) }
ListDef :: { [Def] }
ListDef : {- empty -} { [] } | ListDef Def { flip (:) $1 $2 }
Arg :: { Arg }
Arg : Type Id { CPP.Abs.ADecl $1 $2 }
ListArg :: { [Arg] }
ListArg : {- empty -} { [] }
        | Arg { (:[]) $1 }
        | Arg ',' ListArg { (:) $1 $3 }
Stm :: { Stm }
Stm : Exp ';' { CPP.Abs.SExp $1 }
    | Type ListId ';' { CPP.Abs.SDecls $1 $2 }
    | Type Id '=' Exp ';' { CPP.Abs.SInit $1 $2 $4 }
    | 'return' Exp ';' { CPP.Abs.SReturn $2 }
    | 'while' '(' Exp ')' Stm { CPP.Abs.SWhile $3 $5 }
    | '{' ListStm '}' { CPP.Abs.SBlock (reverse $2) }
    | 'if' '(' Exp ')' Stm 'else' Stm { CPP.Abs.SIfElse $3 $5 $7 }
ListStm :: { [Stm] }
ListStm : {- empty -} { [] } | ListStm Stm { flip (:) $1 $2 }
Exp15 :: { Exp }
Exp15 : 'true' { CPP.Abs.ETrue }
      | 'false' { CPP.Abs.EFalse }
      | Integer { CPP.Abs.EInt $1 }
      | Double { CPP.Abs.EDouble $1 }
      | Id { CPP.Abs.EId $1 }
      | '(' Exp ')' { $2 }
Exp14 :: { Exp }
Exp14 : Id '(' ListExp ')' { CPP.Abs.EApp $1 $3 }
      | Id '++' { CPP.Abs.EPostIncr $1 }
      | Id '--' { CPP.Abs.EPostDecr $1 }
      | Exp15 { $1 }
Exp13 :: { Exp }
Exp13 : '++' Id { CPP.Abs.EPreIncr $2 }
      | '--' Id { CPP.Abs.EPreDecr $2 }
      | Exp14 { $1 }
Exp12 :: { Exp }
Exp12 : Exp12 '*' Exp13 { CPP.Abs.ETimes $1 $3 }
      | Exp12 '/' Exp13 { CPP.Abs.EDiv $1 $3 }
      | Exp13 { $1 }
Exp11 :: { Exp }
Exp11 : Exp11 '+' Exp12 { CPP.Abs.EPlus $1 $3 }
      | Exp11 '-' Exp12 { CPP.Abs.EMinus $1 $3 }
      | Exp12 { $1 }
Exp9 :: { Exp }
Exp9 : Exp10 '<' Exp10 { CPP.Abs.ELt $1 $3 }
     | Exp10 '>' Exp10 { CPP.Abs.EGt $1 $3 }
     | Exp10 '<=' Exp10 { CPP.Abs.ELtEq $1 $3 }
     | Exp10 '>=' Exp10 { CPP.Abs.EGtEq $1 $3 }
     | Exp10 { $1 }
Exp8 :: { Exp }
Exp8 : Exp9 '==' Exp9 { CPP.Abs.EEq $1 $3 }
     | Exp9 '!=' Exp9 { CPP.Abs.ENEq $1 $3 }
     | Exp9 { $1 }
Exp4 :: { Exp }
Exp4 : Exp4 '&&' Exp5 { CPP.Abs.EAnd $1 $3 } | Exp5 { $1 }
Exp3 :: { Exp }
Exp3 : Exp3 '||' Exp4 { CPP.Abs.EOr $1 $3 } | Exp4 { $1 }
Exp2 :: { Exp }
Exp2 : Id '=' Exp2 { CPP.Abs.EAss $1 $3 } | Exp3 { $1 }
Exp :: { Exp }
Exp : Exp1 { $1 }
Exp1 :: { Exp }
Exp1 : Exp2 { $1 }
Exp5 :: { Exp }
Exp5 : Exp6 { $1 }
Exp6 :: { Exp }
Exp6 : Exp7 { $1 }
Exp7 :: { Exp }
Exp7 : Exp8 { $1 }
Exp10 :: { Exp }
Exp10 : Exp11 { $1 }
ListExp :: { [Exp] }
ListExp : {- empty -} { [] }
        | Exp { (:[]) $1 }
        | Exp ',' ListExp { (:) $1 $3 }
Type :: { Type }
Type : 'bool' { CPP.Abs.Type_bool }
     | 'int' { CPP.Abs.Type_int }
     | 'double' { CPP.Abs.Type_double }
     | 'void' { CPP.Abs.Type_void }
ListId :: { [Id] }
ListId : Id { (:[]) $1 } | Id ',' ListId { (:) $1 $3 }
{

returnM :: a -> Err a
returnM = return

thenM :: Err a -> (a -> Err b) -> Err b
thenM = (>>=)

happyError :: [Token] -> Err a
happyError ts =
  Bad $ "syntax error at " ++ tokenPos ts ++ 
  case ts of
    [] -> []
    [Err _] -> " due to lexer error"
    _ -> " before " ++ unwords (map (id . prToken) (take 4 ts))

myLexer = tokens
}

