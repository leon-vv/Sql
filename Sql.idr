module Sql

import Record

import Effects
import Data.List.Quantifiers

%access public export
%default total

maybeSchema : Schema -> Schema
maybeSchema sc = map (\(k, t) => (k, Maybe t)) sc

record Table (sc : Schema) where
  constructor MkTable
  name : String

data SqlType =
    Int
  | Bool
  | Text
  
data SqlTypeEq : Type -> Type where
  IntSql : SqlTypeEq Int
  BoolSql : SqlTypeEq Bool
  StringSql : SqlTypeEq String

getSqlType : SqlTypeEq t -> SqlType
getSqlType IntSql = Sql.Int
getSqlType BoolSql = Sql.Bool
getSqlType StringSql = Sql.Text

showSqlType : SqlTypeEq t -> t -> String
showSqlType IntSql v = show v
showSqlType BoolSql v = show v
showSqlType StringSql v = show v

data JoinType =
    Left
  | Right
  | Inner
  | Outer
  | LeftOuter
  | RightOuter
  | FullOuter

Show JoinType where
  show Left = "LEFT"
  show Right = "RIGHT"
  show Inner = "INNER"
  show Outer = "OUTER"
  show LeftOuter = "LEFT OUTER"
  show RightOuter = "RIGHT OUTER"
  show FullOuter = "FULL OUTER"

mutual

  data Join : Schema -> Schema -> Type where
    JoinClause : JoinType
      -> Table tb_sc
      -> {auto ss: schemaImp tb_sc SqlTypeEq}
      -> (on : Expr acc Bool)
      -> Join tb_sc acc
  
  AnyJoin : Type
  AnyJoin = DPair Schema (\sc => (DPair Schema (Join sc)))

  asAny : Join tb_sc acc -> AnyJoin
  asAny join = (tb_sc ** (acc ** join))

  correctJoin : (baseTable : Schema) -> AnyJoin -> Type
  correctJoin bt (tb_sc ** (acc ** join)) = SubList acc (bt ++ tb_sc)

  correctJoins : List AnyJoin -> (baseTable : Schema) -> Type
  correctJoins joins bt = All (correctJoin bt) joins

  availableColumns : List AnyJoin -> Schema
  availableColumns lst = concat $ map (\(tb_sc ** _) => tb_sc) lst

  data Select : Schema -> Type where
    SelectQuery :
      (target: Schema)
      -> (from : Table sc)
      -> (where_ : Expr sc1 Bool)
	    -> (joins : List AnyJoin)

      {- Proofs that the columns used are valid -}
      -> {auto ss: schemaImp sc SqlTypeEq}
	    -> {auto cj: correctJoins joins sc}
      -> {auto sl: SubList (target ++ sc1) sc}

      -> Select target

  data Expr : Schema -> SqlType -> Type where
	  {- Simple expressions... -} 
    Const : t -> {auto sp: SqlTypeEq t} -> Expr [] (getSqlType sp)
    Col : {auto sp: SqlTypeEq t} -> (col: String)  -> Expr [(col, t)]  (getSqlType sp)

    {- ... come together to be powerful -}
    Concat : Expr sc1 Text -> Expr sc2 Text -> Expr (sc1 ++ sc2) Text

    Is : Expr sc1 t -> Expr sc2 t -> Expr (sc1 ++ sc2) Bool
    And : Expr sc1 Bool -> Expr sc2 Bool -> Expr (sc1 ++ sc2) Bool
    Or : Expr sc1 a -> Expr sc2 a -> Expr (sc1 ++ sc2) a

    InSubQuery : {auto sp: SqlTypeEq t} -> Expr sc (getSqlType sp) -> Select [(k, t)] -> Expr ((k, t)::sc) Bool


joinStr : List String -> (sep : String) -> String
joinStr Nil _ = ""
joinStr [s] _ = s
joinStr (s::rest) sep = s ++ sep ++ (joinStr rest sep)

private
wp : String -> String
wp s = "(" ++ s ++ ")"

mutual

  export
  partial
  exprToString : {t1:SqlType} -> Expr acc t1 -> String
  exprToString (Const c {sp}) = showSqlType sp c
  exprToString (Col c) = c
  exprToString (Concat x y) = "CONCAT( " ++ (ets x) ++ ", " ++ (ets y) ++ ")"
  exprToString (Is x y) = wpe x  ++ " = " ++ wpe y
  exprToString (And x y) = wpe x ++ " AND " ++ wpe y
  exprToString (Or x y) = wpe x ++ " OR " ++ wpe y
  exprToString (InSubQuery x s) = wpe x ++ " IN " ++ wp (selectToString s)
    
  private
  partial
  ets : Expr acc type -> String
  ets = exprToString

  private
  partial
  wpe : Expr acc type -> String
  wpe = wp . ets

  export
  partial
  selectToString : Select sc -> String
  selectToString (SelectQuery sc f w j) = 
    "SELECT "  ++ targetToString sc ++ "\n" ++
    "FROM " ++ fromToString f ++ "\n" ++
    "WHERE " ++ exprToString w ++ "\n" ++
    (joinStr (map joinToString j) "\n")
      where
        targetToString : Schema -> String
        targetToString sch = joinStr (map fst sch) ", "

        fromToString : Table sch -> String
        fromToString = name

        partial
        joinToString : AnyJoin -> String
        joinToString (_ ** (_ ** (JoinClause ty tb on))) =
          show ty ++ " JOIN " ++ (name tb) ++ " ON " ++ ets on

