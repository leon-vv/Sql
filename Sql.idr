module Sql

import Record
import Record.JS

import Effects
import Data.List.Quantifiers

%default total

public export
data SqlType =
    Int
  | Bool
  | Text
  
public export
data SqlTypeEq : Type -> Type where
  IntSql : SqlTypeEq Int
  BoolSql : SqlTypeEq Bool
  StringSql : SqlTypeEq String

export
record Table (sch : Schema) where
  constructor MkTablePriv
  name : String

public export
MkTable : String -> (sch: Schema) -> {sp : schemaImp sch SqlTypeEq} -> Table sch
MkTable name sch = MkTablePriv name

public export
getSqlType : SqlTypeEq t -> SqlType
getSqlType IntSql = Sql.Int
getSqlType BoolSql = Sql.Bool
getSqlType StringSql = Sql.Text

public export
showSqlType : SqlTypeEq t -> t -> String
showSqlType IntSql v = show v
showSqlType BoolSql v = show v
showSqlType StringSql v = show v

public export
data JoinType =
    Left
  | Right
  | Inner
  | Outer
  | LeftOuter
  | RightOuter
  | FullOuter

public export
Show JoinType where
  show Left = "LEFT"
  show Right = "RIGHT"
  show Inner = "INNER"
  show Outer = "OUTER"
  show LeftOuter = "LEFT OUTER"
  show RightOuter = "RIGHT OUTER"
  show FullOuter = "FULL OUTER"

mutual

  public export
  data Join : Schema -> Schema -> Type where
    JoinClause : JoinType
      -> Table tb_sc
      -> {auto ss: schemaImp tb_sc SqlTypeEq}
      -> (on : Expr acc Bool)
      -> Join acc tb_sc

  -- Fields accessed and fields brought into scope
  public export
  data Joins : Schema -> Schema -> Type where
    Nil : Joins [] []
    Cons : Join acc sch -> Joins accs schs -> Joins (acc++accs) (sch++schs)

  public export
  data Select : Schema -> Type where
    SelectQuery :
      (target: Schema)
      -> (from : Table baseTable)
      -> (where_ : Expr accExpr Bool)
	    -> (joins : Joins accJoins joined)

      {- Proofs that the columns used are valid
      The fields that are in the target, accessed by the where
      expression and the fields accessed by the joins should be
      a sublist of the fields in the 'from' table and the tables
      joined in -}
      -> {auto sl: SubList (target ++ accExpr ++ accJoins)
            (baseTable ++ joined)}
      -> {auto ip: schemaImp sch FromJSD}

      -> Select target

  -- The first argument to Expr is a schema of all the 
  -- fields that are being used by the expression.
  -- The second argument is the result type of the expression.
  public export
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

 
-- Join string using separator
private
joinStr : List String -> (sep : String) -> String
joinStr Nil _ = ""
joinStr [s] _ = s
joinStr (s::rest) sep = s ++ sep ++ (joinStr rest sep)

-- Within parentheses
private
wp : String -> String
wp s = "(" ++ s ++ ")"

mutual

  public export
  Show (Join a b) where
    show (JoinClause type tb expr) = show type ++ " JOIN " ++ (name tb) ++ " ON " ++ assert_total (show expr)

  public export
  Show (Joins _ _) where
    show Nil = ""
    show (Cons head tail) = show head ++ "\n" ++ show tail

  Show (Expr _ _) where
    show (Const c {sp}) = showSqlType sp c
    show (Col c) = c
    show (Concat x y) = "CONCAT( " ++ (show x) ++ ", " ++ (show y) ++ ")"
    show (Is x y) = wpe x  ++ " = " ++ wpe y
    show (And x y) = wpe x ++ " AND " ++ wpe y
    show (Or x y) = wpe x ++ " OR " ++ wpe y
    show (InSubQuery x s) = wpe x ++ " IN " ++ wp (show s)

  -- Expression within parenthese
  private
  wpe : Expr _ _ -> String
  wpe = assert_total (wp . show)

  public export
  Show (Select sch) where
    show (SelectQuery sch f w j) = 
      "SELECT "  ++ targetToString sch ++ "\n" ++
      "FROM " ++ fromToString f ++ "\n" ++
      "WHERE " ++ show w ++ "\n" ++ show j
        where
          targetToString : Schema -> String
          targetToString sch = joinStr (map fst sch) ", "

          fromToString : Table _ -> String
          fromToString = name
