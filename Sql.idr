module Sql

import Record
import Record.JS

import FerryJS

import Effects
import Data.List.Quantifiers


%include Node "./Sql/runtime.js"

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

public export
getSqlType : SqlTypeEq t -> SqlType
getSqlType IntSql = Sql.Int
getSqlType BoolSql = Sql.Bool
getSqlType StringSql = Sql.Text

public export
getIdrisType : SqlType -> Type
getIdrisType Sql.Int = Int
getIdrisType Sql.Bool = Bool
getIdrisType Sql.String = String

export
record Table (sch : Schema) where
  constructor MkTablePriv
  namePriv : String

export
name : Table sch -> String
name = namePriv

export
MkTable : {auto ip: SchemaImp sch SqlTypeEq}
      -> String
      -> Table sch
MkTable name = MkTablePriv name

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
      -> (on : Expr acc Bool)
      -> Join acc tb_sc

  -- The first schema contains the fields accessed
  -- while the second schema contains the fields brought
  -- into scope by the join.
  public export
  data Joins : Schema -> Schema -> Type where
    Nil : Joins [] []
    Cons : Join acc sch -> Joins accs schs -> Joins (acc++accs) (sch++schs)

  public export
  data Select : Schema -> Type where
    SelectQuery :
      NamedExprs accs (r::res) -- Not empty by pattern match
      -> (from : Table baseTable)
      -> (where_ : Expr accWhere Bool)
	    -> (joins : Joins accJoins joined)
      {- Proofs that the columns used are valid
      The fields that are in the target, accessed by the where
      expression and the fields accessed by the joins should be
      a sublist of the fields in the 'from' table and the tables
      joined in -}
      -> {auto sl: SubList
            (accs ++ accWhere ++ accJoins)
            (baseTable ++ joined)}
      -> Select (r::res)

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

  -- First schema contains the fields accessed.
  -- The second schema contains the result of the query.
  public export
  data NamedExprs : Schema -> Schema -> Type where
    ExprsNil : NamedExprs [] []
    ExprsCons : (k: String) 
        -> Expr acc t
        -> NamedExprs accs res
        -> NamedExprs (acc ++ accs) ((k, getIdrisType t)::res)

  resultFromJS : NamedExprs acc res -> FromJS (Record res)
  resultFromJS ExprsNil = fromJSRecNil
  resultFromJS (ExprsCons {t} k ex rest) =
    (let fromJSToRest = resultFromJS rest
    in fromJSRecord (fromJS t) fromJSToRest)
      where fromJS : (t: SqlType) -> FromJS (getIdrisType t)
            fromJS Sql.Int = fromJSToInt
            fromJS Sql.Bool = fromJSToBool
            fromJS Sql.Text = fromJSToString


public export
data Update : Type where
  UpdateQuery : ToJS (Record updateSch) =>
    (table: Table tableSch)
    -> NamedExprs accs _ -- Not empty by pattern match
    -> (where_ : Expr whereAccs Bool)
    -> {auto sl: SubList (asccs ++ whereAccs) tableSch}
    -> Update

public export
data Delete : Type where
  DeleteQuery :
    (table: Table tableSch)
    -> (where_: Expr accExpr Bool)
    -> {auto sl: SubList accExpr tableSch}
    -> Delete

public export
data Insert : Type where
  InsertQuery :
    (table: Table tableSch)
    -> NamedExprs accs _
    -> {auto sl: SubList accs tableSch}
    -> Insert

