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

escapeLiteral : String -> String
escapeLiteral =
  unsafePerformIO .
    jscall "escapeLiteral(%0)" (String -> JS_IO String)

escapeIdentifier : String -> String
escapeIdentifier =
  unsafePerformIO .
    jscall "escapeIdentifier(%0)" (String -> JS_IO String)
    
-- Join string using separator
joinStr : List String -> (sep : String) -> String
joinStr Nil _ = ""
joinStr [s] _ = s
joinStr (s::rest) sep = s ++ sep ++ (joinStr rest sep)

-- Within parentheses
wp : String -> String
wp s = "(" ++ s ++ ")"

showSqlType : SqlTypeEq t -> t -> String
showSqlType IntSql v = show v
showSqlType BoolSql v = show v
showSqlType StringSql v = escapeLiteral v

mutual

  toList : NamedExprs _ _ -> List (String, String)
  toList ExprsNil = []
  toList (ExprsCons k expr rest) = (escapeIdentifier k, show expr) :: toList rest


  showWithSeparator : NamedExprs _ _ -> String -> String
  showWithSeparator nexprs sep =
    joinStr
      (map (\(k, v) => v ++ sep ++ k) $ toList $ nexprs) 
      ", "

  -- Show as in a select query
  export
  Show (NamedExprs _ _) where
    show nexprs = showWithSeparator nexprs " AS "
 
  export
  Show (Join a b) where
    show (JoinClause type tb expr) =
      show type ++ " JOIN " ++
        escapeIdentifier (name tb) ++ " ON " ++ 
        assert_total (show expr)
    
  export
  Show (Joins _ _) where
    show Nil = ""
    show (Cons head tail) = show head ++ "\n" ++ show tail


  export 
  Show (Expr _ _) where
    show (Const c {sp}) = showSqlType sp c
    show (Col c) = escapeIdentifier c
    show (Concat x y) = "CONCAT( " ++ (show x) ++ ", " ++ (show y) ++ ")"
    show (Is x y) = wpe x  ++ " = " ++ wpe y
    show (And x y) = wpe x ++ " AND " ++ wpe y
    show (Or x y) = wpe x ++ " OR " ++ wpe y
    show (InSubQuery x s) = wpe x ++ " IN " ++ wp (show s)
  
  -- Expression within parenthese
  private
  wpe : Expr _ _ -> String
  wpe = assert_total (wp . show)

  export
  Show (Select target) where
    show (SelectQuery exprs f w j) = 
      "SELECT "  ++ show exprs ++ "\n" ++
      "FROM " ++ escapeIdentifier (name f) ++ "\n" ++
      "WHERE " ++ show w ++ "\n" ++ show j
  
export
Show Update where
  show (UpdateQuery tbl nexprs w) =
    let assign = showWithSeparator nexprs " = "
    in 
      "UPDATE " ++ name tbl ++ "\n" ++
      "SET (" ++ assign ++ ")\n" ++
      "WHERE " ++ show w

export
Show Delete where
  show (DeleteQuery tbl w) =
    "DELETE FROM " ++ name tbl ++ "\n" ++
    "WHERE " ++ show w

export
Show Insert where
  show (InsertQuery tbl nexprs) =
    let strLst = toList nexprs
    in let cols = map fst strLst
    in let vals = map snd strLst
    in
      "INSERT INTO " ++ name tbl ++ "\n" ++
      "(" ++ joinStr cols ", " ++ ")\n" ++
      "VALUES (" ++ joinStr vals ", " ++ ")\n"

