module Sql.JS

import Sql

import Event

import Record
import Record.JS

import FerryJS

import Effects

%default total

public export
DBConnection : Type
DBConnection = Ptr

private
undefined : Ptr
undefined = unsafePerformIO (jscall "undefined" (JS_IO Ptr))

export
newConnection : {default "" user: String}
        -> {default "" host: String}
        -> {default "" database: String}
        -> {default "" password: String} -> JS_IO DBConnection
newConnection {user} {host} {database} {password} =
  jscall "makePool(%0, %1, %2, %3)"
    (Ptr -> Ptr -> Ptr -> Ptr -> JS_IO Ptr)
    (mkRef database) (mkRef user) (mkRef host) (mkRef password)
  where mkRef : String -> Ptr
        mkRef "" = undefined
        mkRef s = toJS s

toRecordList : FromJS (Record sch) -> Record [("rows", Ptr)] -> List (Record sch)
toRecordList (FromJSFun f) {sch} rec = let ref = rec .. "rows"
                                       in (fromJS {to=List (Record sch)} ref)



-- Escape literal
private
el : String -> String
el = unsafePerformIO . jscall "escapeLiteral(%0)" (String -> JS_IO String)

-- Escape identifier
private
ei : String -> String
ei = unsafePerformIO . jscall "escapeIdentifier(%0)" (String -> JS_IO String)
    
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


private
showSqlType : SqlTypeEq t -> t -> String
showSqlType IntSql v = show v
showSqlType BoolSql v = show v
showSqlType StringSql v = el v


mutual

  public export
  Show (Join a b) where
    show (JoinClause type tb expr) = show type ++ " JOIN " ++ ei (name tb) ++ " ON " ++ assert_total (show expr)

  public export
  Show (Joins _ _) where
    show Nil = ""
    show (Cons head tail) = show head ++ "\n" ++ show tail

  Show (Expr _ _) where
    show (Const c {sp}) = showSqlType sp c
    show (Col c) = ei c
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
  Show (Select target) where
    show (SelectQuery {target} f w j) = 
      "SELECT "  ++ targetToString target ++ "\n" ++
      "FROM " ++ fromToString f ++ "\n" ++
      "WHERE " ++ show w ++ "\n" ++ show j
        where
          targetToString : Schema -> String
          targetToString sch = joinStr (map fst sch) ", "

          fromToString : Table _ -> String
          fromToString = name
  
  public export
  Show Update where
    show (UpdateQuery {ip} tbl rec w) =
      let assign = showRecordAssignment rec {ip=ip}
      in 
        "UPDATE " ++ name tbl ++ "\n" ++
        "SET (" ++ assign ++ ")\n" ++
        "WHERE " ++ show w

  public export
  Show Delete where
    show (DeleteQuery tbl w) =
      "DELETE FROM " ++ name tbl ++ "\n" ++
      "WHERE " ++ show w

  public export
  Show Insert where
    show (InsertQuery {ip} tbl rec) =
      let strLst = toStringList {ip=ip} rec
      in let cols = map fst strLst
      in let vals = map snd strLst
      in
        "INSERT INTO " ++ name tbl ++ "\n" ++
        "(" ++ joinStr cols ", " ++ ")\n" ++
        "VALUES (" ++ joinStr vals ", " ++ ")\n"


export
partial
runSelectQuery : Select sch
    -> DBConnection
    -> JS_IO (Event (List (Record sch)))
runSelectQuery query@(SelectQuery {target} {fjs} _ _ _) pool = do
  ref <- jscall "query(%0, %1)"
      (Ptr -> Ptr -> JS_IO Ptr) 
      pool (toJS (show query))
  event <- fromGeneratorReference {sch=[("rows", Ptr)]} ref
  pure (map (toRecordList fjs {sch=target}) event)
 














