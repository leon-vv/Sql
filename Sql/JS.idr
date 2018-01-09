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
      

