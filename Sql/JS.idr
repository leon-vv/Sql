module Sql.JS

import Sql
import Event
import Record
import FerryJS

import Effects

%default total

export
DBConnection : Type
DBConnection = Ptr

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

toIdrisExprs : NamedExprs acc res -> ToIdris (Record res)
toIdrisExprs ExprNil = toIdrisRecNil
toIdrisExprs (ExprCons {t} k ex rest) =
  toIdrisRecord (toIdrisSql t) (toIdrisExprs rest)


partial
toRecordList : ToIdris (Record sch) -> Record [("rows", Ptr)] -> List (Record sch)
toRecordList (ToIdrisFn f) {sch} rec =
  let ref = rec .. "rows"
  in (toIdrisUnsafe {to=List (Record sch)} ref)

runQuery : Ptr -> String -> JS_IO Ptr
runQuery pool query = jscall "query(%0, %1)" (Ptr -> Ptr -> JS_IO Ptr) pool (toJS query)

export
SelectQueryResult : Schema -> Type
SelectQueryResult sch = (Ptr, Select sch)

export
partial
runSelectQuery : Select sch
    -> DBConnection
    -> JS_IO (SelectQueryResult sch)
runSelectQuery query conn = (`MkPair` query) <$> runQuery conn (show query)

export
waitSelectResult : SelectQueryResult sch -> Event Single (List (Record sch))
waitSelectResult (ptr, (SelectQuery {r} {res} exprs _ _ _)) =
  let schema = [("rows", List (Record (r::res)))]
  in let ti = toIdrisList (toIdrisExprs exprs)
  in let ev = assert_total $ ptrToEvent {to=Record schema} Node (pure ptr) "" 
  in map (.. "rows") ev

export
RowCountResult : Type
RowCountResult = Ptr

export
waitRowCountResult : RowCountResult -> Event Single Int
waitRowCountResult ptr = 
  let ev = assert_total $
            ptrToEvent {to=Record [("rowCount", Int)]} Node (pure ptr) ""
  in map (.. "rowCount") ev

rowCountQuery : Show a => a -> DBConnection -> JS_IO RowCountResult
rowCountQuery query conn = runQuery conn (show query)

export
partial
runUpdateQuery : Update -> DBConnection -> JS_IO RowCountResult
runUpdateQuery = rowCountQuery

export
partial
runDeleteQuery : Delete -> DBConnection -> JS_IO RowCountResult
runDeleteQuery = rowCountQuery

export
partial
runInsertQuery : Insert -> DBConnection -> JS_IO RowCountResult
runInsertQuery = rowCountQuery
















