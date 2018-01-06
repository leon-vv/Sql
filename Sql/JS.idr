module Sql.JS

import Sql

import Event

import Record
import Record.JS

import IdrisScript
import IdrisScript.Arrays

%default total

public export
Obj : String -> Type
Obj s = JSValue (JSObject s)

private
toRef : ToJS a to => a -> JSRef
toRef {to} a = unpack (toJS {to=to} a)

public export
Pool : Type
Pool = JSRef

private
undefined : JSRef
undefined = unsafePerformIO (jscall "undefined" (JS_IO JSRef))

public export
makePool : {default "" user: String}
        -> {default "" host: String}
        -> {default "" database: String}
        -> {default "" password: String} -> JS_IO Pool
makePool {user} {host} {database} {password} =
  jscall "makePool(%0, %1, %2, %3)"
    (JSRef -> JSRef -> JSRef -> JSRef -> JS_IO JSRef)
    (mkRef database) (mkRef user) (mkRef host) (mkRef password)
  where mkRef : String -> JSRef
        mkRef "" = undefined
        mkRef s = toRef {to=JSString} s

private
arrayToObjects : JSValue JSArray -> JS_IO (Maybe (List (Obj "anonymous")))
arrayToObjects arr = (do
      ra <- reverse arr 
      l <- length ra
      withIndex ra Z l [])
        where
          withIndex : JSValue JSArray -> Nat -> Nat -> List (Obj "anonymous") -> JS_IO (Maybe (List (Obj "anonymous")))
          withIndex arr idx Z lst = pure (Just lst)
          withIndex arr idx (S l) lst = do
            elem <- arr !! l
            case elem of
              Just (JSObject "anonymous" ** v) => withIndex arr (idx+1) l (v::lst)
              _ => pure Nothing

private
objListToRecords : List (Obj "anonymous") -> {auto ip: SchemaImp sch FromJSD} -> JS_IO (Maybe (List (Record sch)))
objListToRecords {sch} {ip} objs = do
    maybeRecs <- sequence $ map (objectToRecord {schema=sch} {fp=ip}) objs
    pure (sequence maybeRecs)

private
refToRecords : {auto ip: SchemaImp sch FromJSD} -> JSRef -> JS_IO (Maybe (List (Record sch)))
refToRecords {ip} {sch} ref = do
  packed <- pack ref
  case packed of
    (JSObject "Array" ** array) => do
      maybeObjs <- arrayToObjects array
      (case maybeObjs of
        Just objs => objListToRecords {sch=sch} {ip=ip} objs
        Nothing => pure Nothing)
    _ => pure Nothing

private
partial
refToRecordsUnsafe : {auto ip: SchemaImp sch FromJSD} -> JSRef -> JS_IO (List (Record sch))
refToRecordsUnsafe {ip} {sch} ref = do (Just lst) <- refToRecords {ip=ip} {sch=sch} ref
                                       pure lst

private
partial
toRecord : {ip: SchemaImp sch FromJSD} -> Record [("rows", JSRef)] -> JS_IO (List (Record sch))
toRecord {ip} {sch} rec = refToRecordsUnsafe {ip=ip} {sch=sch} (rec .. "rows")

export
partial
runSelectQuery : {auto ip: SchemaImp sch FromJSD}
    -> Select sch
    -> Pool
    -> JS_IO (Event (List (Record sch)))
runSelectQuery {ip} {sch} query pool = (do
    ref <- jscall "query(%0, %1)"
        (JSRef -> JSRef -> JS_IO JSRef) 
        pool (toRef {to=JSString} (show query))
    event <- fromGeneratorReference {sch=[("rows", JSRef)]} ref
    pure (mapIO (toRecord {ip=ip} {sch=sch}) event))
      

