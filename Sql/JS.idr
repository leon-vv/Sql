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
objListToRecords : List (Obj "anonymous") -> {auto ip: schemaImp sch FromJSD} -> JS_IO (Maybe (List (Record sch)))
objListToRecords {sch} {ip} objs = do
    maybeRecs <- sequence $ map (objectToRecord {schema=sch} {fp=ip}) objs
    pure (sequence maybeRecs)

private
refToRecords : {auto ip: schemaImp sch FromJSD} -> JSRef -> JS_IO (Maybe (List (Record sch)))
refToRecords {ip} {sch} ref = do
  packed <- pack ref
  case packed of
    (JSObject "Array" ** array) => do
      maybeObjs <- arrayToObjects array
      (case maybeObjs of
        Just objs => objListToRecords {sch=sch} {ip=ip} objs
        Nothing => pure Nothing)
    _ => pure Nothing


runSelectQuery : {auto ip: schemaImp sch FromJSD}
    -> Select sch
    -> Pool
    -> Event (List (Record sch))
runSelectQuery query pool {ip} {sch} = do
    ref <- jscall "query(%0, %1)"
        (JSRef -> JSRef -> JS_IO JSRef) 
        pool (toRef {to=JSString} (show query))
    maybeRec <- fromEventReference {sch=[("rows", JSRef)]} ref
    case maybeRec of
         Just rec => refToRecords {ip=ip} {sch=sch} (rec .. "rows")
         Nothing => pure Nothing


runSelectQueryUnsafe : {auto ip: schemaImp sch FromJSD}
    -> Select sch
    -> Pool
    -> JS_IO (List (Record sch))
runSelectQueryUnsafe s p {ip} = do
  maybeList <- runSelectQuery {ip=ip} s p
  case maybeList of
    Just lst => pure lst
    Nothing => idris_crash "Sql.JS: Failed to run select query"



