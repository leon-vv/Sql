module Sql.JS

import Sql

import Record
import Record.JS

import IdrisScript
import IdrisScript.Arrays

%default total

public export
Obj : Type
Obj = JSValue (JSObject "Object")

private
arrayToObjects : JSValue JSArray -> JS_IO (Maybe (List Obj))
arrayToObjects arr = (do
      ra <- reverse arr 
      l <- length ra
      withIndex ra Z l [])
        where
          withIndex : JSValue JSArray -> Nat -> Nat -> List Obj -> JS_IO (Maybe (List Obj))
          withIndex arr idx Z lst = pure (Just lst)
          withIndex arr idx (S l) lst = do
            elem <- arr !! l
            case elem of
              Just (JSObject "Object" ** v) => withIndex arr (idx+1) l (v::lst)
              _ => pure Nothing

private
objListToRecords : List Obj -> {auto ip: schemaImp sch FromJSD} -> JS_IO (Maybe (List (Record sch)))
objListToRecords {sch} {ip} objs = do
    maybeRecs <- sequence $ map (objectToRecord {schema=sch} {fp=ip}) objs
    pure (sequence maybeRecs)

runSelectQuery : Select sch
    -> {auto ip: schemaImp sch FromJSD}
    -> JS_IO (Maybe (List (Record sch)))
runSelectQuery s {ip} {sch} = do
      ref <- jscall "runSelectQuery(%0)" (String -> JS_IO JSRef) (show s)
      packed <- pack ref
      case packed of
        (JSObject "Array" ** array) => do
          maybeObjs <- arrayToObjects array
          (case maybeObjs of
            Just objs => objListToRecords {sch=sch} {ip=ip} objs
            Nothing => pure Nothing)
        _ => pure Nothing

runSelectQueryUnsafe : Select sch
    -> {auto ip: schemaImp sch FromJSD}
    -> JS_IO (List (Record sch))
runSelectQueryUnsafe s {ip} = do
  maybeList <- runSelectQuery s {ip=ip}
  case maybeList of
    Just lst => pure lst
    Nothing => idris_crash "Sql.JS: Failed to run select query"



