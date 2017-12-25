module Sql.JS

import Sql

import Record
import Record.JS

import IdrisScript
import IdrisScript.Arrays

%access public export
%access total

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
          withIndex arr idx (S l) lst = (arr !! l) >>= (\elem => case elem of
                                    Just (JSObject "Object" ** v) => withIndex arr (idx+1) l (v::lst)
                                    Just _ => pure Nothing
                                    Nothing => pure Nothing)

private
objListToRecords : List Obj -> {auto ip: schemaImp sc FromJSD} -> JS_IO (Maybe (List (Record sc)))
objListToRecords {sc} {ip} objs = do
    maybeRecs <- sequence $ map (objectToRecord sc {fp=ip}) objs
    pure (sequence maybeRecs)

partial
runSelectQuery : Select sc
    -> {auto ip: schemaImp sc FromJSD}
    -> JS_IO (Maybe (List (Record sc)))
runSelectQuery s {ip} {sc} =
    let queryString = selectToString s
    in do
      ref <- jscall "runSelectQuery(%0)" (String -> JS_IO JSRef) queryString
      packed <- pack ref
      case packed of
        (JSObject "Array" ** array) => do
          maybeObjs <- arrayToObjects array
          case maybeObjs of
            Just objs => objListToRecords {sc=sc} {ip=ip} objs
            Nothing => pure Nothing
        _ => pure Nothing

      
