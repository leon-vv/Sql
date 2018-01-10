import Sql
import Sql.JS

import Event

import Record

import FerryJS

import Effects

todoSchema : Schema
todoSchema = [("name", String)]

todo : Table Main.todoSchema
todo = MkTable {sch=[("name", String)]} "todo"

State : Type
State = Event (List (Record todoSchema))

selectQuery : Select Main.todoSchema
selectQuery = 
  selectJust (Col String "name")
    {as="name"}
    {from=todo}

selectQuery2 : Select Main.todoSchema
selectQuery2 =
  selectJust (Col String "name")
    {as="name"}
    {from=todo}
    {where_=
      ((Col String "name" =# Const "abc")
      &&# (Col String "name" =# Const "def"))}

selectQuery3 : Select [("a", String), ("b", String)]
selectQuery3 =
  select
    ("a" `isExpr` (Const "abc") $
      ("b" `isLastExpr` (Const "daf")))
    {from=todo}


initialState : JS_IO State
initialState = let l = "leonvv" in do 
  c <- newConnection {user=l} {password=l} {database=l}
  runSelectQuery selectQuery c

logAll : List String -> JS_IO ()
logAll lst = do sequence $ map log lst; pure ()

nextState : State -> JS_IO State
nextState ev = do
  maybeLst <- ev
  (case maybeLst of
       Just lst => do logAll (map (.. "name") lst)
       Nothing => pure ())
  pure ev

main : JS_IO ()
main = run initialState nextState

