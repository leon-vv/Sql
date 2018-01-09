import Sql
import Sql.JS

import Event

import Record
import Record.JS

import FerryJS

import Effects

todoSchema : Schema
todoSchema = [("name", String)]

todo : Table Main.todoSchema
todo = MkTable {sch=[("name", String)]} "todo"

State : Type
State = Event (List (Record todoSchema))

selectQuery : Select Main.todoSchema
selectQuery = SelectQuery todo (Const True) Nil 

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

