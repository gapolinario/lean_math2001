import Lean

--open Lean Elab Command Term Meta
open Lean

elab "#mycommand2" : command =>
  logInfo "Hello World"

#mycommand2 -- Hello World
