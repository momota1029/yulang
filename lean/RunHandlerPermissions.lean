import Yulang.HandlerPermissionExamples

/-!
Run the boundary-qualified arm check and actual incoming-action handlers:

    lake env lean --trust=0 --run RunHandlerPermissions.lean
-/

open Yulang Directed HandlerPermissions HandlerPermissionExamples

def main : IO Unit := do
  if diagnostics onlyConsole arms != [.io] then
    throw (IO.userError "the console annotation must report exactly the io arm")
  if check onlyConsole arms || !check onlyConsole [.console] then
    throw (IO.userError "incoming-handler permission acceptance changed")
  IO.println "console annotation => io arm reported, console arm permitted"
  for (name, actual, expected) in runtimeCases do
    if actual != expected then
      throw (IO.userError (name ++ ": unexpected runtime head " ++ reprStr actual))
    IO.println (name ++ " => " ++ reprStr actual)
  IO.println "incoming handler permission tour passed"
