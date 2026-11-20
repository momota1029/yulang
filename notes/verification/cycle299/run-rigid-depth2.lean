import Yulang.GeneralGeneratedDictionaryControls299

open Yulang
open GeneralGeneratedDictionaryRun299 (run)
open GeneralGeneratedDictionaryMemo299 (checkMemo)
open GeneralGeneratedRigidCompile299 (source encode fromGoals incomplete)
open GeneralGeneratedRigidNested299 (decode eraseKeys)
open Roles.Examples

def main : IO Unit := do
  let compiled := fromGoals goodImpls source encode
  unless checkMemo compiled [0,1,2] 3 && !(checkMemo compiled [0,1,2] 2) do
    throw (IO.userError "unexpected depth bound")
  IO.println "PASS compiled rigid nested Display needs three fuel units"
  match RoleDictionaries.elaborate goodImpls goodImpls_wellFormed (decode 0), run compiled 3 0 with
  | .resolved plan, some (.node 0 [.node 0 [.node 1 []]]) =>
    match eraseKeys plan with
    | .node 0 [.node 0 [.node 1 []]] =>
      IO.println "PASS the existing rigid elaborator and computed frontier agree on keys 0 → 0 → 1"
    | _ => throw (IO.userError "old elaborator did not produce expected keys")
  | _, _ => throw (IO.userError "incorrect nested dictionary")
  unless (run (fromGoals goodImpls source incomplete) 3 0).isNone do
    throw (IO.userError "incorrect missing-input result")
  IO.println "PASS omitting the int goal leaves the selected child's row unresolved"
  IO.println "This is the older rigid elaborator, not a new V8 raw execution."
