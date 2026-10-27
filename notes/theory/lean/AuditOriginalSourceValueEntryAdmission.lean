import Lean.Elab.Command
import Lean.Util.CollectAxioms
import YulangClosure.OriginalSourceValueEntryAdmission

set_option pp.fullNames true
set_option pp.privateNames true
set_option pp.proofs true
set_option pp.deepTerms true
set_option pp.maxSteps 1000000
open Lean Elab Command

/- Author-owned mechanical census, not independent review. -/
run_cmd do
  let env ← getEnv
  let some index := env.getModuleIdx? `YulangClosure.OriginalSourceValueEntryAdmission
    | throwError "target module is not imported"
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    if env.getModuleIdxFor? name == some index then
      count := count + 1
      match info with
      | .axiomInfo _ => throwError "project axiom: {name}"
      | _ => pure ()
      logInfo m!"YULANG_SOURCE_RECEIPT_BEGIN {name}"
      let id := mkIdent name
      elabCommand (← `(#check @$id))
      elabCommand (← `(#print axioms $id))
      for ax in ← collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "unapproved axiom in {name}: {ax}"
      logInfo m!"YULANG_SOURCE_RECEIPT_END {name}"
  unless count == 28 do throwError "expected six authored and 22 generated declarations, got {count}"
  logInfo m!"YULANG_SOURCE_RECEIPT_COUNT declarations={count}"
