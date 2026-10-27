import Lean.Elab.Command
import Lean.Util.CollectAxioms
import YulangClosure.OriginalEventProofCut
set_option pp.fullNames true
set_option pp.privateNames true
set_option pp.universes false
set_option pp.maxSteps 1000000
open Lean Elab Command
#print YulangClosure.OriginalEventProofCut.ActualFieldsPreserved
#print YulangClosure.OriginalEventProofCut.BodyConsumerAtCut
run_cmd do
  let env ← getEnv
  let some index := env.getModuleIdx? `YulangClosure.OriginalEventProofCut
    | throwError "module missing"
  let required := #[`YulangClosure.OriginalEventProofCut.body_consumer_actual_fields,
    `YulangClosure.OriginalEventProofCut.generated_value_body_actual_fields]
  let mut targets : Array Name := #[]
  let mut theorems : Array Name := #[]
  for (name, info) in env.constants.toList do
    if env.getModuleIdxFor? name == some index then
      targets := targets.push name
      match info with
      | .thmInfo _ => theorems := theorems.push name
      | .axiomInfo _ => throwError "project axiom {name}"
      | _ => pure ()
  for root in required do
    unless theorems.contains root do throwError "required theorem missing {root}"
  for name in targets do
    logInfo m!"ORIGIN_AUDIT_BEGIN {name}"
    let id := mkIdent name
    elabCommand (← `(#check @$id))
    elabCommand (← `(#print axioms $id))
    for ax in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "unapproved axiom {name}: {ax}"
    logInfo m!"ORIGIN_AUDIT_END {name}"
  logInfo m!"ORIGIN_DECLARATIONS {targets.size}; THEOREMS {theorems.size}"
