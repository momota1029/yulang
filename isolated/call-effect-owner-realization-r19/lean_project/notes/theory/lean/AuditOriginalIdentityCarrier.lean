import Lean.Elab.Command
import Lean.Util.CollectAxioms
import YulangClosure.OriginalIdentityCarrier

set_option pp.fullNames true
set_option pp.privateNames true
set_option pp.proofs true
set_option pp.deepTerms true
set_option pp.maxSteps 1000000
open Lean Elab Command

/- Complete origin-based type and axiom census, including every definition,
private declaration and generated theorem. This independently checks the exact frozen carrier module; semantic source
correspondence is reviewed separately. -/
run_cmd do
  let env ← getEnv
  let moduleName := `YulangClosure.OriginalIdentityCarrier
  let some index := env.getModuleIdx? moduleName
    | throwError "audited module is not imported"
  let required : Array Name := #[
    `YulangClosure.OriginalIdentityCarrier.allocation_keeps_actual_code,
    `YulangClosure.OriginalIdentityCarrier.bound_name_delay_run,
    `YulangClosure.OriginalIdentityCarrier.history_same_capture,
    `YulangClosure.OriginalIdentityCarrier.observation_meaning,
    `YulangClosure.OriginalIdentityCarrier.name_delay_whole,
    `YulangClosure.OriginalIdentityCarrier.generated_identity_from_name_delay]
  let mut targets : Array Name := #[]
  let mut theorems : Nat := 0
  for (name, info) in env.constants.toList do
    if env.getModuleIdxFor? name == some index then
      targets := targets.push name
      match info with
      | .thmInfo _ => theorems := theorems + 1
      | .axiomInfo _ => throwError "project axiom: {name}"
      | _ => pure ()
  for root in required do
    unless targets.contains root do throwError "missing required theorem: {root}"
    match env.find? root with
    | some (.thmInfo _) => pure ()
    | _ => throwError "required root is not a theorem: {root}"
  for name in targets do
    logInfo m!"YULANG_CARRIER_REVIEW_BEGIN {name}"
    let id := mkIdent name
    elabCommand (← `(#check @$id))
    elabCommand (← `(#print axioms $id))
    for ax in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "unapproved axiom in {name}: {ax}"
    logInfo m!"YULANG_CARRIER_REVIEW_END {name}"
  logInfo m!"YULANG_CARRIER_REVIEW_COUNT declarations={targets.size} theorems={theorems}"
