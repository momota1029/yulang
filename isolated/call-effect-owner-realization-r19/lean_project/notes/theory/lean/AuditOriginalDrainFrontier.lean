import Lean.Elab.Command
import Lean.Util.CollectAxioms
import YulangClosure.OriginalDrainFrontier

set_option pp.fullNames true
set_option pp.privateNames true
set_option pp.universes true
set_option pp.proofs true
set_option pp.deepTerms true
set_option pp.maxSteps 1000000
open Lean Elab Command

/- Complete origin-based type and axiom census, including every definition,
private declaration and generated theorem. This is not a source extraction
or a proof of the original global inference-accessibility proposition. -/
run_cmd do
  let env ← getEnv
  let moduleName := `YulangClosure.OriginalDrainFrontier
  let some index := env.getModuleIdx? moduleName
    | throwError "audited module is not imported"
  let required : Array Name := #[
    `YulangClosure.OriginalDrainFrontier.fresh_poll,
    `YulangClosure.OriginalDrainFrontier.initial_polls,
    `YulangClosure.OriginalDrainFrontier.nonentry_idle,
    `YulangClosure.OriginalDrainFrontier.update_returns_entry,
    `YulangClosure.OriginalDrainFrontier.tail_polls,
    `YulangClosure.OriginalDrainFrontier.replace_polls,
    `YulangClosure.OriginalDrainFrontier.advanced_polls,
    `YulangClosure.OriginalDrainFrontier.apply_polls,
    `YulangClosure.OriginalDrainFrontier.execute_polls,
    `YulangClosure.OriginalDrainFrontier.initialized_polls,
    `YulangClosure.OriginalDrainFrontier.initialized_active_entry,
    `YulangClosure.OriginalDrainFrontier.initialized_active_entry_only,
    `YulangClosure.OriginalDrainFrontier.initialized_active_not_boundary,
    `YulangClosure.OriginalDrainFrontier.initialized_active_first_settlement,
    `YulangClosure.OriginalDrainFrontier.initialized_dispatch_current,
    `YulangClosure.OriginalDrainFrontier.initialized_dispatch_first_settlement]
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
    logInfo m!"YULANG_FRONTIER_REVIEW_BEGIN {name}"
    let id := mkIdent name
    elabCommand (← `(#check @$id))
    elabCommand (← `(#print axioms $id))
    for ax in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "unapproved axiom in {name}: {ax}"
    logInfo m!"YULANG_FRONTIER_REVIEW_END {name}"
  logInfo m!"YULANG_FRONTIER_REVIEW_COUNT declarations={targets.size} theorems={theorems}"
