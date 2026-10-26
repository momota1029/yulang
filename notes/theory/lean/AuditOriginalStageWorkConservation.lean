import Lean.Elab.Command
import Lean.Util.CollectAxioms
import YulangClosure.OriginalStageWorkConservation

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
  let moduleName := `YulangClosure.OriginalStageWorkConservation
  let some index := env.getModuleIdx? moduleName
    | throwError "audited module is not imported"
  let required : Array Name := #[
    `YulangClosure.OriginalStageWorkConservation.structural_current,
    `YulangClosure.OriginalStageWorkConservation.update_current,
    `YulangClosure.OriginalStageWorkConservation.structural_not_returned,
    `YulangClosure.OriginalStageWorkConservation.returned_is_ready,
    `YulangClosure.OriginalStageWorkConservation.active_not_returned,
    `YulangClosure.OriginalStageWorkConservation.structural_working,
    `YulangClosure.OriginalStageWorkConservation.update_working,
    `YulangClosure.OriginalStageWorkConservation.advanced_working,
    `YulangClosure.OriginalStageWorkConservation.apply_working,
    `YulangClosure.OriginalStageWorkConservation.structural_not_take,
    `YulangClosure.OriginalStageWorkConservation.update_take,
    `YulangClosure.OriginalStageWorkConservation.next_queue_keeps,
    `YulangClosure.OriginalStageWorkConservation.advanced_keeps_tail,
    `YulangClosure.OriginalStageWorkConservation.live_top_above,
    `YulangClosure.OriginalStageWorkConservation.completed_processed,
    `YulangClosure.OriginalStageWorkConservation.advanced_flight,
    `YulangClosure.OriginalStageWorkConservation.replace_flight,
    `YulangClosure.OriginalStageWorkConservation.push_frame_flight,
    `YulangClosure.OriginalStageWorkConservation.apply_flight,
    `YulangClosure.OriginalStageWorkConservation.enqueue_flight,
    `YulangClosure.OriginalStageWorkConservation.states_start,
    `YulangClosure.OriginalStageWorkConservation.states_step,
    `YulangClosure.OriginalStageWorkConservation.conserve,
    `YulangClosure.OriginalStageWorkConservation.boundary_excludes_flight,
    `YulangClosure.OriginalStageWorkConservation.first_boundary_processed,
    `YulangClosure.OriginalStageWorkConservation.every_queued_processed,
    `YulangClosure.OriginalStageWorkConservation.select_first,
    `YulangClosure.OriginalStageWorkConservation.no_earlier_before,
    `YulangClosure.OriginalStageWorkConservation.conserve_completion,
    `YulangClosure.OriginalStageWorkConservation.first_boundary_completion,
    `YulangClosure.OriginalStageWorkConservation.prefix_live,
    `YulangClosure.OriginalStageWorkConservation.execute_suffix,
    `YulangClosure.OriginalStageWorkConservation.every_queue_has_new_completion,
    `YulangClosure.OriginalStageWorkConservation.initialized_dispatch_queue_coverage]
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
    logInfo m!"YULANG_STAGE_WORK_CONSERVATION_BEGIN {name}"
    let id := mkIdent name
    elabCommand (← `(#check @$id))
    elabCommand (← `(#print axioms $id))
    for ax in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "unapproved axiom in {name}: {ax}"
    logInfo m!"YULANG_STAGE_WORK_CONSERVATION_END {name}"
  logInfo m!"YULANG_STAGE_WORK_CONSERVATION_COUNT declarations={targets.size} theorems={theorems}"
