import Lean.Elab.Command
import Lean.Util.CollectAxioms
import YulangClosure.OriginalDrainStages
set_option pp.fullNames true
set_option pp.privateNames true
set_option pp.universes true
set_option pp.proofs true
set_option pp.deepTerms true
set_option pp.maxSteps 1000000
#check @YulangClosure.OriginalDrainStages.fresh_shape
#print axioms YulangClosure.OriginalDrainStages.fresh_shape
#check @YulangClosure.OriginalDrainStages.working_empty_is_transport
#print axioms YulangClosure.OriginalDrainStages.working_empty_is_transport
#check @YulangClosure.OriginalDrainStages.terminal_current_empty
#print axioms YulangClosure.OriginalDrainStages.terminal_current_empty
#check @YulangClosure.OriginalDrainStages.finish_dispatch_shape
#print axioms YulangClosure.OriginalDrainStages.finish_dispatch_shape
#check @YulangClosure.OriginalDrainStages.structural_shape
#print axioms YulangClosure.OriginalDrainStages.structural_shape
#check @YulangClosure.OriginalDrainStages.update_shape
#print axioms YulangClosure.OriginalDrainStages.update_shape
#check @YulangClosure.OriginalDrainStages.structural_owner
#print axioms YulangClosure.OriginalDrainStages.structural_owner
#check @YulangClosure.OriginalDrainStages.update_owner
#print axioms YulangClosure.OriginalDrainStages.update_owner
#check @YulangClosure.OriginalDrainStages.initial_valid
#print axioms YulangClosure.OriginalDrainStages.initial_valid
#check @YulangClosure.OriginalDrainStages.advance_valid
#print axioms YulangClosure.OriginalDrainStages.advance_valid
#check @YulangClosure.OriginalDrainStages.apply_valid
#print axioms YulangClosure.OriginalDrainStages.apply_valid
#check @YulangClosure.OriginalDrainStages.execute_valid
#print axioms YulangClosure.OriginalDrainStages.execute_valid
#check @YulangClosure.OriginalDrainStages.initialized_valid
#print axioms YulangClosure.OriginalDrainStages.initialized_valid
#check @YulangClosure.OriginalDrainStages.projected_empty_boundary_iff
#print axioms YulangClosure.OriginalDrainStages.projected_empty_boundary_iff
#check @YulangClosure.OriginalDrainStages.initialized_boundary_is_transport
#print axioms YulangClosure.OriginalDrainStages.initialized_boundary_is_transport
#check @YulangClosure.OriginalDrainStages.settlement_starts_at_boundary
#print axioms YulangClosure.OriginalDrainStages.settlement_starts_at_boundary
#check @YulangClosure.OriginalDrainStages.boundary_enters_settlement
#print axioms YulangClosure.OriginalDrainStages.boundary_enters_settlement
#check @YulangClosure.OriginalDrainStages.dirty_empty_stays_transport
#print axioms YulangClosure.OriginalDrainStages.dirty_empty_stays_transport
#check @YulangClosure.OriginalDrainStages.clean_empty_enters_diagnostics
#print axioms YulangClosure.OriginalDrainStages.clean_empty_enters_diagnostics
#check @YulangClosure.OriginalDrainStages.indexed_member
#print axioms YulangClosure.OriginalDrainStages.indexed_member
#check @YulangClosure.OriginalDrainStages.apply_keeps_suspended
#print axioms YulangClosure.OriginalDrainStages.apply_keeps_suspended
#check @YulangClosure.OriginalDrainStages.same_top_is_saved_frame
#print axioms YulangClosure.OriginalDrainStages.same_top_is_saved_frame
#check @YulangClosure.OriginalDrainStages.resume_same_frame
#print axioms YulangClosure.OriginalDrainStages.resume_same_frame
#check @YulangClosure.OriginalDrainStages.initialized_resume_same_frame
#print axioms YulangClosure.OriginalDrainStages.initialized_resume_same_frame
#check @YulangClosure.OriginalDrainStages.resumed_transport_boundary
#print axioms YulangClosure.OriginalDrainStages.resumed_transport_boundary
#check @YulangClosure.OriginalDrainStages.truncate_keeps_queue
#print axioms YulangClosure.OriginalDrainStages.truncate_keeps_queue
#check @YulangClosure.OriginalDrainStages.truncate_survivor_is_original
#print axioms YulangClosure.OriginalDrainStages.truncate_survivor_is_original
#check @YulangClosure.OriginalDrainStages.truncate_survivor_shape
#print axioms YulangClosure.OriginalDrainStages.truncate_survivor_shape
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let some target := env.getModuleIdx? `YulangClosure.OriginalDrainStages
    | throwError "review target is not imported"
  let mut total : Nat := 0
  let mut theoremCount : Nat := 0
  for (name, info) in env.constants.toList do
    if env.getModuleIdxFor? name == some target then
      total := total + 1
      let label ← match info with
        | .axiomInfo _ => throwError "target contains an axiom: {name}"
        | .thmInfo _ => theoremCount := theoremCount + 1; pure "theorem"
        | .defnInfo _ => pure "definition"
        | .opaqueInfo _ => pure "opaque"
        | .inductInfo _ => pure "inductive"
        | .ctorInfo _ => pure "constructor"
        | .recInfo _ => pure "recursor"
        | .quotInfo _ => pure "quotient"
      logInfo m!"REVIEW_BEGIN {label} {name}"
      let ident := mkIdent name
      elabCommand (← `(#check @$ident))
      elabCommand (← `(#print axioms $ident))
      let dependencies ← collectAxioms name
      for dependency in dependencies do
        unless dependency == `propext || dependency == `Classical.choice || dependency == `Quot.sound do
          throwError "unexpected dependency {dependency} for {name}"
      logInfo m!"REVIEW_END {name}"
  logInfo m!"REVIEW_COUNT {total} {theoremCount}"
