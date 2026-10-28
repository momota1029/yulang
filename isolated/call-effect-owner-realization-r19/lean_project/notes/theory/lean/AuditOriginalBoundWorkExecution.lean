import Lean.Elab.Command
import Lean.Util.CollectAxioms
import YulangClosure.OriginalBoundWorkExecution
set_option pp.fullNames true
set_option pp.privateNames true
set_option pp.universes true
set_option pp.proofs true
set_option pp.deepTerms true
set_option pp.maxSteps 1000000
#check @YulangClosure.OriginalBoundWorkExecution.scoped_admission_whole
#print axioms YulangClosure.OriginalBoundWorkExecution.scoped_admission_whole
#check @YulangClosure.OriginalBoundWorkExecution.canonical_request_whole
#print axioms YulangClosure.OriginalBoundWorkExecution.canonical_request_whole
#check @YulangClosure.OriginalBoundWorkExecution.selected_request_canonical
#print axioms YulangClosure.OriginalBoundWorkExecution.selected_request_canonical
#check @YulangClosure.OriginalBoundWorkExecution.loop_inputs_representatives
#print axioms YulangClosure.OriginalBoundWorkExecution.loop_inputs_representatives
#check @YulangClosure.OriginalBoundWorkExecution.unscoped_stops
#print axioms YulangClosure.OriginalBoundWorkExecution.unscoped_stops
#check @YulangClosure.OriginalBoundWorkExecution.physical_representatives
#print axioms YulangClosure.OriginalBoundWorkExecution.physical_representatives
#check @YulangClosure.OriginalBoundWorkExecution.observe_retains
#print axioms YulangClosure.OriginalBoundWorkExecution.observe_retains
#check @YulangClosure.OriginalBoundWorkExecution.finish_retains
#print axioms YulangClosure.OriginalBoundWorkExecution.finish_retains
#check @YulangClosure.OriginalBoundWorkExecution.append_retains
#print axioms YulangClosure.OriginalBoundWorkExecution.append_retains
#check @YulangClosure.OriginalBoundWorkExecution.reserve_retains
#print axioms YulangClosure.OriginalBoundWorkExecution.reserve_retains
#check @YulangClosure.OriginalBoundWorkExecution.journal_retains
#print axioms YulangClosure.OriginalBoundWorkExecution.journal_retains
#check @YulangClosure.OriginalBoundWorkExecution.admitted_retains
#print axioms YulangClosure.OriginalBoundWorkExecution.admitted_retains
#check @YulangClosure.OriginalBoundWorkExecution.imported_retains
#print axioms YulangClosure.OriginalBoundWorkExecution.imported_retains
#check @YulangClosure.OriginalBoundWorkExecution.insert_retains
#print axioms YulangClosure.OriginalBoundWorkExecution.insert_retains
#check @YulangClosure.OriginalBoundWorkExecution.insert_fibers_unchanged
#print axioms YulangClosure.OriginalBoundWorkExecution.insert_fibers_unchanged
#check @YulangClosure.OriginalBoundWorkExecution.insert_request
#print axioms YulangClosure.OriginalBoundWorkExecution.insert_request
#check @YulangClosure.OriginalBoundWorkExecution.finish_retained
#print axioms YulangClosure.OriginalBoundWorkExecution.finish_retained
#check @YulangClosure.OriginalBoundWorkExecution.finish_ready_slot
#print axioms YulangClosure.OriginalBoundWorkExecution.finish_ready_slot
#check @YulangClosure.OriginalBoundWorkExecution.append_ready_readback
#print axioms YulangClosure.OriginalBoundWorkExecution.append_ready_readback
#check @YulangClosure.OriginalBoundWorkExecution.observe_ready
#print axioms YulangClosure.OriginalBoundWorkExecution.observe_ready
#check @YulangClosure.OriginalBoundWorkExecution.reserve_ready
#print axioms YulangClosure.OriginalBoundWorkExecution.reserve_ready
#check @YulangClosure.OriginalBoundWorkExecution.journal_ready
#print axioms YulangClosure.OriginalBoundWorkExecution.journal_ready
#check @YulangClosure.OriginalBoundWorkExecution.admitted_ready
#print axioms YulangClosure.OriginalBoundWorkExecution.admitted_ready
#check @YulangClosure.OriginalBoundWorkExecution.imported_ready
#print axioms YulangClosure.OriginalBoundWorkExecution.imported_ready
#check @YulangClosure.OriginalBoundWorkExecution.insert_ready
#print axioms YulangClosure.OriginalBoundWorkExecution.insert_ready
#check @YulangClosure.OriginalBoundWorkExecution.bound_at_metadata
#print axioms YulangClosure.OriginalBoundWorkExecution.bound_at_metadata
#check @YulangClosure.OriginalBoundWorkExecution.selected_bound_execution
#print axioms YulangClosure.OriginalBoundWorkExecution.selected_bound_execution
#check @YulangClosure.OriginalBoundWorkExecution.every_captured_delivered
#print axioms YulangClosure.OriginalBoundWorkExecution.every_captured_delivered
#check @YulangClosure.OriginalBoundWorkExecution.Computed.row_execution_dispatch
#print axioms YulangClosure.OriginalBoundWorkExecution.Computed.row_execution_dispatch
#check @YulangClosure.OriginalBoundWorkExecution.Computed.row_execution_at_metadata
#print axioms YulangClosure.OriginalBoundWorkExecution.Computed.row_execution_at_metadata
#check @YulangClosure.OriginalBoundWorkExecution.Computed.sources_generated
#print axioms YulangClosure.OriginalBoundWorkExecution.Computed.sources_generated
#check @YulangClosure.OriginalBoundWorkExecution.Computed.row_physical_and_order
#print axioms YulangClosure.OriginalBoundWorkExecution.Computed.row_physical_and_order
#check @YulangClosure.OriginalBoundWorkExecution.Computed.row_first_loop_complete
#print axioms YulangClosure.OriginalBoundWorkExecution.Computed.row_first_loop_complete
#check @YulangClosure.OriginalBoundWorkExecution.Computed.row_exact_children
#print axioms YulangClosure.OriginalBoundWorkExecution.Computed.row_exact_children
#check @YulangClosure.OriginalBoundWorkExecution.Computed.row_all_captured
#print axioms YulangClosure.OriginalBoundWorkExecution.Computed.row_all_captured
#check @YulangClosure.OriginalBoundWorkExecution.Computed.sample_failure_keeps_append
#print axioms YulangClosure.OriginalBoundWorkExecution.Computed.sample_failure_keeps_append
#check @YulangClosure.OriginalBoundWorkExecution.Computed.fiber_sample_failure_keeps_partial
#print axioms YulangClosure.OriginalBoundWorkExecution.Computed.fiber_sample_failure_keeps_partial
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let some target := env.getModuleIdx? `YulangClosure.OriginalBoundWorkExecution
    | throwError "audit target is not imported"
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
      logInfo m!"AUDIT_BEGIN {label} {name}"
      let ident := mkIdent name
      elabCommand (← `(#check @$ident))
      elabCommand (← `(#print axioms $ident))
      let dependencies ← collectAxioms name
      for dependency in dependencies do
        unless dependency == `propext || dependency == `Classical.choice || dependency == `Quot.sound do
          throwError "unexpected dependency {dependency} for {name}"
      logInfo m!"AUDIT_END {name}"
  logInfo m!"AUDIT_COUNT {total} {theoremCount}"
