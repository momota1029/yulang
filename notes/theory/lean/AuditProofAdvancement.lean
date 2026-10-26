import Lean.Elab.Command
import Lean.Util.CollectAxioms
import YulangClosure.ProofAdvancement

/-!
Complete originating-module audit for the four proof advancement modules.
Run after the default build:

  lake build
  lake env lean -j1 -M1024 AuditProofAdvancement.lean

Every theorem constant is checked, including private and generated helpers.
The named application roots must actually occur in that inventory. Kernel
acceptance and this axiom audit do not discharge theorem hypotheses or replace
independent source/meaning review.
-/

set_option pp.fullNames true
set_option pp.privateNames true
set_option pp.universes false

open Lean Elab Command

run_cmd do
  let modules : Array Name := #[
    `YulangClosure.PaperTermSubstitutionAlgebra,
    `YulangClosure.PaperCallEntryFormation,
    `YulangClosure.PaperAllocationExecution,
    `YulangClosure.NativeIntegerArithmetic
  ]
  let roots : Array Name := #[
    `YulangClosure.PaperTypes.PaperTermAlgebra.replaceValue_comp,
    `YulangClosure.PaperTypes.PaperTermAlgebra.replaceComputation_comp,
    `YulangClosure.PaperTypes.PaperTermAlgebra.mapType_replaceValue,
    `YulangClosure.PaperTypes.PaperTermAlgebra.mapType_replaceComputation,
    `YulangClosure.PaperTypes.PaperTermAlgebra.response_after_environment,
    `YulangClosure.PaperTypes.PaperTermAlgebra.graphFormals_computation,
    `YulangClosure.PaperTypes.PaperTermAlgebra.typed_value_composition,
    `YulangClosure.PaperTypes.PaperTermAlgebra.typed_computation_composition,
    `YulangClosure.PaperTypes.PaperCallEntryFormation.call_spine_formation,
    `YulangClosure.PaperTypes.PaperCallEntryFormation.call_spine_finite_interaction,
    `YulangClosure.PaperTypes.PaperCallEntryFormation.value_entry_view_frontier,
    `YulangClosure.PaperTypes.PaperAllocationExecution.finite_history,
    `YulangClosure.PaperTypes.PaperAllocationExecution.saved_response_prefix,
    `YulangClosure.PaperTypes.PaperAllocationExecution.saved_response_history,
    `YulangClosure.PaperTypes.PaperAllocationExecution.allocated_body_history,
    `YulangClosure.PaperTypes.PaperAllocationExecution.fresh_response_replay,
    `YulangClosure.NativeIntegerArithmetic.decimalAdd_decode,
    `YulangClosure.NativeIntegerArithmetic.decimalSubtract_decode,
    `YulangClosure.Control.actual_call_request_completed_add_response,
    `YulangClosure.Control.actual_call_request_completed_subtract_response
  ]
  let env ← getEnv
  let mut targets : Array Name := #[]
  for moduleName in modules do
    let some moduleIndex := env.getModuleIdx? moduleName
      | throwError "audited module is not imported: {moduleName}"
    let mut count : Nat := 0
    for (name, info) in env.constants.toList do
      if env.getModuleIdxFor? name == some moduleIndex then
        match info with
        | .thmInfo _ =>
            unless !targets.contains name do
              throwError "duplicate theorem target: {name}"
            targets := targets.push name
            count := count + 1
        | .axiomInfo _ => throwError "project axiom in audited module: {name}"
        | _ => pure ()
    if count == 0 then
      throwError "audited module has no theorem declarations: {moduleName}"
    logInfo m!"YULANG_AUDIT_MODULE {moduleName} {count}"
  for root in roots do
    unless targets.contains root do
      throwError "required application root is missing or is not a theorem: {root}"
  for name in targets do
    logInfo m!"YULANG_AUDIT_BEGIN {name}"
    let id := mkIdent name
    elabCommand (← `(#check @$id))
    elabCommand (← `(#print axioms $id))
    let axioms ← collectAxioms name
    for ax in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "unapproved axiom in {name}: {ax}"
    logInfo m!"YULANG_AUDIT_END {name}"
  logInfo m!"YULANG_AUDIT_COUNT {targets.size}"
