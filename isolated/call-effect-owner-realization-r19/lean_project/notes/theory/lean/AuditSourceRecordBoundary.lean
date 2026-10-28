import Lean.Elab.Command
import Lean.Util.CollectAxioms
import YulangClosure.OriginalSourceRecordBoundary

set_option pp.fullNames true
set_option pp.privateNames true
set_option pp.universes false
set_option pp.proofs true
open Lean Elab Command

run_cmd do
  let moduleName := `YulangClosure.OriginalSourceRecordBoundary
  let roots : Array Name := #[
    `YulangClosure.OriginalSourceRecordBoundary.construct_record,
    `YulangClosure.OriginalSourceRecordBoundary.construct_preserves,
    `YulangClosure.OriginalSourceRecordBoundary.common_payload_constructed,
    `YulangClosure.OriginalSourceRecordBoundary.constructed_survivors,
    `YulangClosure.OriginalSourceRecordBoundary.successive_boundaries_survivors,
    `YulangClosure.OriginalSourceRecordBoundary.pure_scan_completes,
    `YulangClosure.OriginalSourceRecordBoundary.constructed_record_execution,
    `YulangClosure.OriginalSourceRecordBoundary.constructed_children_safe,
    `YulangClosure.OriginalSourceRecordBoundary.constructed_record_prefixes,
    `YulangClosure.OriginalSourceRecordBoundary.compile_owner_readback,
    `YulangClosure.OriginalSourceRecordBoundary.compiled_owner_preserves,
    `YulangClosure.OriginalSourceRecordBoundary.compile_owners_exact,
    `YulangClosure.OriginalSourceRecordBoundary.compiled_source_member,
    `YulangClosure.OriginalSourceRecordBoundary.compiled_source_preserves,
    `YulangClosure.OriginalSourceRecordBoundary.constructed_original_boundary,
    `YulangClosure.OriginalSourceRecordBoundary.Witness.original_boundary_owners,
    `YulangClosure.OriginalSourceRecordBoundary.Witness.original_source_constructs_both,
    `YulangClosure.OriginalSourceRecordBoundary.Witness.exact_source_programs,
    `YulangClosure.OriginalSourceRecordBoundary.Witness.source_sequence_does_not_resurrect,
    `YulangClosure.OriginalSourceRecordBoundary.Witness.input_typed,
    `YulangClosure.OriginalSourceRecordBoundary.Witness.original_source_sequence_typed,
    `YulangClosure.OriginalSourceRecordBoundary.Witness.absent_common_is_statically_compared,
    `YulangClosure.OriginalSourceRecordBoundary.Witness.nested_identity_and_record_construct
  ]
  let env ← getEnv
  let some moduleIndex := env.getModuleIdx? moduleName
    | throwError "module not imported: {moduleName}"
  let mut count : Nat := 0
  let mut targets : Array Name := #[]
  for (name, info) in env.constants.toList do
    if env.getModuleIdxFor? name == some moduleIndex then
      count := count + 1
      match info with
      | .thmInfo _ => targets := targets.push name
      | .axiomInfo _ => throwError "project axiom: {name}"
      | _ => pure ()
  if targets.isEmpty then throwError "empty originating inventory"
  logInfo m!"RECORD_AUDIT_DECLARATIONS {count}"
  for root in roots do
    unless targets.contains root do throwError "required theorem missing: {root}"
  for name in targets do
    logInfo m!"RECORD_AUDIT_BEGIN {name}"
    let id := mkIdent name
    elabCommand (← `(#check @$id))
    elabCommand (← `(#print axioms $id))
    for ax in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "unapproved axiom {ax} in {name}"
    logInfo m!"RECORD_AUDIT_END {name}"
  logInfo m!"RECORD_AUDIT_COUNT {targets.size}"
  logInfo m!"RECORD_AUDIT_PUBLIC_ROOTS {roots.size}"
