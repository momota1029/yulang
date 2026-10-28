import Lean.Elab.Command
import Lean.Util.CollectAxioms
import YulangClosure.OriginalScopedClosure

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
  let moduleName := `YulangClosure.OriginalScopedClosure
  let some index := env.getModuleIdx? moduleName
    | throwError "audited module is not imported"
  let required : Array Name := #[
    `YulangClosure.OriginalScopedClosure.erase_allocate,
    `YulangClosure.OriginalScopedClosure.erase_allocate_forest,
    `YulangClosure.OriginalScopedClosure.erase_copy,
    `YulangClosure.OriginalScopedClosure.erase_copy_forest,
    `YulangClosure.OriginalScopedClosure.source_residual,
    `YulangClosure.OriginalScopedClosure.definition_residual,
    `YulangClosure.OriginalScopedClosure.joint_residual,
    `YulangClosure.OriginalScopedClosure.copy_residual,
    `YulangClosure.OriginalScopedClosure.source_copy_adequacy,
    `YulangClosure.OriginalScopedClosure.joint_copy_adequacy,
    `YulangClosure.OriginalScopedClosure.copied_owner,
    `YulangClosure.OriginalScopedClosure.copied_shared_reference,
    `YulangClosure.OriginalScopedClosure.copied_event_reference,
    `YulangClosure.OriginalScopedClosure.description_copy_distinct,
    `YulangClosure.OriginalScopedClosure.copied_event_proof,
    `YulangClosure.OriginalScopedClosure.actual_key_uses_original_event,
    `YulangClosure.OriginalScopedClosure.actual_key_copy_independent,
    `YulangClosure.OriginalScopedClosure.proof_key_copy,
    `YulangClosure.OriginalScopedClosure.proof_key_logical_extension,
    `YulangClosure.OriginalScopedClosure.shared_anchor_copy_independent,
    `YulangClosure.OriginalScopedClosure.copy_publications,
    `YulangClosure.OriginalScopedClosure.prepare_residual,
    `YulangClosure.OriginalScopedClosure.opened_readback,
    `YulangClosure.OriginalScopedClosure.opened_restore_fields,
    `YulangClosure.OriginalScopedClosure.open_publication_of_readbacks,
    `YulangClosure.OriginalScopedClosure.opened_alias_same_description,
    `YulangClosure.OriginalScopedClosure.opened_source_residual,
    `YulangClosure.OriginalScopedClosure.actual_annotated_publication,
    `YulangClosure.OriginalScopedClosure.actual_annotated_copy,
    `YulangClosure.OriginalScopedClosure.actual_annotated_export_opened]
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
    logInfo m!"YULANG_SCOPED_ROOT_REVIEW_BEGIN {name}"
    let id := mkIdent name
    elabCommand (← `(#check @$id))
    elabCommand (← `(#print axioms $id))
    for ax in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "unapproved axiom in {name}: {ax}"
    logInfo m!"YULANG_SCOPED_ROOT_REVIEW_END {name}"
  logInfo m!"YULANG_SCOPED_ROOT_REVIEW_COUNT declarations={targets.size} theorems={theorems}"
