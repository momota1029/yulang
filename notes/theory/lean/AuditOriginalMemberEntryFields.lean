import Lean.Elab.Command
import Lean.Util.CollectAxioms
import YulangClosure.OriginalMemberEntryFields

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
  let moduleName := `YulangClosure.OriginalMemberEntryFields
  let some index := env.getModuleIdx? moduleName
    | throwError "audited module is not imported"
  let required : Array Name := #[
    `YulangClosure.OriginalMemberEntryFields.component_erases,
    `YulangClosure.OriginalMemberEntryFields.component_residual,
    `YulangClosure.OriginalMemberEntryFields.component_source_reconstruction,
    `YulangClosure.OriginalMemberEntryFields.registered_world,
    `YulangClosure.OriginalMemberEntryFields.registered_installed,
    `YulangClosure.OriginalMemberEntryFields.registered_binding,
    `YulangClosure.OriginalMemberEntryFields.registered_internal_origin,
    `YulangClosure.OriginalMemberEntryFields.registered_one_component,
    `YulangClosure.OriginalMemberEntryFields.registered_whole_residual,
    `YulangClosure.OriginalMemberEntryFields.registered_whole_publications,
    `YulangClosure.OriginalMemberEntryFields.operational_fields_ignore_descriptions,
    `YulangClosure.OriginalMemberEntryFields.registered_preserves_old_binding,
    `YulangClosure.OriginalMemberEntryFields.registered_other_capture,
    `YulangClosure.OriginalMemberEntryFields.registered_provider_captures,
    `YulangClosure.OriginalMemberEntryFields.registered_old_capture_fields,
    `YulangClosure.OriginalMemberEntryFields.registered_shared_witnesses]
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
    logInfo m!"YULANG_MEMBER_ROOT_REVIEW_BEGIN {name}"
    let id := mkIdent name
    elabCommand (← `(#check @$id))
    elabCommand (← `(#print axioms $id))
    for ax in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "unapproved axiom in {name}: {ax}"
    logInfo m!"YULANG_MEMBER_ROOT_REVIEW_END {name}"
  logInfo m!"YULANG_MEMBER_ROOT_REVIEW_COUNT declarations={targets.size} theorems={theorems}"
