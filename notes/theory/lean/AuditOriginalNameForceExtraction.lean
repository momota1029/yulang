import Lean.Elab.Command
import Lean.Util.CollectAxioms
import YulangClosure.OriginalNameForceExtraction

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
  let moduleName := `YulangClosure.OriginalNameForceExtraction
  let some index := env.getModuleIdx? moduleName
    | throwError "audited module is not imported"
  let required : Array Name := #[
    `YulangClosure.OriginalNameForceExtraction.run_succ,
    `YulangClosure.OriginalNameForceExtraction.every_prefix,
    `YulangClosure.OriginalNameForceExtraction.failed_prefix,
    `YulangClosure.OriginalNameForceExtraction.missing_binding,
    `YulangClosure.OriginalNameForceExtraction.uninitialized_binding,
    `YulangClosure.OriginalNameForceExtraction.dispatch_failure,
    `YulangClosure.OriginalNameForceExtraction.initialized_evaluate,
    `YulangClosure.OriginalNameForceExtraction.dangling_address,
    `YulangClosure.OriginalNameForceExtraction.owner_from_allocation,
    `YulangClosure.OriginalNameForceExtraction.other_force_unchanged,
    `YulangClosure.OriginalNameForceExtraction.other_incidence_unchanged,
    `YulangClosure.OriginalNameForceExtraction.checked_domain_unchanged,
    `YulangClosure.OriginalNameForceExtraction.actual_admission_unchanged,
    `YulangClosure.OriginalNameForceExtraction.prior_observation_unchanged,
    `YulangClosure.OriginalNameForceExtraction.other_owners_unchanged,
    `YulangClosure.OriginalNameForceExtraction.every_owned_prefix,
    `YulangClosure.OriginalNameForceExtraction.force_incidence,
    `YulangClosure.OriginalNameForceExtraction.project_run,
    `YulangClosure.OriginalNameForceExtraction.prefix_event,
    `YulangClosure.OriginalNameForceExtraction.prefix_valid,
    `YulangClosure.OriginalNameForceExtraction.prefix_result,
    `YulangClosure.OriginalNameForceExtraction.prefix_form,
    `YulangClosure.OriginalNameForceExtraction.failed_observation,
    `YulangClosure.OriginalNameForceExtraction.return_receipt,
    `YulangClosure.OriginalNameForceExtraction.name_delay_from_native_prefixes,
    `YulangClosure.OriginalNameForceExtraction.dangling_view,
    `YulangClosure.OriginalNameForceExtraction.missing_view,
    `YulangClosure.OriginalNameForceExtraction.mismatched_view,
    `YulangClosure.OriginalNameForceExtraction.captured_by_bind_bound,
    `YulangClosure.OriginalNameForceExtraction.bound_name_evaluate,
    `YulangClosure.OriginalNameForceExtraction.allocated_bound_force]
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
    logInfo m!"YULANG_NAME_FORCE_ROOT_REVIEW_BEGIN {name}"
    let id := mkIdent name
    elabCommand (← `(#check @$id))
    elabCommand (← `(#print axioms $id))
    for ax in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "unapproved axiom in {name}: {ax}"
    logInfo m!"YULANG_NAME_FORCE_ROOT_REVIEW_END {name}"
  logInfo m!"YULANG_NAME_FORCE_ROOT_REVIEW_COUNT declarations={targets.size} theorems={theorems}"
