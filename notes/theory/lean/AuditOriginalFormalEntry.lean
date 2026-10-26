import Lean.Elab.Command
import Lean.Util.CollectAxioms
import YulangClosure.OriginalFormalAdmission
import YulangClosure.OriginalForcedParameter

/-! Complete originating-theorem census for the formal declaration and
actual forced-Return suppliers. This audit does not assert global source
soundness or provide the missing source/native interpretation. -/
set_option pp.fullNames true
set_option pp.privateNames true
set_option pp.universes false
set_option pp.proofs true
open Lean Elab Command

run_cmd do
  let modules := #[`YulangClosure.OriginalFormalAdmission,
    `YulangClosure.OriginalForcedParameter]
  let required := #[
    `YulangClosure.OriginalFormalAdmission.actual_build_from_whole_telescope,
    `YulangClosure.OriginalFormalAdmission.actual_build_selects_formal,
    `YulangClosure.OriginalFormalAdmission.value_entry_body_keeps_contract,
    `YulangClosure.OriginalFormalAdmission.computation_entry_body_keeps_contract,
    `YulangClosure.OriginalFormalAdmission.no_erased_owner_singleton_admission,
    `YulangClosure.OriginalForcedParameter.meaning_force_return_fields,
    `YulangClosure.OriginalForcedParameter.background_force_return_fields,
    `YulangClosure.OriginalForcedParameter.bind_after_force_return_meaning,
    `YulangClosure.OriginalForcedParameter.bind_after_force_return_background]
  let env ← getEnv
  let mut targets : Array Name := #[]
  for moduleName in modules do
    let some index := env.getModuleIdx? moduleName
      | throwError "audited module is not imported: {moduleName}"
    for (name, info) in env.constants.toList do
      if env.getModuleIdxFor? name == some index then
        match info with
        | .thmInfo _ => targets := targets.push name
        | .axiomInfo _ => throwError "project axiom: {name}"
        | _ => pure ()
  for root in required do
    unless targets.contains root do throwError "missing required theorem: {root}"
  for name in targets do
    logInfo m!"YULANG_AUDIT_BEGIN {name}"
    let id := mkIdent name
    elabCommand (← `(#check @$id))
    elabCommand (← `(#print axioms $id))
    for ax in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "unapproved axiom in {name}: {ax}"
    logInfo m!"YULANG_AUDIT_END {name}"
  logInfo m!"YULANG_AUDIT_COUNT {targets.size}"
