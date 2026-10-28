import Lean.Elab.Command
import Lean.Util.CollectAxioms
import YulangClosure.OriginalFormalAdmission
import YulangClosure.OriginalForcedParameter
import YulangClosure.OriginalSourceClosure
import YulangClosure.OriginalReturnWorld
import YulangClosure.OriginalPrincipalityResolution
import YulangClosure.OriginalInferenceTerminationResolution

/-! Origin-based census of the six 2026-10-27 proof modules. This prints all
theorem types and transitive axioms, including private/generated theorems.
Passing this audit does not discharge the explicitly quantified hypotheses
or identify the local interpretation with all original source semantics. -/
set_option pp.fullNames true
set_option pp.privateNames true
set_option pp.universes false
set_option pp.proofs true
open Lean Elab Command

/- Each command releases its census before the next module. The combined
import/census uses a local 2 GiB audit limit; the proof modules themselves
are checked at the project's unchanged 1 GiB limit. No kernel-checking
setting changes. The initial 1 GiB audit failure is retained in the report. -/
private def auditModule (moduleName : Name) (required : Array Name) : CommandElabM Unit := do
  let env ← getEnv
  let some index := env.getModuleIdx? moduleName
    | throwError "audited module is not imported: {moduleName}"
  let mut targets : Array Name := #[]
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
  logInfo m!"YULANG_MODULE_COUNT {moduleName} {targets.size}"

run_cmd auditModule `YulangClosure.OriginalFormalAdmission #[
  `YulangClosure.OriginalFormalAdmission.actual_build_from_whole_telescope,
  `YulangClosure.OriginalFormalAdmission.actual_build_selects_formal]

run_cmd auditModule `YulangClosure.OriginalForcedParameter #[
  `YulangClosure.OriginalForcedParameter.bind_after_force_return_meaning,
  `YulangClosure.OriginalForcedParameter.bind_after_force_return_background]

run_cmd auditModule `YulangClosure.OriginalSourceClosure #[
  `YulangClosure.OriginalSourceClosure.generated_value_body_consumer,
  `YulangClosure.OriginalSourceClosure.generated_computation_body_consumer]

run_cmd auditModule `YulangClosure.OriginalReturnWorld #[
  `YulangClosure.OriginalReturnWorld.actual_entry_return_world,
  `YulangClosure.OriginalReturnWorld.delivered_meaning_from_actual_force,
  `YulangClosure.OriginalReturnWorld.delivered_background_from_actual_force]

run_cmd auditModule `YulangClosure.OriginalPrincipalityResolution #[
  `YulangClosure.OriginalPrincipalityResolution.CallBoundary.h_call_requires_certificate,
  `YulangClosure.OriginalPrincipalityResolution.OrderBoundary.coverage_does_not_determine_principality]

run_cmd auditModule `YulangClosure.OriginalInferenceTerminationResolution #[
  `YulangClosure.OriginalInferenceTerminationResolution.earlier_replay_cannot_read_fresh_request]
