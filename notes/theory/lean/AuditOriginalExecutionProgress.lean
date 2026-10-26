import Lean.Elab.Command
import Lean.Util.CollectAxioms
import YulangClosure.OriginalIdentityRealization
import YulangClosure.OriginalReplayDrain
import YulangClosure.OriginalDrainBoundary
import YulangClosure.OriginalReplayBoundary

/-! Complete origin-based theorem census for the next original execution
suppliers. Private and generated theorem constants are included. Every type
and transitive axiom set is printed; required application roots are checked.
The audit establishes these conditional declarations, not the unresolved
whole-language source/native correspondence or original global termination. -/
set_option pp.fullNames true
set_option pp.privateNames true
set_option pp.universes false
set_option pp.proofs true
set_option pp.deepTerms true
set_option pp.maxSteps 1000000
open Lean Elab Command

private def auditModule (moduleName : Name) (required : Array Name) : CommandElabM Unit := do
  let env ← getEnv
  let some index := env.getModuleIdx? moduleName
    | throwError "audited module is not imported: {moduleName}"
  let mut declarations : Nat := 0
  let mut targets : Array Name := #[]
  for (name, info) in env.constants.toList do
    if env.getModuleIdxFor? name == some index then
      declarations := declarations + 1
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
  logInfo m!"YULANG_MODULE_COUNT {moduleName} declarations={declarations} theorems={targets.size}"

run_cmd auditModule `YulangClosure.OriginalIdentityRealization #[
  `YulangClosure.OriginalIdentityRealization.generated_identity_name_realization,
  `YulangClosure.OriginalIdentityRealization.receipt_origin_carrier,
  `YulangClosure.OriginalIdentityRealization.realized_name_future_function]

run_cmd auditModule `YulangClosure.OriginalReplayDrain #[
  `YulangClosure.OriginalReplayDrain.ordinary_return_issues_all,
  `YulangClosure.OriginalReplayDrain.synchronous_delivery_has_real_return,
  `YulangClosure.OriginalReplayDrain.synchronous_consume_normal_control,
  `YulangClosure.OriginalReplayDrain.function_four_ports_before_empty,
  `YulangClosure.OriginalReplayDrain.replay_relation_processed]

run_cmd auditModule `YulangClosure.OriginalDrainBoundary #[
  `YulangClosure.OriginalDrainBoundary.step_keeps_working,
  `YulangClosure.OriginalDrainBoundary.losing_working_has_boundary,
  `YulangClosure.OriginalDrainBoundary.removal_has_boundary]

run_cmd auditModule `YulangClosure.OriginalReplayBoundary #[
  `YulangClosure.OriginalReplayBoundary.queued_at_first_boundary,
  `YulangClosure.OriginalReplayBoundary.ordinary_relation_at_first_boundary,
  `YulangClosure.OriginalReplayBoundary.function_four_ports_at_first_boundary]
