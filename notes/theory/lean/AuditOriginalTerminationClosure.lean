import Lean.Elab.Command
import Lean.Util.CollectAxioms
import YulangClosure.OriginalTerminationClosure

/-! Complete originating-module audit, including private/generated theorems.
Run `lake build +YulangClosure.OriginalTerminationClosure`, then
`lake env lean -j1 -M1024 AuditOriginalTerminationClosure.lean`.
The checker validates the retained-rewrite owner projection; it does not
certify whole-inference termination or rollback/source-history extraction. -/
set_option pp.fullNames true
set_option pp.privateNames true
set_option pp.universes false
set_option pp.proofs true
open Lean Elab Command

run_cmd do
  let moduleName := `YulangClosure.OriginalTerminationClosure
  let roots : Array Name := #[
    `YulangClosure.OriginalTerminationClosure.recordAdmission_retained,
    `YulangClosure.OriginalTerminationClosure.recordRewrite_exact,
    `YulangClosure.OriginalTerminationClosure.retained_excludes_body,
    `YulangClosure.OriginalTerminationClosure.retained_excludes_context_fallback,
    `YulangClosure.OriginalTerminationClosure.fallback_requires_unwritten,
    `YulangClosure.OriginalTerminationClosure.rewrite_initial_valid,
    `YulangClosure.OriginalTerminationClosure.rewrite_step_valid,
    `YulangClosure.OriginalTerminationClosure.rewrite_run_valid,
    `YulangClosure.OriginalTerminationClosure.changed_extrusion_parents_nodup,
    `YulangClosure.OriginalTerminationClosure.changed_extrusion_targets_persistent,
    `YulangClosure.OriginalTerminationClosure.prior_changed_extrusion_excludes_later_body
  ]
  let env ← getEnv
  let some moduleIndex := env.getModuleIdx? moduleName
    | throwError "audited module is not imported: {moduleName}"
  let mut targets : Array Name := #[]
  for (name, info) in env.constants.toList do
    if env.getModuleIdxFor? name == some moduleIndex then
      match info with
      | .thmInfo _ => targets := targets.push name
      | .axiomInfo _ => throwError "project axiom: {name}"
      | _ => pure ()
  if targets.isEmpty then throwError "empty theorem inventory"
  for root in roots do
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
