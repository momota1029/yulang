import Lean.Elab.Command
import Lean.Util.CollectAxioms
import YulangClosure.WholeMetatheory

/-!
Complete originating-module audit of the four 2026-10-26 whole-metatheory
components, including private/generated theorems outside their namespace.

Run `lake build` and then
`lake --no-cache env lean -j1 -M1536 AuditWholeMetatheory.lean`.
The audit's local memory allowance does not change the proof-build settings.
It prints every complete theorem type and complete axiom list, rejects project
axioms, checks the required public roots and rejects every axiom outside Lean's
standard logical whitelist. This audit does not prove omitted source premises.
-/
set_option pp.fullNames true
set_option pp.privateNames true
set_option pp.universes false
set_option pp.proofs true

open Lean Elab Command

run_cmd do
  let modules : Array Name := #[
    `YulangClosure.NativeScopeTransformer,
    `YulangClosure.OriginalEffectHygiene,
    `YulangClosure.OriginalPrincipality,
    `YulangClosure.OriginalInferenceTermination
  ]
  let roots : Array Name := #[
    `YulangClosure.NativeScopeTransformer.evaluate_then,
    `YulangClosure.NativeScopeTransformer.compiled_execution,
    `YulangClosure.NativeScopeTransformer.evaluate_rename,
    `YulangClosure.NativeScopeTransformer.local_support_injection_is_insufficient,
    `YulangClosure.OriginalEffectHygiene.source_publication_constructs_replay,
    `YulangClosure.OriginalEffectHygiene.published_execution_judgment,
    `YulangClosure.OriginalEffectHygiene.generated_new_use_keeps_original_publication,
    `YulangClosure.OriginalEffectHygiene.Native.return_then_name_cannot_revive,
    `YulangClosure.SimpleSub.OriginalPrincipality.joint_descent_iff_fiber_constant,
    `YulangClosure.SimpleSub.OriginalPrincipality.quotient_uses_complete_on_fiber,
    `YulangClosure.SimpleSub.OriginalPrincipality.joint_solution_coverage_iff,
    `YulangClosure.SimpleSub.OriginalPrincipality.TwoUseExample.constructive_two_use_descent,
    `YulangClosure.OriginalInferenceTermination.scanStep_varying_tables_wellFounded,
    `YulangClosure.OriginalInferenceTermination.scanLoop_eq_total,
    `YulangClosure.OriginalInferenceTermination.scanTotal_execution,
    `YulangClosure.OriginalInferenceTermination.constructed_context_children,
    `YulangClosure.OriginalInferenceTermination.contextTraversal_varying_tables_wellFounded,
    `YulangClosure.OriginalInferenceTermination.drain_projection_not_accessible
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
            if targets.contains name then
              throwError "duplicate theorem: {name}"
            targets := targets.push name
            count := count + 1
        | .axiomInfo _ => throwError "project axiom: {name}"
        | _ => pure ()
    if count == 0 then throwError "empty theorem inventory: {moduleName}"
    logInfo m!"YULANG_AUDIT_MODULE {moduleName} {count}"
  for root in roots do
    unless targets.contains root do
      throwError "missing required theorem: {root}"
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
