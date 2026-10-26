import Lean.Elab.Command
import Lean.Util.CollectAxioms
import YulangClosure.InferenceProofs

/-! Exact originating-module audit, including private and generated theorems.
Run `lake build` followed by `lake env lean -j1 -M1024 AuditInferenceProofs.lean`.
Kernel acceptance does not establish unprovided theorem premises or source meaning.
-/
set_option pp.fullNames true
set_option pp.privateNames true
set_option pp.universes false

open Lean Elab Command

run_cmd do
  let modules : Array Name := #[
    `YulangClosure.BirthLevelSCC,
    `YulangClosure.SimpleSubConstraintSyntax,
    `YulangClosure.SimpleSubConstraintSoundness,
    `YulangClosure.SimpleSubGeneralizationSoundness,
    `YulangClosure.SimpleSubRegularSolutions,
    `YulangClosure.SimpleSubRegularConstraintSoundness,
    `YulangClosure.SimpleSubScopedPublication,
    `YulangClosure.SimpleSubRegularPublication,
    `YulangClosure.SimpleSubRegularDecision,
    `YulangClosure.SimpleSubRegularGraphExtension,
    `YulangClosure.SimpleSubRegularCompletion,
    `YulangClosure.NativeProfileRestriction,
    `YulangClosure.SimpleSubGrowingInference,
    `YulangClosure.SimpleSubLatticeCertificates
  ]
  let roots : Array Name := #[
    `YulangClosure.BirthLevelSCC.finiteReach_iff,
    `YulangClosure.BirthLevelSCC.projection_filter_iff,
    `YulangClosure.BirthLevelSCC.filtered_compression_iff,
    `YulangClosure.BirthLevelSCC.finite_helper_qualifies_iff,
    `YulangClosure.SimpleSub.Sub.subst,
    `YulangClosure.SimpleSub.Store.quotient_pullback,
    `YulangClosure.SimpleSub.extrusion_directed,
    `YulangClosure.SimpleSub.negative_demand_reflection,
    `YulangClosure.SimpleSub.positive_demand_reflection,
    `YulangClosure.SimpleSub.replay_solution_iff,
    `YulangClosure.SimpleSub.Step.sound,
    `YulangClosure.SimpleSub.History.sound,
    `YulangClosure.SimpleSub.History.quotient_sound,
    `YulangClosure.SimpleSub.History.empty_sound,
    `YulangClosure.SimpleSub.Generalization.transport_freshen,
    `YulangClosure.SimpleSub.Generalization.quotient_uses_with_clients,
    `YulangClosure.SimpleSub.Generalization.canonical_quotient_minimum,
    `YulangClosure.SimpleSub.Generalization.canonical_post_uses_disjoint,
    `YulangClosure.SimpleSub.Generalization.minimum_quotient_uses_with_clients,
    `YulangClosure.SimpleSub.Regular.coinduction,
    `YulangClosure.SimpleSub.Regular.regular_unfold,
    `YulangClosure.SimpleSub.Regular.accepted_demands_sound,
    `YulangClosure.SimpleSub.Regular.accepted_joint_relation,
    `YulangClosure.SimpleSub.Regular.regular_trans,
    `YulangClosure.SimpleSub.Regular.regular_refl,
    `YulangClosure.SimpleSub.Regular.Extrusion.sound,
    `YulangClosure.SimpleSub.Regular.accepted_original_demands,
    `YulangClosure.SimpleSub.Regular.accepted_original_joint,
    `YulangClosure.SimpleSub.Regular.accepted_renamed_original,
    `YulangClosure.SimpleSub.Regular.acyclic_original_reconstructed,
    `YulangClosure.SimpleSub.ScopedPublication.reachable_active_image,
    `YulangClosure.SimpleSub.ScopedPublication.publication_clause_image,
    `YulangClosure.SimpleSub.ScopedPublication.publication_with_clients,
    `YulangClosure.SimpleSub.ScopedPublication.metadata_publication_with_clients,
    `YulangClosure.SimpleSub.ScopedPublication.numeric_closure_does_not_imply_guard_closure,
    `YulangClosure.SimpleSub.ScopedPublication.minimum_does_not_imply_guard_closure,
    `YulangClosure.SimpleSub.RegularPublication.findNode_sound,
    `YulangClosure.SimpleSub.RegularPublication.decodeTerm_rename,
    `YulangClosure.SimpleSub.RegularPublication.decode_freshen_transport,
    `YulangClosure.SimpleSub.RegularPublication.checkStore_sound,
    `YulangClosure.SimpleSub.RegularPublication.history_store_sound,
    `YulangClosure.SimpleSub.RegularPublication.decode_function_exact,
    `YulangClosure.SimpleSub.RegularPublication.publication_history_with_clients,
    `YulangClosure.SimpleSub.RegularPublication.checked_publication_with_clients,
    `YulangClosure.SimpleSub.RegularPublication.cyclic_two_uses_and_client,
    `YulangClosure.SimpleSub.RegularDecision.prune_checked,
    `YulangClosure.SimpleSub.RegularDecision.constructed_exact,
    `YulangClosure.SimpleSub.RegularDecision.decideDemands_exact,
    `YulangClosure.SimpleSub.RegularDecision.decided_publication_with_clients,
    `YulangClosure.SimpleSub.RegularExtension.Extends.history,
    `YulangClosure.SimpleSub.RegularCompletion.completeTerm_correct,
    `YulangClosure.SimpleSub.RegularCompletion.completedStore_correct,
    `YulangClosure.SimpleSub.RegularCompletion.completed_publication_with_clients,
    `YulangClosure.NativeProfileRestriction.dependentBind_restriction,
    `YulangClosure.NativeProfileRestriction.valueBind_profile_restriction,
    `YulangClosure.SimpleSub.GrowingInference.GrowingHistory.flatten,
    `YulangClosure.SimpleSub.GrowingInference.completed_growing_store_sound,
    `YulangClosure.SimpleSub.GrowingInference.completed_growing_publication_with_clients,
    `YulangClosure.SimpleSub.Lattice.checkDerivation_iff,
    `YulangClosure.SimpleSub.Lattice.accepts_sound,
    `YulangClosure.SimpleSub.Lattice.accepted_joint_relation,
    `YulangClosure.SimpleSub.Lattice.ofRegular_sub,
    `YulangClosure.SimpleSub.Lattice.Layer.toSub
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
    if count == 0 then
      throwError "empty theorem inventory: {moduleName}"
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
