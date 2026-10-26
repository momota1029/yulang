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
    `YulangClosure.SimpleSubLatticeCertificates,
    `YulangClosure.SimpleSubLatticeInference,
    `YulangClosure.SimpleSubLatticeDecision,
    `YulangClosure.SimpleSubLatticeGrowingInference,
    `YulangClosure.NativeRowModel,
    `YulangClosure.RecordBoundaryPreservation,
    `YulangClosure.NativeReplayCoverage
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
    `YulangClosure.SimpleSub.Lattice.Layer.toSub,
    `YulangClosure.SimpleSub.LatticeInference.decode_function_exact,
    `YulangClosure.SimpleSub.LatticeInference.publication_history_with_clients,
    `YulangClosure.SimpleSub.LatticeInference.ofRegular_history,
    `YulangClosure.SimpleSub.LatticeInference.decodeTerm_ofRegular,
    `YulangClosure.SimpleSub.LatticeInference.Completion.completedStore_correct,
    `YulangClosure.SimpleSub.LatticeInference.Completion.completed_publication_with_clients,
    `YulangClosure.SimpleSub.LatticeDecision.constructed_checked,
    `YulangClosure.SimpleSub.LatticeDecision.constructed_exact,
    `YulangClosure.SimpleSub.LatticeDecision.regular_unfold,
    `YulangClosure.SimpleSub.LatticeDecision.decideDemands_exact,
    `YulangClosure.SimpleSub.LatticeDecision.decided_joint_relation,
    `YulangClosure.SimpleSub.LatticeInference.Completion.Extends.approx,
    `YulangClosure.SimpleSub.LatticeInference.Completion.Extends.regular,
    `YulangClosure.SimpleSub.LatticeGrowingInference.GrowingHistory.flatten,
    `YulangClosure.SimpleSub.LatticeGrowingInference.GrowingHistory.decided_sound,
    `YulangClosure.SimpleSub.LatticeGrowingInference.completed_decided_growing_store_sound,
    `YulangClosure.SimpleSub.LatticeGrowingInference.completed_decided_growing_publication_with_clients,
    `YulangClosure.SimpleSub.NativeRowModel.canonical_bounds,
    `YulangClosure.SimpleSub.NativeRowModel.canonical_valid,
    `YulangClosure.SimpleSub.NativeRowModel.canonical_guarded,
    `YulangClosure.SimpleSub.NativeRowModel.canonical_guard_checked,
    `YulangClosure.SimpleSub.NativeRowModel.canonical_decided,
    `YulangClosure.SimpleSub.NativeRowModel.canonical_interval,
    `YulangClosure.SimpleSub.NativeRowModel.canonical_completed_publication,
    `YulangClosure.SimpleSub.NativeRowModel.canonical_decoded_store,
    `YulangClosure.SimpleSub.NativeRowModel.recursive_store_constructed,
    `YulangClosure.SimpleSub.NativeRowModel.recursive_decision_constructed,
    `YulangClosure.SimpleSub.NativeRowModel.alias_cycle_constructed,
    `YulangClosure.SimpleSub.NativeRowModel.lower_join_upper_meet_need_not_equal,
    `YulangClosure.RecordBoundary.compileField_sound,
    `YulangClosure.RecordBoundary.compile_sound,
    `YulangClosure.RecordBoundary.common_field_resolved,
    `YulangClosure.RecordBoundary.required_input_present,
    `YulangClosure.RecordBoundary.fieldRun_preserves,
    `YulangClosure.RecordBoundary.run_preserves,
    `YulangClosure.RecordBoundary.outputTyped_visible,
    `YulangClosure.RecordBoundary.compiled_run_preserves,
    `YulangClosure.RecordBoundary.fieldRun_presence,
    `YulangClosure.RecordBoundary.run_survivors,
    `YulangClosure.RecordBoundary.composed_survivors,
    `YulangClosure.RecordBoundary.execute_runs,
    `YulangClosure.RecordBoundary.Witness.direct_comparison_nontransitive,
    `YulangClosure.RecordBoundary.Witness.accepted_paths_have_different_views,
    `YulangClosure.NativeReplayCoverage.mem_product,
    `YulangClosure.NativeReplayCoverage.replay_quadrants_cover,
    `YulangClosure.NativeReplayCoverage.incoming_replay_covers_all,
    `YulangClosure.NativeReplayCoverage.empty_covered,
    `YulangClosure.NativeReplayCoverage.step_covered,
    `YulangClosure.NativeReplayCoverage.run_covered,
    `YulangClosure.NativeReplayCoverage.committed_routes_covered,
    `YulangClosure.NativeReplayCoverage.completed_routes_cover,
    `YulangClosure.NativeReplayCoverage.scan_direct,
    `YulangClosure.NativeReplayCoverage.scan_exact_without_direct_growth,
    `YulangClosure.NativeReplayCoverage.temporal_three_case_coverage,
    `YulangClosure.NativeReplayCoverage.equal_level_row_bound_is_upper,
    `YulangClosure.NativeReplayCoverage.function_children_exact,
    `YulangClosure.NativeReplayCoverage.live_concat_saved_count_misses_atom
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
