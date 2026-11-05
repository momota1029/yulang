import Yulang
import Lean

/- The allowlist applies to every declaration from a Yulang module, including
private implementation declarations, not only the principal theorems below. -/
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      let moduleName := environment.header.moduleNames[index.toNat]!
      if (`Yulang).isPrefixOf moduleName then
        checked := checked + 1
        let axioms ← collectAxioms name
        for dependency in axioms do
          unless allowed.contains dependency do
            throwError "Forbidden axiom dependency: {name} depends on {dependency}"
  if checked = 0 then
    throwError "The audit did not find any Yulang declarations"
  logInfo m!"Axiom allowlist passed for {checked} declarations from Yulang modules"

#print axioms Yulang.Inference.Formula.holds_subst
#print axioms Yulang.Inference.EnvRel.lift
#print axioms Yulang.Inference.generate_models_iff_typing
#print axioms Yulang.Inference.principal_exact
#print axioms Yulang.Inference.principal_most_general
#print axioms Yulang.Inference.unbound_not_typable
#print axioms Yulang.Polymorphism.generated_effectful_alias_accepted
#print axioms Yulang.Polymorphism.generated_effectful_alias_cannot_erase_io
#print axioms Yulang.Structural.scalar_preserved
#print axioms Yulang.Structural.record_width
#print axioms Yulang.Structural.generated_heterogeneous_union_satisfied
#print axioms Yulang.Structural.generated_heterogeneous_int_rejected
#print axioms Yulang.Structural.generated_scalar_spread_rejected
#print axioms Yulang.Annotations.check_iff
#print axioms Yulang.Annotations.negative_permission_does_not_inject
#print axioms Yulang.Annotations.no_substitution_invariant_extensional_check
#print axioms Yulang.AnnotationSnapshots.Observation.check_exact
#print axioms Yulang.AnnotationSnapshots.annotation_exact
#print axioms Yulang.AnnotationSnapshots.instantiated_row_meaning
#print axioms Yulang.AnnotationSnapshots.emit_subst
#print axioms Yulang.AnnotationSnapshots.principal_observed_exact
#print axioms Yulang.AnnotationSnapshots.valid_observation_adds_no_instantiation_bound
#print axioms Yulang.AnnotationSnapshots.invalid_observation_rejects_all_instantiations
#print axioms Yulang.AnnotationSnapshots.Examples.t3_later_instantiation_accepts
#print axioms Yulang.AnnotationSnapshots.Examples.t3_new_observation_would_reject
#print axioms Yulang.RecursiveInference.FullAnnotation.scheme_instances
#print axioms Yulang.RecursiveInference.captured_type_ignores_local_rows
#print axioms Yulang.RecursiveInference.generateSCC_exact
#print axioms Yulang.RecursiveInference.closeSCC_exact
#print axioms Yulang.RecursiveInference.inferUnannotatedSCC_exact
#print axioms Yulang.HigherOrder.guard_arrow_noncapture
#print axioms Yulang.HigherOrder.list_callback_noncapture
#print axioms Yulang.HigherOrder.Examples.fresh_roundtrip_is_not_symmetric
#print axioms Yulang.Directed.release_protect
#print axioms Yulang.Directed.protect_release
#print axioms Yulang.Directed.legacy_capture_agrees
#print axioms Yulang.Directed.Computation.default_zero_boundary_noncapture
#print axioms Yulang.Directed.Computation.shallowHandle_bounded
#print axioms Yulang.Directed.Computation.protect_bounded_iff
#print axioms Yulang.Directed.Computation.release_bounded_iff
#print axioms Yulang.DirectedHigherOrder.transport_opposite
#print axioms Yulang.DirectedHigherOrder.release_guard
#print axioms Yulang.DirectedHigherOrder.guard_release
#print axioms Yulang.DirectedHigherOrder.guard_arrow_noncapture
#print axioms Yulang.DirectedHigherOrder.Examples.contravariant_debt_preserves_local_callback
#print axioms Yulang.EffectInference.request_constraints_exact
#print axioms Yulang.EffectInference.boundary_constraints_exact
#print axioms Yulang.EffectInference.handler_constraints_exact
#print axioms Yulang.EffectInference.generated_handler_composes_effect_bounds
#print axioms Yulang.RowInference.RowExpr.eval_subst
#print axioms Yulang.RowInference.request_constraints_exact
#print axioms Yulang.RowInference.boundary_constraints_exact
#print axioms Yulang.RowInference.handler_constraints_exact
#print axioms Yulang.Inference.EnvRel.rename
#print axioms Yulang.EffectInference.local_result_no_escape
#print axioms Yulang.EffectInference.local_outer_environment
#print axioms Yulang.EffectInference.poly_request_constraints_exact
#print axioms Yulang.EffectInference.poly_handler_constraints_exact
#print axioms Yulang.RowInference.poly_request_constraints_exact
#print axioms Yulang.RowInference.poly_handler_constraints_exact
#print axioms Yulang.SignedStructural.generated_poly_request_at_any_type
#print axioms Yulang.SignedStructural.generated_poly_requests_independent
#print axioms Yulang.SignedStructural.generated_poly_handler_resumes_payload
#print axioms Yulang.SignedStructural.generated_poly_handler_payload_escape_rejected
#print axioms Yulang.RowInference.generated_signed_handler_composes_effect_bounds
#print axioms Yulang.RowInference.signed_eval_release_protect
#print axioms Yulang.RowInference.signed_eval_protect_release
#print axioms Yulang.RowInference.signed_negative_debt_survives
#print axioms Yulang.SignedStructural.generated_request_satisfied
#print axioms Yulang.SignedStructural.generated_request_without_effect_rejected
#print axioms Yulang.SignedStructural.generated_release_retains_debt
#print axioms Yulang.SignedStructural.generated_release_cannot_drop_debt
#print axioms Yulang.Effects.capture_partition
#print axioms Yulang.Effects.residual_least
#print axioms Yulang.Effects.default_boundary_noncapture
#print axioms Yulang.Effects.visible_head_protected_tail
#print axioms Yulang.Effects.release_preserves_other
#print axioms Yulang.Effects.release_protect_row
#print axioms Yulang.Effects.unhandled_operation_retains_family
#print axioms Yulang.Effects.RowExpr.eval_subst
#print axioms Yulang.Effects.Computation.default_boundary_operational_noncapture
#print axioms Yulang.Effects.Computation.shallow_resume_is_original
#print axioms Yulang.Effects.Computation.shallowHandle_bounded
#print axioms Yulang.Effects.Examples.nested_sub_returns_zero
#print axioms Yulang.Effects.Examples.erasing_protection_changes_result
#print axioms Yulang.Horn.check_iff
#print axioms Yulang.Horn.mem_valuations
#print axioms Yulang.Horn.intersection_models
#print axioms Yulang.Horn.solve_principal
#print axioms Yulang.Horn.solve_eq_none_iff
#print axioms Yulang.Horn.solve_complete
#print axioms Yulang.Horn.solve_eq_some_iff
#print axioms Yulang.FiniteReachability.closure_least
#print axioms Yulang.FiniteReachability.closure_exact
#print axioms Yulang.FiniteReachability.Reach.append
#print axioms Yulang.FiniteReachability.closure_empty
#print axioms Yulang.FiniteReachability.closure_congr
#print axioms Yulang.EvaluationOrder.references_exact
#print axioms Yulang.EvaluationOrder.dependencies_exact
#print axioms Yulang.EvaluationOrder.checkAt_exact
#print axioms Yulang.EvaluationOrder.check_exact
#print axioms Yulang.EvaluationOrder.accepted_initializer_earlier
#print axioms Yulang.EvaluationOrder.accepted_statement_available
#print axioms Yulang.EvaluationOrder.computed_self_dependency_rejected
#print axioms Yulang.EvaluationOrder.future_computed_dependency_rejected
#print axioms Yulang.EvaluationOrder.lambda_no_dependency
#print axioms Yulang.EvaluationOrder.applied_lambda_preserves_body_dependency
#print axioms Yulang.EvaluationOrder.passed_function_dependency
#print axioms Yulang.EvaluationOrder.Examples.computed_cycle_rejected
#print axioms Yulang.EvaluationOrder.Examples.curried_inline_lambda_application_rejected
#print axioms Yulang.Methods.resolve_unique_iff
#print axioms Yulang.Methods.resolve_missing_iff
#print axioms Yulang.Methods.resolve_ambiguous_iff
#print axioms Yulang.Methods.select_ext
#print axioms Yulang.Methods.resolve_perm
#print axioms Yulang.Variants.partition
#print axioms Yulang.Variants.residual_greatest
#print axioms Yulang.Variants.residual_least
#print axioms Yulang.Variants.residual_constraint_iff
#print axioms Yulang.Variants.residual_empty_iff
#print axioms Yulang.Variants.residual_map_payload

#print axioms Yulang.Variants.Merged.normalize_unique
#print axioms Yulang.Variants.Merged.lookup_normalize
#print axioms Yulang.Variants.Merged.tags_normalize
#print axioms Yulang.Variants.Merged.mergeAll_eq_none_iff
#print axioms Yulang.Variants.Merged.normalize_residual
#print axioms Yulang.Variants.Merged.selected_normalize
#print axioms Yulang.Variants.Merged.mem_residual_normalize_iff
#print axioms Yulang.Variants.Merged.handled_no_residual_payload
#print axioms Yulang.Variants.Merged.residual_empty_iff
#print axioms Yulang.Variants.Merged.case_exact_tags_empty
#print axioms Yulang.Variants.Merged.case_omitted_tag
#print axioms Yulang.Variants.Merged.case_omitted_normalize
#print axioms Yulang.Variants.Merged.normalize_map
#print axioms Yulang.Variants.Merged.residual_map
#print axioms Yulang.Variants.Merged.variant_union_upper_bound
#print axioms Yulang.Variants.Merged.Examples.id_merge
#print axioms Yulang.Variants.Merged.Examples.id_handled_entirely
#print axioms Yulang.Variants.Merged.Examples.str_leaves_num

#print axioms Yulang.Roles.Term.subst_size
#print axioms Yulang.Roles.args_subst_size
#print axioms Yulang.Roles.constraint_variables_in_head
#print axioms Yulang.Roles.size_decreases
#print axioms Yulang.Roles.matches_iff
#print axioms Yulang.Roles.matched_constraint
#print axioms Yulang.Roles.wellFormed_cons
#print axioms Yulang.Roles.resolve
#print axioms Yulang.Roles.resolve_resolved_iff
#print axioms Yulang.Roles.resolve_noImpl_iff
#print axioms Yulang.Roles.resolve_sound
#print axioms Yulang.Roles.resolve_complete
#print axioms Yulang.Roles.resolve_resolved_iff_derives
#print axioms Yulang.Roles.head_overlap_iff
#print axioms Yulang.Roles.resolve_ambiguous_iff
#print axioms Yulang.Roles.Examples.nested_list_resolved
#print axioms Yulang.Roles.Examples.missing_str_noImpl
#print axioms Yulang.Roles.Examples.rigid_variable_noImpl
#print axioms Yulang.Roles.Examples.duplicating_not_wellFormed
#print axioms Yulang.Roles.Examples.bad_not_wellFormed
#print axioms Yulang.Roles.Examples.bad_no_derives
#print axioms Yulang.Roles.Examples.bad_foo_int_no_derives
#print axioms Yulang.Roles.Examples.overlap_ambiguous
#print axioms Yulang.Roles.Examples.overlap_before_constraints

#print axioms Yulang.Roles.assoc_rhs_closed
#print axioms Yulang.Roles.assoc_rhs_matching
#print axioms Yulang.Roles.default_rhs_closed
#print axioms Yulang.Roles.assoc_independent_of_constraints
#print axioms Yulang.Roles.assoc_explicit_eq
#print axioms Yulang.Roles.assoc_total_closed
#print axioms Yulang.Roles.assoc_unique
#print axioms Yulang.Roles.assoc_derivation_agrees
#print axioms Yulang.Roles.assoc_derivations_unique
#print axioms Yulang.Roles.assoc_explicit_size
#print axioms Yulang.Roles.AssocExamples.str_value
#print axioms Yulang.Roles.AssocExamples.box_value
#print axioms Yulang.Roles.AssocExamples.default_value
#print axioms Yulang.Roles.AssocExamples.parameter_default_value
#print axioms Yulang.Roles.AssocExamples.explicit_overrides_default
#print axioms Yulang.Roles.AssocExamples.rigid_goal_value
#print axioms Yulang.Roles.AssocExamples.escaping_not_assocWellFormed
#print axioms Yulang.Roles.AssocExamples.missing_not_assocWellFormed
#print axioms Yulang.Roles.AssocExamples.undeclared_not_assocWellFormed

#print axioms Yulang.RoleConstraints.resolve_exact
#print axioms Yulang.RoleConstraints.Store.check_exact
#print axioms Yulang.RoleConstraints.Store.add_comm
#print axioms Yulang.RoleConstraints.Store.add_idempotent
#print axioms Yulang.RoleConstraints.Store.permutation_preserves_solutions
#print axioms Yulang.RoleConstraints.add_associated_exact
#print axioms Yulang.RoleConstraints.selected_impl_adds_ordinary_equation
#print axioms Yulang.RoleConstraints.AssocExamples.conflicting_constraint_rejects
#print axioms Yulang.CheckedRoles.checkOccurrences_exact
#print axioms Yulang.CheckedRoles.checkDatabase_exact
#print axioms Yulang.CheckedRoles.checked_condition_strictly_decreases
#print axioms Yulang.CheckedRoles.invalid_exact
#print axioms Yulang.CheckedRoles.resolve_exact
#print axioms Yulang.CheckedRoles.ambiguous_exact
#print axioms Yulang.CheckedRoles.valid_answer_exists
#print axioms Yulang.CheckedRoles.Examples.invalid_database_rejected_before_lookup
