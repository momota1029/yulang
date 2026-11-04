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
#print axioms Yulang.Variants.partition
#print axioms Yulang.Variants.residual_greatest
#print axioms Yulang.Variants.residual_least
#print axioms Yulang.Variants.residual_constraint_iff
#print axioms Yulang.Variants.residual_empty_iff
#print axioms Yulang.Variants.residual_map_payload
