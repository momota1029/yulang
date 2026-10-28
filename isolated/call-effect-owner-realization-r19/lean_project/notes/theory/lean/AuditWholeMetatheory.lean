import Lean.Elab.Command
import Lean.Util.CollectAxioms
import YulangClosure.WholeMetatheory

/-!
Complete originating-module audit of the eight 2026-10-26 whole-metatheory
components, including private/generated theorems outside their namespace.

Run `lake build` and then
`lake --no-cache env lean -j1 -M1536 AuditWholeMetatheory.lean`.
The audit's local memory allowance does not change the proof-build settings.
Lazy sourceRules equation helpers can originate in an earlier imported
dependency when these components are combined. Audit their complete family
explicitly as well, so standalone record-audit coverage is retained.
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
    `YulangClosure.OriginalInferenceTermination,
    `YulangClosure.NativeFreshScopeTransport,
    `YulangClosure.SourcePrincipalTransport,
    `YulangClosure.OriginalSourceRecordBoundary,
    `YulangClosure.NativeInferenceProgress
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
    `YulangClosure.OriginalInferenceTermination.drain_projection_not_accessible,
    `YulangClosure.NativeFreshScopeTransport.allocate_extends,
    `YulangClosure.NativeFreshScopeTransport.fresh_extends,
    `YulangClosure.NativeFreshScopeTransport.fresh_injective_on_old,
    `YulangClosure.NativeFreshScopeTransport.fresh_touched_range,
    `YulangClosure.NativeFreshScopeTransport.fresh_copied_disjoint_from_fixed,
    `YulangClosure.NativeFreshScopeTransport.fresh_evaluate,
    `YulangClosure.NativeFreshScopeTransport.fresh_evaluate_and_reuse,
    `YulangClosure.NativeFreshScopeTransport.native_map_not_globally_injective,
    `YulangClosure.NativeFreshScopeTransport.repeated_key_overwrites_without_old_collision,
    `YulangClosure.NativeFreshScopeTransport.external_protection_survives_local_release,
    `YulangClosure.SourcePrincipalTransport.program_call_owners,
    `YulangClosure.SourcePrincipalTransport.actual_body_bindings,
    `YulangClosure.SourcePrincipalTransport.recursive_name_is_monomorphic,
    `YulangClosure.SourcePrincipalTransport.h_call_complete_rule,
    `YulangClosure.SourcePrincipalTransport.recursive_call_complete_rule,
    `YulangClosure.SourcePrincipalTransport.recursive_field_retains_h_suffix,
    `YulangClosure.SourcePrincipalTransport.h_name_source_derivation,
    `YulangClosure.SourcePrincipalTransport.source_owners_after_all_frames,
    `YulangClosure.SourcePrincipalTransport.source_subjects_after_all_frames,
    `YulangClosure.SourcePrincipalTransport.h_return_supplies_current_receiver,
    `YulangClosure.OriginalSourceRecordBoundary.construct_record,
    `YulangClosure.OriginalSourceRecordBoundary.construct_preserves,
    `YulangClosure.OriginalSourceRecordBoundary.common_payload_constructed,
    `YulangClosure.OriginalSourceRecordBoundary.constructed_survivors,
    `YulangClosure.OriginalSourceRecordBoundary.successive_boundaries_survivors,
    `YulangClosure.OriginalSourceRecordBoundary.pure_scan_completes,
    `YulangClosure.OriginalSourceRecordBoundary.constructed_record_execution,
    `YulangClosure.OriginalSourceRecordBoundary.constructed_children_safe,
    `YulangClosure.OriginalSourceRecordBoundary.constructed_record_prefixes,
    `YulangClosure.OriginalSourceRecordBoundary.compile_owner_readback,
    `YulangClosure.OriginalSourceRecordBoundary.compiled_owner_preserves,
    `YulangClosure.OriginalSourceRecordBoundary.compile_owners_exact,
    `YulangClosure.OriginalSourceRecordBoundary.compiled_source_member,
    `YulangClosure.OriginalSourceRecordBoundary.compiled_source_preserves,
    `YulangClosure.OriginalSourceRecordBoundary.constructed_original_boundary,
    `YulangClosure.OriginalSourceRecordBoundary.Witness.original_boundary_owners,
    `YulangClosure.OriginalSourceRecordBoundary.Witness.original_source_constructs_both,
    `YulangClosure.OriginalSourceRecordBoundary.Witness.exact_source_programs,
    `YulangClosure.OriginalSourceRecordBoundary.Witness.source_sequence_does_not_resurrect,
    `YulangClosure.OriginalSourceRecordBoundary.Witness.input_typed,
    `YulangClosure.OriginalSourceRecordBoundary.Witness.original_source_sequence_typed,
    `YulangClosure.OriginalSourceRecordBoundary.Witness.absent_common_is_statically_compared,
    `YulangClosure.OriginalSourceRecordBoundary.Witness.nested_identity_and_record_construct,
    `YulangClosure.NativeInferenceProgress.source_context_atom,
    `YulangClosure.NativeInferenceProgress.admitted_context_atom,
    `YulangClosure.NativeInferenceProgress.filter_bound_identity,
    `YulangClosure.NativeInferenceProgress.decompose_fibers_identity,
    `YulangClosure.NativeInferenceProgress.decompose_children_atom,
    `YulangClosure.NativeInferenceProgress.value_port_context_atom,
    `YulangClosure.NativeInferenceProgress.total_next,
    `YulangClosure.NativeInferenceProgress.total_reject,
    `YulangClosure.NativeInferenceProgress.total_finish,
    `YulangClosure.NativeInferenceProgress.total_bind,
    `YulangClosure.NativeInferenceProgress.atomic_scan_clean,
    `YulangClosure.NativeInferenceProgress.replay_scan_clean,
    `YulangClosure.NativeInferenceProgress.shallow_scan_clean,
    `YulangClosure.NativeInferenceProgress.consume_context_closure,
    `YulangClosure.NativeInferenceProgress.expand_consumes,
    `YulangClosure.NativeInferenceProgress.native_expand_context_closure,
    `YulangClosure.NativeInferenceProgress.signature_fiber_atom,
    `YulangClosure.NativeInferenceProgress.post_atom,
    `YulangClosure.NativeInferenceProgress.transport_atom,
    `YulangClosure.NativeInferenceProgress.replay_context_shallow,
    `YulangClosure.NativeInferenceProgress.renamed_atom,
    `YulangClosure.NativeInferenceProgress.step_invariant,
    `YulangClosure.NativeInferenceProgress.reachable_context_closure,
    `YulangClosure.NativeInferenceProgress.atom_extension,
    `YulangClosure.NativeInferenceProgress.shallow_extension,
    `YulangClosure.NativeInferenceProgress.invariant_extension,
    `YulangClosure.NativeInferenceProgress.growing_context_closure,
    `YulangClosure.NativeInferenceProgress.fresh_prefix_constructed
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
  for index in List.range 46 do
    let name := Name.str `YulangClosure.OriginalSource.sourceRules s!"eq_{index + 1}"
    match env.find? name with
    | some (.thmInfo _) => pure ()
    | _ => throwError "missing shared source-rule theorem: {name}"
    unless targets.contains name do
      targets := targets.push name
      logInfo m!"YULANG_AUDIT_SHARED {name}"
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
