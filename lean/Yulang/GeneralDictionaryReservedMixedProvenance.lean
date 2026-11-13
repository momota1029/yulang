import Yulang.GeneralDictionaryReservedEqualityStep
import Yulang.GeneralDictionaryRequestProvenanceTrace

/-! Regression of genuine mixed provenance: source 0 is observed at the reachable
initial snapshot, while reserved source 2 has no initial slot and is justified by
the installed packet. The general batch theorem, then its real Value-trace
transport, supply all-model validity; no semantic request premise is assumed. -/
namespace Yulang.GeneralDictionaryReservedMixedProvenance
open GeneralDictionaryFiniteObservedExampleReserved
open GeneralDictionaryFiniteObservedExampleReservedPositive
open GeneralDictionaryFiniteObservedExample (registry declaration interpretation descriptor query)
open GeneralNominalMaterialization GeneralDictionaryObservedFiniteRequests
open GeneralDictionaryRequestProvenance GeneralDictionaryReservedEqualityStep

abbrev original := GeneralDictionaryFiniteObservedExample.request
abbrev batch : List Request := [original,request]

abbrev source_tree : Tree state 0 query := by
  have h := Tree.nominal (state := state) 0 descriptor rfl (n := 3)
    (fun _ => 1) (fun _ => GeneralNominalInspection.Query.scalar .int)
    (by simp [List.ofFn_succ]) (fun _ => Tree.scalar 1 .int rfl)
  simpa [query,List.ofFn_succ] using h

theorem source_observed : Observed state interpretation [original] := by
  intro r member
  have same := List.mem_singleton.mp member
  subst r
  refine ⟨0,rfl,?_⟩
  change Nonempty (Tree state 0 (GeneralNominalInspection.translate state.constructors interpretation
    (GeneralDeclarationPatterns.normalize original.pattern)))
  rw [show GeneralNominalInspection.translate state.constructors interpretation
    (GeneralDeclarationPatterns.normalize original.pattern) = query from
    GeneralDictionaryFiniteObservedExample.translation]
  exact ⟨source_tree⟩

theorem reserved_covered : GeneralDictionaryRecordedBatchModels.Covered installed.current [request] := by
  intro r member
  have same := List.mem_singleton.mp member
  subst r
  refine ⟨packet,packet_recorded,?_,?_⟩
  · change request ∈ requests state registry root declaration _ _
    rw [actual_requests_exact]
    exact List.mem_singleton_self _
  · change (generated state interpretation [request]).variables = []
    simp [generated,request,GeneralNominalInspection.translate,GeneralDeclarationPatterns.normalize,
      GeneralDeclarationPatterns.normalizeArgs,interpretation,
      GeneralDictionaryFiniteObservedExample.interpretation,GeneralNominalExamples.interpretation,
      GeneralDictionaryFiniteObservedExample.constructors,schema,schemas,Schema.append]

theorem supported : Supported registry root installed batch := by
  intro r member
  change r ∈ [original,request] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact Or.inl ⟨start,⟨start,⟨context,initial_source,rfl⟩,.refl⟩,
      .tail .refl value_install_step,source_observed⟩
  · exact Or.inr reserved_covered

theorem installed_batch_models (capture : GeneralDeclarationDemands.Capture)
    (report : GeneralNominalRecursiveInspection.Report installed.current.context.state)
    (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalSaturationState.Models installed.current assignment) :
    Models installed.current.context.state declaration capture report
      (generated installed.current.context.state installed.current.context.interpretation batch) assignment :=
  GeneralDictionaryRequestProvenance.models registry root installed value_reachable batch supported
    declaration capture report assignment valid

theorem after_batch_models (capture : GeneralDeclarationDemands.Capture)
    (report : GeneralNominalRecursiveInspection.Report after.current.context.state)
    (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalSaturationState.Models after.current assignment) :
    Models after.current.context.state declaration capture report
      (generated after.current.context.state after.current.context.interpretation batch) assignment :=
  GeneralDictionaryRequestProvenanceTrace.models_after_trace registry root installed after
    value_reachable (.tail .refl equality_step) batch supported declaration capture report assignment valid

theorem inhabited_mixed_provenance :
    (¬ Observed state interpretation [request]) ∧
    Supported registry root installed batch ∧
    GeneralNominalSaturationState.Models installed.current positive ∧
    GeneralNominalSaturationState.Models after.current positive :=
  ⟨not_observed,supported,installed_models,(models_iff positive).mpr installed_models⟩
end Yulang.GeneralDictionaryReservedMixedProvenance
