import Yulang.GeneralDictionaryReservedNominalRefresh

/-! Current dictionary after a real carrier-changing nominal refresh, through
scalar-head structure and recorded request provenance. No Local, Stable, or
executor-exactness premise is used. -/
namespace Yulang.GeneralDictionaryReservedRefreshedEvidence
open GeneralDictionaryFiniteObservedExampleReserved
open GeneralDictionaryFiniteObservedExampleReservedPositive
open GeneralDictionaryReservedNominalRefresh
open GeneralDictionaryFiniteObservedExample (registry declaration checked equation interpretation)
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralNominalSaturationState GeneralDictionaryRecursiveEvidence

noncomputable abbrev current := refreshed.current.context
noncomputable abbrev shape : GeneralDictionaryProvenanceScalarBranch.Shape current root declaration where
  role := rfl
  slot := (1 : Fin 3)
  base := .int
  noNominal := rfl
  head := rfl
  inputs := rfl
  query := by
    change GeneralNominalInspection.queries state interpretation declaration = [.scalar .int]
    simp [GeneralNominalInspection.queries,GeneralDeclarations.Declaration.normalHead,
      GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,
      GeneralNominalInspection.translate,interpretation,GeneralNominalExamples.interpretation]
  located := by decide +kernel
  defined := by
    intro output member
    have same := List.mem_singleton.mp member
    subst output
    exact ⟨equation,List.mem_singleton_self _,rfl⟩

theorem metadata : Metadata registry current :=
  GeneralDictionaryFiniteObservedExample.metadata

theorem recorded : packet ∈ refreshed.current.packets := packet_recorded

theorem requests_exact (capture : GeneralNominalAllocation.Bindings) :
    GeneralNominalMaterialization.requests current.state registry root declaration checked capture = [request] := by
  rw [GeneralDictionaryObservedScalarRequests.requests_root _ _ _ _ _ _ (by intro clause member; cases member)]
  rfl

theorem covered : GeneralDictionaryRecordedBatchModels.Covered refreshed.current [request] := by
  intro r member
  obtain ⟨prior,present,requested,free⟩ := GeneralDictionaryReservedMixedProvenance.reserved_covered r member
  exact ⟨prior,present,requested,free⟩

theorem supported : GeneralDictionaryRequestProvenance.Supported registry root refreshed
    (GeneralNominalMaterialization.requests current.state registry root declaration checked
      (bindings current.state (report current declaration [(shape.slot,shape.slot)]))) := by
  rw [requests_exact]
  exact GeneralDictionaryRequestProvenance.supported_of_recorded registry root refreshed [request] covered

theorem current_instance (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : Models refreshed.current assignment) :
    Instance registry current assignment root declaration.id [] := by
  have result := GeneralDictionaryProvenanceScalarBranch.instance_of_shape registry root root refreshed
    refreshed_reachable declaration (by simp) checked shape supported metadata assignment valid
  have empty := GeneralDictionaryLinearLeaf.children_empty current registry root declaration checked rfl
    (bindings current.state (report current declaration [(shape.slot,shape.slot)]))
  simpa only [empty] using result

theorem current_evidence (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : Models refreshed.current assignment) :
    Evidence registry current assignment root (.node declaration.id []) :=
  evidence_node registry current assignment root declaration.id [] [] (current_instance assignment valid) .nil

theorem reachable_inhabited_dictionary :
    B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary GeneralDeclarationExamples.roles) registry root refreshed ∧
    Models refreshed.current positive ∧ GeneralNominalState.Known current.state 2 ∧
    Evidence registry current positive root (.node declaration.id []) :=
  ⟨refreshed_reachable,refreshed_inhabited,output_known,current_evidence positive refreshed_inhabited⟩
end Yulang.GeneralDictionaryReservedRefreshedEvidence
