import Yulang.GeneralDictionaryMixedCatalogExample

/-! The strict per-request filtering witness has a genuine common assignment.
This remains a raw checked journal example, not a reachability claim. -/
namespace Yulang.GeneralDictionaryMixedCatalogInhabited
open GeneralDictionaryMixedCatalogExample
open GeneralNominalExamples (context state model state_models listDescriptor displayRoot interpretation)
open GeneralNominalRecursiveInspection GeneralNominalRecursiveCandidates GeneralNominalUnaryCaptureFacts
open GeneralNominalMaterialization CommonNominalFullCarrier

theorem target_nonzero (clause : Nat) : target clause ≠ 0 := by
  have positive := GeneralNominalIdentities.source_above_seed (state true).seed
    (GeneralNominalAllocation.origin 100 1 5 (clause+20) 0)
  unfold target GeneralNominalAllocation.source
  omega

theorem query : GeneralNominalInspection.queries (state true) interpretation declaration = [.nominal 0 [.variables [0]]] := by
  simp [GeneralNominalInspection.queries,GeneralDeclarations.Declaration.normalHead,
    GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,
    GeneralNominalInspection.translate,interpretation]

theorem branch : packet.Holds model := by
  have privateModel := private_models (context true) registry displayRoot declaration 0 listDescriptor rfl 0 rfl
    (1,1) rfl query model (state_models true)
  refine ⟨privateModel.1,privateModel.2,?_⟩
  change Models (state true) declaration (GeneralNominalPacketSupport.capture packet)
    (report (context true) declaration [(0,0)]) (GeneralNominalPacketSupport.namedSchema packet) model
  rw [generated_exact,report_exact (context true) declaration 0 listDescriptor rfl 0 (1,1) rfl query]
  refine ⟨?_,?_,?_,?_⟩
  · intro test member
    have equal := List.mem_singleton.mp member; subst test
    refine ⟨⟨_,.source _⟩,?_⟩
    intro actual observed; cases observed
    simp only [Test.Holds,target_nonzero]
    exact ⟨subtype_refl _,subtype_refl _⟩
  · intro entry member
    have equal := List.mem_singleton.mp member; subst entry
    refine ⟨⟨_,.source _⟩,?_⟩
    intro actual observed; cases observed
    simp [VariableHolds,GeneralDeclarations.Declaration.outputNames,
      GeneralNominalPacketSupport.capture,GeneralNominalSaturationState.Packet.bindings,
      report_exact (context true) declaration 0 listDescriptor rfl 0 (1,1) rfl query,
      captured,bindings,GeneralNominalAllocation.capture,GeneralNominalAllocation.occurrences,
      GeneralNominalCaptureMerges.Fits,target_nonzero,
      subtype_refl]
  · intro first one last two _ _ _ a b ha hb
    have x := List.mem_singleton.mp one; have y := List.mem_singleton.mp two
    subst first; subst last; cases ha; cases hb
    exact ⟨subtype_refl _,subtype_refl _⟩
  · intro entry member cap recorded _ _ origin same a b ha hb
    have x := List.mem_singleton.mp member; subst entry
    have y := List.mem_singleton.mp recorded; subst cap
    have z := Option.some.inj same; subst origin
    cases ha
    have fit := (nominal_argument_bounds (state true) model (state_models true) 0 listDescriptor rfl 0 (1,1) rfl).2 b hb
    simpa [GeneralNominalExamples.model,target_nonzero,GeneralNominalCaptureMerges.Fits,Equivalent] using fit

theorem journal_models : GeneralNominalSaturationState.Models journal model := by
  refine ⟨state_models true,?_,?_⟩
  · intro p member; have equal := List.mem_singleton.mp member; subst p; exact branch
  · intro site member; cases member

theorem nonvacuous_strict_coverage :
    GeneralNominalSaturationState.Models journal model ∧
    closedRequest ∈ GeneralDictionaryRequestCatalog.catalog tracked ∧
    closedRequest ∉ GeneralDictionaryReachableRequestHistory.safeCatalog tracked :=
  ⟨journal_models,strict_coverage⟩
end Yulang.GeneralDictionaryMixedCatalogInhabited
