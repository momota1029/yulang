import Yulang.GeneralNominalTraceRefreshExample197

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalTraceEvidence197
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalTraceRefreshExample197
open GeneralNominalRefreshFork (state context descriptor)
open GeneralNominalExecutableView196 (next start finish certificate)
open GeneralNominalRecursiveCandidates (arguments generated RequestReady BranchModels)
open GeneralNominalSpineFacts
open GeneralNominalRecursiveInspection
open GeneralDeclarationExamples (roles)

abbrev names : Fin 1 → Nat := fun _ => 0
abbrev bounds : Fin 1 → GeneralNominalInspection.Bounds (state none) := fun _ => (3,3)
def spine : Spine (state none) names bounds 1 :=
  .wrap 1 2 (descriptor (2,2)) rfl rfl (.leaf 2 (descriptor (3,3)) rfl rfl)

theorem query_spine : GeneralNominalInspection.queries (state none)
    (context none).interpretation declaration = [spine.query] := computed_query

theorem schema : generated registry (context none) focus declaration declaration_checked [(1,1)] = {} := by
  unfold generated GeneralNominalMaterialization.requests GeneralCanonicalChildOrder.canonicalEmit
  simp only [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,List.mergeSort_nil]
  rfl

theorem current_instance (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models (state none) model) :
    GeneralDictionaryRecursiveEvidence.Instance registry (context none) model focus 970 [] := by
  have computed := report_exact (context none) declaration names bounds spine query_spine
  have privateFacts := private_models (context none) registry focus declaration names
    (fun a b _ => Subsingleton.elim a b) (by rfl) bounds spine query_spine model valid
  refine ⟨declaration,by simp,declaration_checked,rfl,rfl,[(1,1)],lookup,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [computed]
    exact spine_finished (state none) names bounds spine none
  · refine ⟨?_,?_⟩
    · intro output member; cases member
    · rw [schema]
  · unfold GeneralNominalAllocation.children GeneralDictionaryEmissionPlans.children GeneralCanonicalChildOrder.canonicalEmit
    simp only [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,List.mergeSort_nil]
    rfl
  · exact GeneralNominalRefreshFork.metadata none
  · exact privateFacts.1
  · exact privateFacts.2
  · rw [schema]
    exact GeneralNominalMaterialization.empty_models ..

theorem source_tree (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models (state none) model) :
    GeneralSourceDictionaries.Evidence
      (GeneralDictionaryRecursiveEvidence.Instance registry (context none) model) tree :=
  .node (current_instance model valid) (by intro child member; cases member)

theorem source_readback : Readback focus payload tree := ⟨rfl,rfl⟩

/-- Complete source evidence in every original model, with a fixed concrete
nested-nominal source witness; no Evidence premise is assumed. -/
theorem source_payload (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalCenteredHeadStepEffects.Models start model) :
    (GeneralNominalCenteredHeadWFBoundary.boundary roles).Evidence registry start model focus payload :=
  ⟨tree,source_readback,source_tree model valid.1.1.1⟩

/-- The actual descriptor-inserting WF step preserves the complete nested
nominal dictionary in every final model. The changed slot0 is outside its trace. -/
theorem final_payload (wide : Bool) (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalCenteredHeadStepEffects.Models (finish wide) model) :
    (GeneralNominalCenteredHeadWFBoundary.boundary roles).Evidence registry (finish wide)
      model focus payload := by
  exact GeneralNominalTraceDictionary197.universal_refresh (state := start) (next := next wide) (certificate wide) (traced wide) source_readback
    (fun m hm => source_tree m hm.1.1.1) model valid

theorem inhabited_complete (wide : Bool) :
    GeneralNominalCenteredHeadStepEffects.Models start GeneralNominalRefreshFork.model ∧
    GeneralNominalCenteredHeadStepEffects.Models (finish wide) GeneralNominalRefreshFork.model ∧
    (GeneralNominalCenteredHeadWFBoundary.boundary roles).Evidence registry start
      GeneralNominalRefreshFork.model focus payload ∧
    (GeneralNominalCenteredHeadWFBoundary.boundary roles).Evidence registry (finish wide)
      GeneralNominalRefreshFork.model focus payload := by
  have m := GeneralNominalExecutableView196.inhabited wide
  exact ⟨m.1,m.2,source_payload _ m.1,final_payload wide _ m.2⟩
end Yulang.GeneralNominalTraceEvidence197
