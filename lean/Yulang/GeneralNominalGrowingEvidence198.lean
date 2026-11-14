import Yulang.GeneralNominalGrowingRefresh198
import Yulang.GeneralNominalIdentityLeaf

set_option backward.isDefEq.respectTransparency false
/-! A nonempty registry's actual source dictionary survives the inhabited
slot-growing WF refresh. This is semantic Evidence, not a Classify claim. -/
namespace Yulang.GeneralNominalGrowingEvidence198
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalGrowingRefresh198
open GeneralDeclarationExamples (roles constructors)
open GeneralNominalRecursiveInspection
open GeneralNominalCenteredHeadStepEffects (Models)
open GeneralNominalCenteredHeadWFBoundary (boundary)

theorem declaration_checked : DeclarationChecked constructors roles declaration := by
  constructor
  · simp [Declaration.Signature,roles,GeneralDeclarationExamples.bareRole]
  · simp [Declaration.Identified,Declaration.outputNames]
  · simp [Declaration.Produced]
  · simp [Declaration.OutputOnly,Declaration.outputNames]
  · simp [Declaration.Scoped]
  · simp [Declaration.ConstructorScoped,GeneralDeclarationPatterns.ArgsWellScoped,
      GeneralDeclarationPatterns.WellScoped]
  all_goals intro clause member; cases member

abbrev packet : GeneralNominalSaturationState.Packet roles :=
  ⟨registry,oldContext,GeneralNominalDemandMerging.pointSite root,declaration,declaration_checked,[(0,0)]⟩

theorem shape : GeneralNominalIdentityLeaf.Shape declaration :=
  ⟨rfl,rfl,by intro equation member; cases member⟩

theorem lookup : GeneralNominalRecursiveCandidates.arguments oldContext root = some [(0,0)] := by
  decide +kernel

theorem schema : GeneralNominalRecursiveCandidates.generated registry oldContext root declaration
    declaration_checked [(0,0)] = {} := by
  unfold GeneralNominalRecursiveCandidates.generated GeneralNominalMaterialization.requests
    GeneralCanonicalChildOrder.canonicalEmit
  simp only [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,List.mergeSort_nil]
  rfl

theorem current_instance (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models oldContext.state model) :
    GeneralDictionaryRecursiveEvidence.Instance registry oldContext model root 1980 [] := by
  have inputs := GeneralNominalIdentityLeaf.inputs_valid (packet := packet) shape (slot := 0) rfl model
  refine ⟨declaration,by simp,declaration_checked,rfl,rfl,[(0,0)],lookup,?_,?_,?_,?_,?_⟩
  · rw [GeneralNominalIdentityLeaf.report_exact shape]
    exact ⟨rfl,rfl,rfl⟩
  · constructor
    · intro output member; cases member
    · rw [schema]
  · exact (GeneralNominalIdentityLeaf.children_empty packet rfl).symm
  · refine ⟨rfl,?_⟩
    intro name primitive recorded
    by_cases two : name = 2
    · subst name
      have same : GeneralCandidateInspection.Primitive.scalar .int = primitive := Option.some.inj recorded
      subst primitive
      exact ⟨⟨[],2⟩,rfl,rfl⟩
    · simp [two] at recorded
  · rw [GeneralDictionaryRecursiveEvidence.branch_models_iff]
    refine ⟨valid,inputs.1.1,inputs.1.2.1,inputs.1.2.2,inputs.2.1,?_⟩
    rw [schema]
    exact GeneralNominalMaterialization.empty_models ..

theorem source_payload (model : GeneralNominalCommonBridge.Assignment) (valid : Models start model) :
    (boundary roles).Evidence registry start model root (.node 1980 []) :=
  ⟨.node root 1980 [],⟨rfl,rfl⟩,.node (current_instance model valid.1.1.1)
    (by intro child member; cases member)⟩

theorem final_payload (model : GeneralNominalCommonBridge.Assignment) (valid : Models finish model) :
    (boundary roles).Evidence registry finish model root (.node 1980 []) :=
  GeneralNominalRefiningJournal198.universal_evidence (.tail .refl actual_step) source_payload model valid

theorem inhabited_evidence : ∃ model, Models start model ∧ Models finish model ∧
    (boundary roles).Evidence registry start model root (.node 1980 []) ∧
    (boundary roles).Evidence registry finish model root (.node 1980 []) := by
  obtain ⟨model,initial,final⟩ := GeneralNominalGrowingRefresh198.inhabited
  exact ⟨model,initial,final,source_payload model initial,final_payload model final⟩
end Yulang.GeneralNominalGrowingEvidence198
