import Yulang.GeneralDictionaryScalarLeaf
import Yulang.GeneralNominalCenteredSteps
import Yulang.GeneralDictionarySharedRecordedTree
/-! A real point-initial centered source with scalar Int evidence and no journal
tree. Its terminal packet is already committed, so an installation requiring
novelty cannot be used merely to record it. No stable/final executor claim. -/
namespace Yulang.GeneralDictionaryCenteredLeafRegression176
open GeneralNominalExamples GeneralNominalCenteredSteps GeneralNominalCenters
open GeneralDeclarationExamples (roles)
open GeneralNominalSaturationState (Packet)

abbrev start := initial (context true) displayChild
abbrev packet : Packet roles := ⟨registry,context true,
  GeneralNominalDemandMerging.pointSite displayChild,intDisplay,int_display_checked,[(1,1)]⟩
abbrev plan : Plan roles := ⟨packet,rootSite (state true).seed displayChild,rfl⟩

def shape : GeneralDictionaryScalarLeaf.ScalarLeafShape (context true) displayChild intDisplay where
  terminal := rfl
  outputs := rfl
  role := rfl
  slot := ⟨1,by decide +kernel⟩
  base := .int
  noNominal := rfl
  head := rfl
  inputs := rfl
  query := by
    simp [GeneralNominalInspection.queries,GeneralDeclarations.Declaration.normalHead,
      GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize]
    change GeneralNominalInspection.translate GeneralDeclarationExamples.constructors interpretation
      (.app 2 []) = .scalar .int
    simp [GeneralNominalInspection.translate,interpretation]
  located := rfl

theorem children_empty : packet.children = [] := by cbv

theorem already_committed : GeneralNominalFeedbackSteps.Committed start.erased.current packet := by
  constructor
  · intro model valid
    exact GeneralDictionaryScalarLeaf.branch_models (context true) registry displayChild intDisplay
      int_display_checked shape model valid.1
  · intro child member
    rw [children_empty] at member
    cases member

theorem not_novel : ¬ (¬ GeneralNominalFeedbackSteps.Committed start.erased.current plan.packet) :=
  fun novel => novel already_committed


theorem initial_source : GeneralNominalSourceFormation.InitialSource registry (context true) displayChild where
  roles_agree := rfl
  metadata := GeneralDictionarySupportRecursiveExample.initial_source.metadata
  linked := by
    constructor
    · intro index
      change 1 ∈ GeneralNominalState.sources (state true) ∧ 1 ∈ GeneralNominalState.sources (state true)
      decide +kernel
    · intro output member
      cases member
  intervals := fun _ _ _ => CommonNominalFullCarrier.subtype_refl _
  below_seed := GeneralDictionarySupportRecursiveExample.initial_source.below_seed
  unallocated := rfl

theorem initial_model : Models start model :=
  (point_initial_models (context true) displayChild (fun _ => rfl) model).mpr (state_models true)

theorem current_evidence (assignment : GeneralNominalCommonBridge.Assignment) (valid : Models start assignment) :
    GeneralDictionaryRecursiveEvidence.Evidence registry start.erased.current.context assignment displayChild (.node 3 []) :=
  GeneralDictionaryRecursiveEvidence.evidence_node _ _ _ _ _ _ _
    (GeneralDictionarySupportRecursiveExample.leaf_instance assignment valid.1.1) .nil

theorem no_recorded_tree (payload : GeneralDictionaryReadback.Payload) :
    ¬ GeneralDictionarySharedRecordedTree.RecordedTree start.erased.current displayChild payload := by
  have empty : ∀ occurrence payload,
      ¬ GeneralDictionarySharedRecordedTree.RecordedTree start.erased.current occurrence payload := by
    intro occurrence payload tree
    cases tree with
    | node packet member dictionaries children => cases member
  exact empty displayChild payload

theorem nonvacuous_evidence_without_tree :
    InitialSource registry displayChild start ∧ Models start model ∧
    GeneralDictionaryRecursiveEvidence.Evidence registry start.erased.current.context model displayChild (.node 3 []) ∧
    ¬ GeneralDictionarySharedRecordedTree.RecordedTree start.erased.current displayChild (.node 3 []) :=
  ⟨GeneralNominalCenteredSteps.initial_source initial_source,initial_model,
    current_evidence model initial_model,no_recorded_tree _⟩

end Yulang.GeneralDictionaryCenteredLeafRegression176
