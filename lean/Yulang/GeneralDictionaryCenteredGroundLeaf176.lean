import Yulang.GeneralDictionaryCenteredLeafRegression176
import Yulang.GeneralNominalCenteredGroundBoundary
import Yulang.GeneralNominalGroundExamples

/-! The scalar leaf regression belongs to exact G, by its point input and
closed Int source label. No stability or final-executor claim is made. -/
namespace Yulang.GeneralDictionaryCenteredGroundLeaf176
open GeneralNominalExamples GeneralDictionaryCenteredLeafRegression176
open GeneralDeclarationExamples (roles)
open GeneralNominalCenteredGroundBoundary (groundBoundary)

theorem ground : GeneralNominalGroundAccessibility.GroundRoots (context true) displayChild [.app 2 []] := by
  refine ⟨rfl,?_⟩
  intro index
  have zero : index.val = 0 := by have bound := index.isLt; change index.val < 1 at bound; omega
  simp only [zero]
  refine ⟨GeneralNominalGroundExamples.intTerm,⟨?_,rfl,⟨trivial,fun i => Fin.elim0 i⟩⟩,?_⟩
  · simp [GeneralDeclarationPatterns.normalize,GeneralDeclarationPatterns.normalizeArgs,
      GeneralNominalInspection.translate,interpretation,GeneralNominalCompoundReadback.quote]

  · intro assignment valid
    exact GeneralNominalState.normalized_models (state true) assignment valid (1 : Fin 2) (.base .int) rfl

theorem initial : (groundBoundary roles).Initial registry displayChild start :=
  ⟨context true,[.app 2 []],initial_source,(fun _ => rfl),ground,rfl⟩

theorem reachable : B4TargetV5.Reachable (groundBoundary roles) registry displayChild start :=
  ⟨start,initial,.refl⟩

theorem reachable_evidence_without_tree :
    B4TargetV5.Reachable (groundBoundary roles) registry displayChild start ∧
    GeneralNominalCenteredSteps.Models start model ∧
    GeneralDictionaryRecursiveEvidence.Evidence registry start.erased.current.context model displayChild (.node 3 []) ∧
    ¬ GeneralDictionarySharedRecordedTree.RecordedTree start.erased.current displayChild (.node 3 []) :=
  ⟨reachable,initial_model,current_evidence model initial_model,no_recorded_tree _⟩
end Yulang.GeneralDictionaryCenteredGroundLeaf176
