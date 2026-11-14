import Yulang.GeneralDictionaryCenteredScalar177
import Yulang.GeneralDictionaryCenteredRegression176

/-! The new scalar consumer succeeds at the integrated reachable premerge
state where installation is unavailable. This state is not stable: the example
separates producers, and is not a counterexample to the stable target. -/
namespace Yulang.GeneralDictionaryCenteredScalarRegression177
open GeneralDictionaryEarlyMergeScalarExample
open GeneralNominalCenteredSelectionCounterexample
open GeneralNominalCenteredSteps GeneralDeclarations
open GeneralNominalExamples (context state displayRoot model state_models intDisplay int_display_checked interpretation)

noncomputable def shape (n : Nat) :
    GeneralDictionaryScalarLeaf.ScalarLeafShape cbefore.erased.current.context (child n) intDisplay where
  terminal := rfl
  outputs := rfl
  role := rfl
  slot := ⟨1,by decide +kernel⟩
  base := .int
  noNominal := rfl
  head := rfl
  inputs := rfl
  query := by
    simp [GeneralNominalInspection.queries,Declaration.normalHead,GeneralDeclarationPatterns.normalizeArgs,
      GeneralDeclarationPatterns.normalize]
    change GeneralNominalInspection.translate GeneralDeclarationExamples.constructors interpretation (.app 2 []) = .scalar .int
    simp [GeneralNominalInspection.translate,interpretation]
  located := rfl

theorem inhabited : Models cbefore model :=
  (GeneralNominalCenteredSteps.install_models (plan := cplan) (state := cstart) (support := []) rfl model).mpr
    ⟨(point_initial_models _ _ (fun _ => rfl) model).mpr (state_models true),
      branch model (state_models true),cequations model (state_models true)⟩

theorem direct_evidence (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : Models cbefore assignment) :
    GeneralDictionaryRecursiveEvidence.Evidence registry cbefore.erased.current.context assignment
      (child 10) (.node 3 []) :=
  (GeneralDictionaryCenteredScalar177.selected_scalar (declaration := intDisplay)
    (by simp) int_display_checked (shape 10) (child_selected 10) assignment valid).2.2.2

theorem evidence_without_installability :
    B4TargetV5.Reachable (GeneralNominalCenteredGroundBoundary.groundBoundary GeneralDeclarationExamples.roles)
      registry displayRoot cbefore ∧
    Models cbefore model ∧
    GeneralDictionaryRecursiveEvidence.Evidence registry cbefore.erased.current.context model
      (child 10) (.node 3 []) ∧
    ¬ GeneralNominalCenteredWhere.Available registry cbefore (child 10) ∧
    ¬ Stable registry cbefore displayRoot :=
  ⟨ground_reachable,inhabited,direct_evidence model inhabited,not_available,
    GeneralDictionaryCenteredRegression176.premerge_not_stable⟩
end Yulang.GeneralDictionaryCenteredScalarRegression177
