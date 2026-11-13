import Yulang.GeneralDictionaryActualGroundExecutor173

/-! A branching ground-source regression: Show(pair(list(int),int)). It uses
Astra's proved ground progress, with NO GroundCaptureFactorization premise.
It proves actual saturation of the witness executor, not evaluation of its
noncomputable output or construction of a completed dictionary. -/
namespace Yulang.GeneralDictionaryActualGroundExample173
open GeneralNominalGroundExamples
open GeneralNominalActualBoundary
open GeneralNominalActualInspectionSteps
open GeneralNominalSupport
open GeneralNominalSaturationState
open GeneralDictionaryActualGroundExecutor173
open B4TargetV5
abbrev roles := GeneralDeclarationExamples.roles
abbrev start := GeneralNominalSupport.initial context root
noncomputable def final := ((executor roles).run registry start root).1

theorem source_initial : (groundBoundary roles).Initial registry root start :=
  ⟨context,labels,initial_source,point_source,ground,rfl⟩

/-- Genuine actual Step execution, halted final state, stable generated children,
and backward model preservation. No child-accessibility or dictionary residual. -/
theorem actual_run :
    B4Target.Steps (Step registry root) start final ∧
    (∀ next, ¬ Step registry root final next) ∧
    Stable registry final root ∧
    (∀ child, Generated final.current root child → Stable registry final child) ∧
    ∀ model, Models final.current model → Models start.current model := by
  have checkedBoundary : (groundBoundary roles).Checked registry := ⟨rfl,checked⟩
  have reachable := reachable_initial (groundBoundary roles) source_initial
  exact ⟨execution roles registry checkedBoundary start root reachable,
    halted roles registry checkedBoundary start root reachable,
    (final_stable roles registry checkedBoundary start root reachable).1,
    (final_stable roles registry checkedBoundary start root reachable).2,
    final_models roles registry checkedBoundary start root reachable⟩

end Yulang.GeneralDictionaryActualGroundExample173
