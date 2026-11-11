import Yulang.GeneralDictionaryVariableHeads
import Yulang.GeneralDictionaryTerminalFixture

/-! # Exact variable heads compile; nominal heads and nonexact captures defer -/
namespace Yulang.GeneralDictionaryHeadExamples
open GeneralDeclarations GeneralDeclarationPatterns GeneralDeclarationDemands
open GeneralDictionaryTerminalFixture
open GeneralDictionaryVariableHeads
open GeneralDictionaryOutputBinderExamples (binderWrap binderWrap_checked)

abbrev childHeadless : HeadlessInputs state childDemand where
  lower := childInputs.lower
  upper := childInputs.upper
  target := childInputs.target
  arguments := childInputs.arguments
  targets := childInputs.targets

abbrev rootHeadless : HeadlessInputs state rootDemand where
  lower := rootInputs.lower
  upper := rootInputs.upper
  target := rootInputs.target
  arguments := rootInputs.arguments
  targets := rootInputs.targets

theorem leaf_positional_compiles : compileAt state leaf capture 0 = some (.var 0) := rfl

theorem leaf_head_denotes : HeadDenotes leaf capture childDemand childInputs.head := by
  refine ⟨rfl, rfl, ?_⟩
  intro index
  have same : index = ⟨0, by decide⟩ := by
    apply Fin.ext
    have bound := index.isLt
    change index.val < 1 at bound
    change index.val = 0
    omega
  subst index
  exact (compileAt_exact state leaf capture 0 _).mp leaf_positional_compiles

theorem leaf_head_builds : build leaf leaf_checked rfl capture childHeadless = some childInputs :=
  (build_exact leaf leaf_checked rfl capture childHeadless childInputs).mpr
    ⟨rfl, rfl, rfl, leaf_head_denotes⟩

/-- This is the existing transaction HeadInstances interface, now concrete. -/
theorem leaf_concrete_head : heads registry.roles state child leaf capture childInputs.head :=
  leaf_head_denotes

theorem nominal_root_defers : build binderWrap binderWrap_checked rfl capture rootHeadless = none := by
  unfold build
  apply dite_eq_right
  intro complete
  have impossible := complete ⟨0, by decide⟩
  contradiction

abbrev unequalCapture : Capture := ⟨fun _ => (0, 1), fun _ => 2⟩

theorem unequal_leaf_defers : build leaf leaf_checked rfl unequalCapture childHeadless = none := by
  unfold build
  apply dite_eq_right
  intro complete
  have impossible := complete ⟨0, by decide⟩
  contradiction

abbrev absentCapture : Capture := ⟨fun _ => (99, 99), fun _ => 2⟩

theorem absent_source_defers : build leaf leaf_checked rfl absentCapture childHeadless = none := by
  unfold build
  apply dite_eq_right
  intro complete
  have impossible := complete ⟨0, by decide⟩
  contradiction

end Yulang.GeneralDictionaryHeadExamples
