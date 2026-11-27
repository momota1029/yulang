import Yulang.GeneralDeclarativeI65I74LiteralCapturePullback466
namespace Yulang.C466LiteralCapturePullback
open Yulang.GeneralDeclarationPatterns (Pattern normalize covered)
open Yulang.GeneralDeclarativeI65.I72.WrittenPattern460.PhysicalOrigin (atSource Pose)
def shiftedExample : Pattern :=
  .record 10 (.var 1) (.record 10 (.var 99) (.record 20 (.var 7) (.app 3 [])))

theorem exact_shadow_skip_chooses_the_retained_binder :
    covered shiftedExample = true ∧
    atSource (normalize shiftedExample) [.tail,.payload] = some (.var 7) ∧
    pullPos shiftedExample [.tail,.payload] = some [.tail,.tail,.payload] ∧
    atSource shiftedExample [.tail,.payload] = some (.var 99) ∧
    atSource shiftedExample [.tail,.tail,.payload] = some (.var 7) := by
  exact ⟨rfl,rfl,by decide +kernel,rfl,rfl⟩

#print axioms exact_shadow_skip_chooses_the_retained_binder
#print axioms real_ready_capture_binder_lifts_back_before_normalization_without_changing_raw_row
#print axioms hide_pullback_preserves_the_actual_subtree
#print axioms pull_joinfree_normalized_binder_to_exact_written_source
#print axioms pull_joinfree_argument_binder_to_exact_written_source
end Yulang.C466LiteralCapturePullback
