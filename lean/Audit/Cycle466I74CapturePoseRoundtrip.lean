import Yulang.GeneralDeclarativeI65I74CapturePoseRoundtrip466
namespace Yulang.C466LiteralCapturePullback
open Yulang.GeneralDeclarationPatterns (Pattern normalize covered)
open Yulang.GeneralDeclarativeI65.I72.WrittenPattern460.PhysicalOrigin (atSource Pose)
def shiftedRoundtripExample466 : Pattern :=
  .record 10 (.var 1) (.record 10 (.var 99) (.record 20 (.var 7) (.app 3 [])))

theorem roundtrip_retains_only_kept_original_binders :
    covered shiftedRoundtripExample466 = true ∧
    atSource (normalize shiftedRoundtripExample466) [.tail,.payload] = some (.var 7) ∧
    pullPos shiftedRoundtripExample466 [.tail,.payload] = some [.tail,.tail,.payload] ∧
    atSource shiftedRoundtripExample466 [.tail,.payload] = some (.var 99) ∧
    atSource shiftedRoundtripExample466 [.tail,.tail,.payload] = some (.var 7) := by
  exact ⟨rfl,rfl,by decide +kernel,rfl,rfl⟩


theorem a_hidden_binder_does_not_get_a_surviving_normalized_address :
    pushPos shiftedRoundtripExample466 [.tail,.payload] = none ∧
      pushPos shiftedRoundtripExample466 [.tail,.tail,.payload] = some [.tail,.payload] := by
  exact ⟨by decide +kernel,by decide +kernel⟩


#print axioms hide_roundtrip_keeps_the_same_pre_normalized_occurrence
#print axioms source_pose_rebase_is_a_left_inverse_to_the_same_pose
#print axioms two_distinct_retained_binder_poses_do_not_collapse_to_the_same_original
#print axioms a_hidden_binder_does_not_get_a_surviving_normalized_address
end Yulang.C466LiteralCapturePullback
