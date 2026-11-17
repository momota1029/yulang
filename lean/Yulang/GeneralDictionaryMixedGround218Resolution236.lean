import Yulang.GeneralDictionaryMixedGround218RootSelected236
import Yulang.GeneralNominalVersionedMixedResolver236
set_option backward.isDefEq.respectTransparency false
/-! Exact fixed-snapshot resolution of the actual fully stable 218 endpoint.
The old generated child is rejected, but the current parent selects the new
pending child. This is a diagnostic regression, not a successful dictionary. -/
namespace Yulang.GeneralDictionaryMixedGround218Resolution236
open GeneralDictionaryGroundCopy218Source
open GeneralDictionaryMixedGround218FinalState235
open GeneralDictionaryGroundCopy218Reinstall (newChild)
open GeneralDictionaryMixedGround218PointLeaf235 (oldChild)
open GeneralNominalVersionedMixedResolver236
open CommonRoleOutermostResolver

theorem checked : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Checked sourceRegistry :=
 ⟨rfl,source_checked⟩

theorem old_rejected : tree checked reachable oldChild = .rejected :=
 rejected checked reachable GeneralDictionaryMixedGround218FinalRejection235.rejected

theorem new_pending : tree checked reachable newChild.occurrence = .pending :=
 pending checked reachable GeneralDictionaryMixedGround218FinalPending235.pending

theorem root_tree : tree checked reachable root = .selected 0 [.pending] :=
 (tree_exact checked reachable root _).mpr
   (.selected GeneralDictionaryMixedGround218RootSelected236.selected
     (.cons (.pending GeneralDictionaryMixedGround218FinalPending235.pending) .nil))

theorem root_result : classification (tree checked reachable root) = .pending := by
 rw [root_tree]
 rfl

theorem no_root_success (dictionary) :
 ¬ CommonRoleOutermostResolver.Classify
   (GeneralNominalVersionedMixedSourceBoundary234.Local sourceRegistry finalState)
   root (.selected dictionary) := by
 intro classified
 have same := (result_exact checked reachable root (.selected dictionary)).mpr classified
 rw [root_result] at same
 cases same
end Yulang.GeneralDictionaryMixedGround218Resolution236
