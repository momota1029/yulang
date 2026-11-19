import Yulang.FiniteRankBehavior269

namespace Yulang.FiniteBehaviorCatalogue269
open FiniteRankBehavior269 (Code catalogue)
open GeneralRebaseFiniteSlices268 (slices exact_slices)

theorem slice_mono (subset : first.Sublist last) : (slices first).Sublist (slices last) := by
 induction subset with
 | slnil => exact List.Sublist.refl _
 | cons head h ih => exact ih.trans (List.sublist_append_left ..)
 | cons_cons head h ih => exact ih.append (ih.map (head :: ·))

theorem flat_zip (entries : List α) (first last : α → List β)
 (lift : ∀ x, (first x).Sublist (last x)) : (entries.flatMap first).Sublist (entries.flatMap last) := by
 induction entries with
 | nil => exact .slnil
 | cons _ _ ih => exact (lift _).append ih

theorem elementary_supported (labels : List Label) (pool : List (Code Label)) :
 (labels.map (fun x => Code.node x [])).Sublist
 (labels.flatMap fun x => (slices pool).map (Code.node x)) := by
 induction labels with
 | nil => exact .slnil
 | cons x labels ih =>
   change ([Code.node x []] ++ labels.map (fun x => Code.node x [])).Sublist
     (((slices pool).map (Code.node x)) ++ labels.flatMap fun y => (slices pool).map (Code.node y))
   apply List.Sublist.append _ ih
   apply List.singleton_sublist.mpr
   exact List.mem_map.mpr ⟨[],(exact_slices ..).mpr (List.nil_sublist _),rfl⟩

theorem ascending (labels : List Label) (depth : Nat) :
 (catalogue labels depth).Sublist (catalogue labels (depth+1)) := by
 induction depth with
 | zero => exact elementary_supported labels _
 | succ d ih => exact flat_zip labels _ _ (fun x => (slice_mono ih).map (Code.node x))

theorem mono (labels : List Label) (h : first ≤ last) :
 (catalogue labels first).Sublist (catalogue labels last) := by
 induction h with
 | refl => exact List.Sublist.refl _
 | step _ ih => exact ih.trans (ascending labels _)

end Yulang.FiniteBehaviorCatalogue269
