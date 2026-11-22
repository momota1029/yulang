import Yulang.GeneralDeclarativeCurrentMerge345

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeMergeOrder345
open GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedAdministrative232 (merge)
open GeneralNominalSaturationState (Alias)
open GeneralDeclarativeCurrentOrder345 (Row rows)
open GeneralRebaseMergeRequests264 (Joined alias_merge)

private theorem scan_sublist (l : List α) (keep more : α → Bool) (pack : α → List β)
    (mono : ∀ a, keep a = true → more a = true) :
    ((l.filter keep).flatMap pack).Sublist ((l.filter more).flatMap pack) := by
  induction l with
  | nil => exact .slnil
  | cons h t ih =>
    cases one : keep h <;> cases two : more h
    · simpa [List.filter_cons,one,two] using ih
    · simpa [List.filter_cons,one,two] using ih.trans (List.sublist_append_right _ _)
    · have impossible := mono h one
      rw [two] at impossible
      cases impossible
    · simpa [List.filter_cons,one,two] using ih.append_left (pack h)

theorem exact_merge_scan (before : State rs) (first last : Site rs) (focus : Occurrence rs) :
    rows (merge before first last).core focus = by
      classical
      exact (before.core.erased.current.sites.zipIdx.filter fun e =>
        Joined before.core.erased.current first.occurrence.identity last.occurrence.identity
          focus.identity e.1.occurrence.identity).flatMap fun entry =>
        entry.1.occurrence.demand.outputs.zipIdx.map fun out => ⟨entry.2,out.2,out.1⟩ := by
  classical
  unfold rows
  change List.flatMap _ (List.filter _ before.core.erased.current.sites.zipIdx) = _
  congr 1
  congr 1
  funext site
  by_cases yes : Alias (merge before first last).core.erased.current focus.identity site.1.occurrence.identity
  · simp [yes,(alias_merge before first last _ _).mp yes]
  · have absent : ¬ Joined before.core.erased.current first.occurrence.identity last.occurrence.identity
        focus.identity site.1.occurrence.identity := fun h => yes ((alias_merge before first last _ _).mpr h)
    simp [yes,absent]

theorem stable_subsequence (before : State rs) (first last : Site rs) (focus : Occurrence rs) :
    (rows before.core focus).Sublist (rows (merge before first last).core focus) := by
  classical
  rw [exact_merge_scan]
  unfold rows
  apply scan_sublist
  intro a yes
  exact decide_eq_true (.inl (of_decide_eq_true yes))

end Yulang.GeneralDeclarativeMergeOrder345
