import Yulang.GeneralDeclarativeI65I74FlatDispatch481

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.Flat481
open RetainedFull445 (FullProblem)
open Checker408 (Result)

def flattenRetained : RetainedSplit446.Witness446 → LegacyWire := LegacyWire.retained

theorem retained_scope481 (w : RetainedSplit446.Witness446) :
    (flattenRetained w).scope.rank ≤ LegacyScope.retained.rank := by
  exact Nat.le_refl _

private theorem retained_leaf481 (p : FullProblem) (r : Result) (w : RetainedSplit446.Witness446) :
    checkLegacy p r (flattenRetained w) = RetainedSplit446.check_full446 p r w := by
  rfl

theorem retained_same_Bool481 (p : FullProblem) (r : Result) (w : RetainedSplit446.Witness446) :
    check_full_flat p (.legacy .retained r) (.legacy (flattenRetained w)) =
      RetainedSplit446.check_full446 p r w := by
  change (decide ((flattenRetained w).scope.rank ≤ LegacyScope.retained.rank) &&
      checkLegacy p r (flattenRetained w)) = _
  rw [decide_eq_true (retained_scope481 w),Bool.true_and]
  exact retained_leaf481 p r w

def flattenSelected : RetainedSplit446.SelectedReplay447.Witness447 → LegacyWire
  | .previous w => flattenRetained w
  | .localSplitOutput w => .selected w

theorem selected_scope481 (w : RetainedSplit446.SelectedReplay447.Witness447) :
    (flattenSelected w).scope.rank ≤ LegacyScope.selected.rank := by
  cases w with
  | previous old => exact Nat.le_trans (retained_scope481 old) (by decide)
  | localSplitOutput data => exact Nat.le_refl _

private theorem selected_leaf481 (p : FullProblem) (r : Result) (w : RetainedSplit446.SelectedReplay447.Witness447) :
    checkLegacy p r (flattenSelected w) = RetainedSplit446.SelectedReplay447.check_full447 p r w := by
  cases w with
  | previous old => exact retained_leaf481 p r old
  | localSplitOutput data => rfl

theorem selected_same_Bool481 (p : FullProblem) (r : Result) (w : RetainedSplit446.SelectedReplay447.Witness447) :
    check_full_flat p (.legacy .selected r) (.legacy (flattenSelected w)) =
      RetainedSplit446.SelectedReplay447.check_full447 p r w := by
  change (decide ((flattenSelected w).scope.rank ≤ LegacyScope.selected.rank) &&
      checkLegacy p r (flattenSelected w)) = _
  rw [decide_eq_true (selected_scope481 w),Bool.true_and]
  exact selected_leaf481 p r w

def flattenOpaque : Opaque448.Witness448 → LegacyWire
  | .previous w => flattenSelected w
  | .opaqueName w => .opaque w

theorem opaque_scope481 (w : Opaque448.Witness448) :
    (flattenOpaque w).scope.rank ≤ LegacyScope.opaque.rank := by
  cases w with
  | previous old => exact Nat.le_trans (selected_scope481 old) (by decide)
  | opaqueName data => exact Nat.le_refl _

private theorem opaque_leaf481 (p : FullProblem) (r : Result) (w : Opaque448.Witness448) :
    checkLegacy p r (flattenOpaque w) = Opaque448.check_full448 p r w := by
  cases w with
  | previous old => exact selected_leaf481 p r old
  | opaqueName data => rfl

theorem opaque_same_Bool481 (p : FullProblem) (r : Result) (w : Opaque448.Witness448) :
    check_full_flat p (.legacy .opaque r) (.legacy (flattenOpaque w)) =
      Opaque448.check_full448 p r w := by
  change (decide ((flattenOpaque w).scope.rank ≤ LegacyScope.opaque.rank) &&
      checkLegacy p r (flattenOpaque w)) = _
  rw [decide_eq_true (opaque_scope481 w),Bool.true_and]
  exact opaque_leaf481 p r w

def flattenWhole : Opaque448.Whole.Witness → LegacyWire
  | .previous w => flattenOpaque w
  | .wholeBare w => .whole w

theorem whole_scope481 (w : Opaque448.Whole.Witness) :
    (flattenWhole w).scope.rank ≤ LegacyScope.whole.rank := by
  cases w with
  | previous old => exact Nat.le_trans (opaque_scope481 old) (by decide)
  | wholeBare data => exact Nat.le_refl _

private theorem whole_leaf481 (p : FullProblem) (r : Result) (w : Opaque448.Whole.Witness) :
    checkLegacy p r (flattenWhole w) = Opaque448.Whole.check_full448 p r w := by
  cases w with
  | previous old => exact opaque_leaf481 p r old
  | wholeBare data => rfl

theorem whole_same_Bool481 (p : FullProblem) (r : Result) (w : Opaque448.Whole.Witness) :
    check_full_flat p (.legacy .whole r) (.legacy (flattenWhole w)) =
      Opaque448.Whole.check_full448 p r w := by
  change (decide ((flattenWhole w).scope.rank ≤ LegacyScope.whole.rank) &&
      checkLegacy p r (flattenWhole w)) = _
  rw [decide_eq_true (whole_scope481 w),Bool.true_and]
  exact whole_leaf481 p r w

def flattenListSite : ListSites449.Witness → LegacyWire
  | .previous w => flattenWhole w
  | .inspectedList w => .listSite w

theorem listSite_scope481 (w : ListSites449.Witness) :
    (flattenListSite w).scope.rank ≤ LegacyScope.listSite.rank := by
  cases w with
  | previous old => exact Nat.le_trans (whole_scope481 old) (by decide)
  | inspectedList data => exact Nat.le_refl _

private theorem listSite_leaf481 (p : FullProblem) (r : Result) (w : ListSites449.Witness) :
    checkLegacy p r (flattenListSite w) = ListSites449.check_full449 p r w := by
  cases w with
  | previous old => exact whole_leaf481 p r old
  | inspectedList data => rfl

theorem listSite_same_Bool481 (p : FullProblem) (r : Result) (w : ListSites449.Witness) :
    check_full_flat p (.legacy .listSite r) (.legacy (flattenListSite w)) =
      ListSites449.check_full449 p r w := by
  change (decide ((flattenListSite w).scope.rank ≤ LegacyScope.listSite.rank) &&
      checkLegacy p r (flattenListSite w)) = _
  rw [decide_eq_true (listSite_scope481 w),Bool.true_and]
  exact listSite_leaf481 p r w

def flattenListFrame : ListSites449.Frame.Witness → LegacyWire
  | .previous w => flattenListSite w
  | .inspectedFrame w => .listFrame w

theorem listFrame_scope481 (w : ListSites449.Frame.Witness) :
    (flattenListFrame w).scope.rank ≤ LegacyScope.listFrame.rank := by
  cases w with
  | previous old => exact Nat.le_trans (listSite_scope481 old) (by decide)
  | inspectedFrame data => exact Nat.le_refl _

private theorem listFrame_leaf481 (p : FullProblem) (r : Result) (w : ListSites449.Frame.Witness) :
    checkLegacy p r (flattenListFrame w) = ListSites449.Frame.check_full449 p r w := by
  cases w with
  | previous old => exact listSite_leaf481 p r old
  | inspectedFrame data => rfl

theorem listFrame_same_Bool481 (p : FullProblem) (r : Result) (w : ListSites449.Frame.Witness) :
    check_full_flat p (.legacy .listFrame r) (.legacy (flattenListFrame w)) =
      ListSites449.Frame.check_full449 p r w := by
  change (decide ((flattenListFrame w).scope.rank ≤ LegacyScope.listFrame.rank) &&
      checkLegacy p r (flattenListFrame w)) = _
  rw [decide_eq_true (listFrame_scope481 w),Bool.true_and]
  exact listFrame_leaf481 p r w

def flattenGuardedWhere : WhereSites450.Witness → LegacyWire
  | .previous w => flattenListFrame w
  | .whereRoot w => .guardedWhere w

theorem guardedWhere_scope481 (w : WhereSites450.Witness) :
    (flattenGuardedWhere w).scope.rank ≤ LegacyScope.guardedWhere.rank := by
  cases w with
  | previous old => exact Nat.le_trans (listFrame_scope481 old) (by decide)
  | whereRoot data => exact Nat.le_refl _

private theorem guardedWhere_leaf481 (p : FullProblem) (r : Result) (w : WhereSites450.Witness) :
    checkLegacy p r (flattenGuardedWhere w) = WhereSites450.NoSiblingMerge.check_full450 p r w := by
  cases w with
  | previous old => exact listFrame_leaf481 p r old
  | whereRoot data => rfl

theorem guardedWhere_same_Bool481 (p : FullProblem) (r : Result) (w : WhereSites450.Witness) :
    check_full_flat p (.legacy .guardedWhere r) (.legacy (flattenGuardedWhere w)) =
      WhereSites450.NoSiblingMerge.check_full450 p r w := by
  change (decide ((flattenGuardedWhere w).scope.rank ≤ LegacyScope.guardedWhere.rank) &&
      checkLegacy p r (flattenGuardedWhere w)) = _
  rw [decide_eq_true (guardedWhere_scope481 w),Bool.true_and]
  exact guardedWhere_leaf481 p r w

theorem impossible_legacy_scope_returns_false481 (p : FullProblem) (scope : LegacyScope)
    (r : Result) (w : LegacyWire) (late : ¬ w.scope.rank ≤ scope.rank) :
    check_full_flat p (.legacy scope r) (.legacy w) = false := by
  simp [check_full_flat,late]

end Yulang.GeneralDeclarativeI65.I72.Flat481
