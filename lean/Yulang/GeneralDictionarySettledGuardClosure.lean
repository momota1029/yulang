import Yulang.GeneralDictionarySettledGuardedClassification
import Yulang.GeneralDictionarySettledPendingExclusion

/-! Exact I26 selected classification criterion on the old selected-child graph.
No guard is demanded of unrelated demands; this is not semantic Evidence. -/
namespace Yulang.GeneralDictionarySettledGuardClosure
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSupport
open CommonRoleOutermostResolver GeneralDictionarySettledProjection
open GeneralDictionarySettledGuardedClassification
private theorem selected_parts {v : B4Target.Vocabulary} (b : B4Target.SourceBoundary v)
    (r : v.Registry) (s : v.State) (d : v.Demand) (dictionary : Dictionary)
    (classified : B4TargetV3.Classify b r s d (.selected dictionary)) :
    ∃ key children dictionaries,
      B4TargetV3.Local b r s d (.selected key children) ∧
      All₂ (fun child dictionary => B4TargetV3.Classify b r s child (.selected dictionary))
        children dictionaries := by
  cases dictionary with
  | node key dictionaries =>
    cases classified with
    | selected safe unique all => exact ⟨key,_,dictionaries,.selected safe unique,all⟩


variable {roles : Roles.RoleDecls} {registry : Registry} {state : Tracked roles}

/-- An old selected-child edge out of a newly classified parent is also a new
edge. Functionality of the old Local relation aligns the exact child lists. -/
theorem old_child_is_new {root child : Occurrence roles} {dictionary : Dictionary}
    (classified : B4TargetV3.Classify (fresh roles).toSourceBoundary registry state root (.selected dictionary))
    (edge : Child (B4TargetV3.Local (old roles).toSourceBoundary registry state) child root) :
    Child (B4TargetV3.Local (fresh roles).toSourceBoundary registry state) child root := by
  obtain ⟨key,children,selected,member⟩ := edge
  obtain ⟨other,kids,payloads,newLocal,_⟩ := selected_parts _ _ _ _ _ classified
  have same := B4TargetV3.local_functional selected (selected_local_old newLocal)
  cases same
  exact ⟨_,_,newLocal,member⟩

theorem old_descendant_selected {root child : Occurrence roles} {dictionary : Dictionary}
    (classified : B4TargetV3.Classify (fresh roles).toSourceBoundary registry state root (.selected dictionary))
    (path : B4Target.Steps (fun parent child => Child
      (B4TargetV3.Local (old roles).toSourceBoundary registry state) child parent) root child) :
    ∃ payload, B4TargetV3.Classify (fresh roles).toSourceBoundary registry state child (.selected payload) := by
  induction path with
  | refl => exact ⟨dictionary,classified⟩
  | tail _ edge ih =>
    obtain ⟨payload,selected⟩ := ih
    exact GeneralDictionarySettledPendingExclusion.child_selected registry state _ payload selected _
      (old_child_is_new selected edge)

theorem guardClosure_of_classified {root : Occurrence roles} {dictionary : Dictionary}
    (classified : B4TargetV3.Classify (fresh roles).toSourceBoundary registry state root (.selected dictionary)) :
    GuardClosure registry state root := by
  intro child path
  obtain ⟨payload,selected⟩ := old_descendant_selected classified path
  obtain ⟨key,children,dictionaries,localRule,_⟩ := selected_parts _ _ _ _ _ selected
  exact (selected_local_iff.mp localRule).2

/-- Exact criterion: old selected classification plus I26 explanations precisely
on all old selected descendants, including the root. -/
theorem selected_iff {root : Occurrence roles} {dictionary : Dictionary} :
    B4TargetV3.Classify (fresh roles).toSourceBoundary registry state root (.selected dictionary) ↔
    B4TargetV3.Classify (old roles).toSourceBoundary registry state root (.selected dictionary) ∧
      GuardClosure registry state root := by
  constructor
  · intro selected
    exact ⟨selected_classification_old _ _ selected,guardClosure_of_classified selected⟩
  · rintro ⟨selected,guard⟩
    exact classified_of_guards _ _ guard selected
end Yulang.GeneralDictionarySettledGuardClosure
