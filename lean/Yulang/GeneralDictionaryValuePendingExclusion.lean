import Yulang.GeneralNominalValueBoundary

/-! Exclusion for the existing Value support guard only. This does not identify
that guard with I-26's forthcoming unsettled-output delay rule. Selected local
frontiers and completed classifications are excluded, not semantic Evidence. -/
namespace Yulang.GeneralDictionaryValuePendingExclusion
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSupport
open GeneralNominalValueBoundary
open CommonRoleOutermostResolver
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

variable {roles : Roles.RoleDecls}
variable (registry : Registry) (state : Tracked roles) (root : Occurrence roles)

theorem no_local_selected (blocked : SupportPending registry state root)
    (key : Nat) (children : List (Occurrence roles)) :
    ¬ Local registry state root (.selected key children) := by
  intro selected
  cases selected with
  | selected safe _ => exact safe.2.2.2 (Or.inr blocked)

theorem no_boundary_selected (blocked : SupportPending registry state root)
    (key : Nat) (children : List (Occurrence roles)) :
    ¬ B4TargetV3.Local (boundary roles).toSourceBoundary registry state root
      (.selected key children) := by
  intro selected
  exact no_local_selected registry state root blocked key children
    ((local_correspondence registry state root _).mp selected)

theorem no_selected_classification (blocked : SupportPending registry state root)
    (dictionary : Dictionary) :
    ¬ B4TargetV3.Classify (boundary roles).toSourceBoundary registry state root
      (.selected dictionary) := by
  intro selected
  obtain ⟨key,children,_,localRule,_⟩ := selected_parts _ _ _ _ _ selected
  exact no_boundary_selected registry state root blocked key children localRule

private theorem child_classified
    {children : List (Occurrence roles)} {dictionaries : List Dictionary}
    (classified : All₂ (fun child dictionary =>
      B4TargetV3.Classify (boundary roles).toSourceBoundary registry state child (.selected dictionary))
      children dictionaries)
    (child : Occurrence roles) (member : child ∈ children) :
    ∃ dictionary, B4TargetV3.Classify (boundary roles).toSourceBoundary registry state child
      (.selected dictionary) := by
  induction classified with
  | nil => cases member
  | cons head tail ih =>
    rcases List.mem_cons.mp member with rfl | rest
    · exact ⟨_,head⟩
    · exact ih rest

/-- A known selected local parent's child list cannot complete a dictionary if
one child is support-pending. No assumption about semantic child Evidence. -/
theorem child_pending_no_parent_dictionary
    (key : Nat) (children : List (Occurrence roles))
    (selected : B4TargetV3.Local (boundary roles).toSourceBoundary registry state root
      (.selected key children))
    (child : Occurrence roles) (member : child ∈ children)
    (blocked : SupportPending registry state child) (dictionary : Dictionary) :
    ¬ B4TargetV3.Classify (boundary roles).toSourceBoundary registry state root
      (.selected dictionary) := by
  intro classified
  obtain ⟨other,kids,payloads,localRule,all⟩ := selected_parts _ _ _ _ _ classified
  have same := B4TargetV3.local_functional selected localRule
  cases same
  obtain ⟨payload,has⟩ := child_classified registry state all child member
  exact no_selected_classification registry state child blocked payload has
end Yulang.GeneralDictionaryValuePendingExclusion
