import Yulang.GeneralNominalSettledBoundary

/-! I26's actual settled-output guard excludes selected/completed dictionaries.
This is not a denial of the unchanged semantic Evidence predicate. No old
Stable premise is inferred from the new guarded Stable predicate. -/
namespace Yulang.GeneralDictionarySettledPendingExclusion
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSupport
open GeneralNominalSettledBoundary
open GeneralNominalSettledSteps (SupportPending)
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

/-- A completed selected diagnostic tree would yield the forbidden Classify. -/
theorem no_completed_selected (blocked : SupportPending registry state root)
    (tree : Tree) (dictionary : Dictionary)
    (resolved : Resolves (B4TargetV3.Local (boundary roles).toSourceBoundary registry state) root tree) :
    ¬ B4TargetV3.Completed tree (.selected dictionary) := by
  intro completed
  exact no_selected_classification registry state root blocked dictionary
    (B4TargetV3.tree_classifies _ _ _ _ _ _ resolved completed)

/-- Every selected child of a completed dictionary is itself classified selected. -/
theorem child_selected (dictionary : Dictionary)
    (classified : B4TargetV3.Classify (boundary roles).toSourceBoundary registry state root (.selected dictionary))
    (child : Occurrence roles)
    (edge : Child (B4TargetV3.Local (boundary roles).toSourceBoundary registry state) child root) :
    ∃ payload, B4TargetV3.Classify (boundary roles).toSourceBoundary registry state child (.selected payload) := by
  obtain ⟨key,children,selected,member⟩ := edge
  obtain ⟨other,kids,payloads,localRule,all⟩ := selected_parts _ _ _ _ _ classified
  have same := B4TargetV3.local_functional selected localRule
  cases same
  exact child_classified registry state all child member

/-- Arbitrarily deep selected where descendants inherit completed classification. -/
theorem descendant_selected (dictionary : Dictionary)
    (classified : B4TargetV3.Classify (boundary roles).toSourceBoundary registry state root (.selected dictionary))
    (child : Occurrence roles)
    (path : B4Target.Steps
      (fun parent child => Child (B4TargetV3.Local (boundary roles).toSourceBoundary registry state) child parent)
      root child) :
    ∃ payload, B4TargetV3.Classify (boundary roles).toSourceBoundary registry state child (.selected payload) := by
  induction path with
  | refl => exact ⟨dictionary,classified⟩
  | tail _ edge ih =>
    obtain ⟨payload,valid⟩ := ih
    exact child_selected registry state _ payload valid _ edge

/-- A settled-pending selected descendant blocks completion of the whole tree. -/
theorem descendant_pending_no_dictionary (child : Occurrence roles)
    (path : B4Target.Steps
      (fun parent child => Child (B4TargetV3.Local (boundary roles).toSourceBoundary registry state) child parent)
      root child)
    (blocked : SupportPending registry state child) (dictionary : Dictionary) :
    ¬ B4TargetV3.Classify (boundary roles).toSourceBoundary registry state root (.selected dictionary) := by
  intro classified
  obtain ⟨payload,valid⟩ := descendant_selected registry state root dictionary classified child path
  exact no_selected_classification registry state child blocked payload valid

theorem descendant_pending_no_completed (child : Occurrence roles)
    (path : B4Target.Steps
      (fun parent child => Child (B4TargetV3.Local (boundary roles).toSourceBoundary registry state) child parent)
      root child)
    (blocked : SupportPending registry state child) (tree : Tree) (dictionary : Dictionary)
    (resolved : Resolves (B4TargetV3.Local (boundary roles).toSourceBoundary registry state) root tree) :
    ¬ B4TargetV3.Completed tree (.selected dictionary) := by
  intro completed
  exact descendant_pending_no_dictionary registry state root child path blocked dictionary
    (B4TargetV3.tree_classifies _ _ _ _ _ _ resolved completed)

/-- Unsupported expansion is not reported as an ambiguous dictionary either. -/
theorem no_local_ambiguous (blocked : SupportPending registry state root) :
    ¬ Local registry state root .ambiguous := by
  intro ambiguous
  cases ambiguous with
  | ambiguous safe _ _ _ => exact safe.2.2.2 (Or.inr blocked)

end Yulang.GeneralDictionarySettledPendingExclusion
