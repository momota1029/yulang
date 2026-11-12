import Yulang.GeneralDictionaryLocalReadback

/-! Exact syntactic success criterion, separate from semantic Evidence and from
termination of the operational executor. -/
namespace Yulang.GeneralDictionaryLocalReadbackExact
open CommonRoleOutermostResolver GeneralDictionaryLocalReadback
variable {v : B4Target.Vocabulary} (b : B4Target.SourceBoundary v)
    (registry : v.Registry) (state : v.State)

private theorem selected_inv (root : v.Demand) (key : Nat) (dictionaries : List Dictionary)
    (classified : B4TargetV3.Classify b registry state root (.selected (.node key dictionaries))) :
    ∃ children, B4Target.SafeKnown b registry state root ∧
      B4Target.Unique b registry state root key children ∧
      All₂ (fun child dictionary => B4TargetV3.Classify b registry state child (.selected dictionary)) children dictionaries := by
  cases classified with
  | selected safe unique all => exact ⟨_,safe,unique,all⟩

private theorem local_children (root : v.Demand) (key : Nat) (children : List v.Demand)
    (unique : B4Target.Unique b registry state root key children)
    (child : v.Demand) (edge : Child (B4TargetV3.Local b registry state) child root) : child ∈ children := by
  obtain ⟨other,others,selected,member⟩ := edge
  cases selected with
  | selected safe another =>
    obtain ⟨_,same⟩ := unique.2 other others another.1
    exact same ▸ member

mutual
 theorem classified_accessible (root : v.Demand) (dictionary : Dictionary)
    (classified : B4TargetV3.Classify b registry state root (.selected dictionary)) :
    Acc (Child (B4TargetV3.Local b registry state)) root := by
  cases dictionary with
  | node key dictionaries =>
    obtain ⟨children,safe,unique,all⟩ := selected_inv b registry state root key dictionaries classified
    exact .intro root (fun child edge => children_accessible children dictionaries all child
      (local_children b registry state root key children unique child edge))
 termination_by sizeOf dictionary

 theorem children_accessible (children : List v.Demand) (dictionaries : List Dictionary)
    (classified : All₂ (fun child dictionary => B4TargetV3.Classify b registry state child (.selected dictionary))
      children dictionaries) :
    ∀ child ∈ children, Acc (Child (B4TargetV3.Local b registry state)) child := by
  cases classified with
  | nil => intro child member; cases member
  | cons first rest =>
    intro child member
    rcases List.mem_cons.mp member with rfl | member
    · exact classified_accessible _ _ first
    · exact children_accessible _ _ rest child member
 termination_by sizeOf dictionaries
end

private theorem child_witness (children : List v.Demand) (dictionaries : List Dictionary)
    (classified : All₂ (fun child dictionary => B4TargetV3.Classify b registry state child (.selected dictionary))
      children dictionaries) :
    ∀ child ∈ children, ∃ dictionary, B4TargetV3.Classify b registry state child (.selected dictionary) := by
  induction classified with
  | nil => intro child member; cases member
  | cons first rest ih =>
    intro child member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨_,first⟩
    · exact ih child member

/-- Every independent selected-child path of a completed dictionary remains
selected. Uniqueness prevents a hidden alternative local child branch. -/
theorem closure_selected (root : v.Demand) (dictionary : Dictionary)
    (classified : B4TargetV3.Classify b registry state root (.selected dictionary)) :
    ∀ focus, Reach (B4TargetV3.Local b registry state) root focus →
      ∃ key children, B4TargetV3.Local b registry state focus (.selected key children) := by
  have witness : ∀ focus, Reach (B4TargetV3.Local b registry state) root focus →
      ∃ dictionary, B4TargetV3.Classify b registry state focus (.selected dictionary) := by
    intro focus reached
    induction reached with
    | root => exact ⟨dictionary,classified⟩
    | @child parent child reached edge ih =>
      obtain ⟨payload,parentClassified⟩ := ih
      cases payload with
      | node key dictionaries =>
        obtain ⟨children,safe,unique,all⟩ := selected_inv b registry state parent key dictionaries parentClassified
        exact child_witness b registry state children dictionaries all child
          (local_children b registry state parent key children unique child edge)
  intro focus reached
  obtain ⟨payload,derived⟩ := witness focus reached
  cases payload with
  | node key dictionaries =>
    obtain ⟨children,safe,unique,_⟩ := selected_inv b registry state focus key dictionaries derived
    exact ⟨key,children,.selected safe unique⟩

/-- Exact finite success criterion. Neither direction mentions a producer,
operational execution, model, semantic Joint, or Evidence. -/
theorem success_iff (root : v.Demand) :
    (∃ dictionary, B4TargetV3.Classify b registry state root (.selected dictionary)) ↔
    (∀ focus, Reach (B4TargetV3.Local b registry state) root focus →
      ∃ key children, B4TargetV3.Local b registry state focus (.selected key children)) ∧
      Acc (Child (B4TargetV3.Local b registry state)) root := by
  constructor
  · rintro ⟨dictionary,classified⟩
    exact ⟨closure_selected b registry state root dictionary classified,
      classified_accessible b registry state root dictionary classified⟩
  · rintro ⟨selected,accessible⟩
    exact GeneralDictionaryLocalReadback.classified_exists b registry state root selected accessible
end Yulang.GeneralDictionaryLocalReadbackExact
