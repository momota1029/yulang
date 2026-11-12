import Yulang.GeneralDictionaryDiagnosticAccessibility
import Yulang.GeneralDictionaryLocalReadback

/-! Finite diagnostic existence from independent where accessibility and local
totality on its reachable closure. Terminal failures are retained as leaves.
This is not termination or completeness of an operational source executor. -/
namespace Yulang.GeneralDictionaryDiagnosticTotality
open CommonRoleOutermostResolver GeneralDictionaryLocalReadback
variable {v : B4Target.Vocabulary} (b : B4Target.SourceBoundary v)
    (registry : v.Registry) (state : v.State)

private theorem list_trees (children : List v.Demand) (P : v.Demand → Tree → Prop)
    (each : ∀ child ∈ children, ∃ tree, P child tree) :
    ∃ trees, All₂ P children trees := by
  induction children with
  | nil => exact ⟨[],.nil⟩
  | cons child rest ih =>
    obtain ⟨first,one⟩ := each child (List.mem_cons_self)
    obtain ⟨trees,all⟩ := ih (fun child member => each child (List.mem_cons_of_mem _ member))
    exact ⟨first :: trees,.cons one all⟩

/-- No completed classification or semantic evidence is assumed. The finite
diagnostic may contain pending, rejected and ambiguous leaves. -/
theorem diagnostic_exists (root : v.Demand)
    (localExists : ∀ focus, Reach (B4TargetV3.Local b registry state) root focus →
      ∃ frontier, B4TargetV3.Local b registry state focus frontier)
    (accessible : Acc (Child (B4TargetV3.Local b registry state)) root) :
    ∃ tree, Resolves (B4TargetV3.Local b registry state) root tree := by
  have construct : ∀ focus, Acc (Child (B4TargetV3.Local b registry state)) focus →
      Reach (B4TargetV3.Local b registry state) root focus →
      ∃ tree, Resolves (B4TargetV3.Local b registry state) focus tree := by
    intro focus accessible
    induction accessible with
    | intro focus below ih =>
      intro reached
      obtain ⟨frontier,localRule⟩ := localExists focus reached
      cases frontier with
      | pending => exact ⟨.pending,.pending localRule⟩
      | rejected => exact ⟨.rejected,.rejected localRule⟩
      | ambiguous => exact ⟨.ambiguous,.ambiguous localRule⟩
      | selected key children =>
        obtain ⟨trees,all⟩ := list_trees children
          (Resolves (B4TargetV3.Local b registry state))
          (fun child member => ih child ⟨key,children,localRule,member⟩
            (.child reached ⟨key,children,localRule,member⟩))
        exact ⟨.selected key trees,.selected localRule all⟩
  exact construct root accessible .root

/-- Under local existence on the selected-child closure, accessibility is
exactly finite diagnostic existence, not necessarily dictionary success. -/
theorem diagnostic_iff_accessible (root : v.Demand)
    (localExists : ∀ focus, Reach (B4TargetV3.Local b registry state) root focus →
      ∃ frontier, B4TargetV3.Local b registry state focus frontier) :
    (∃ tree, Resolves (B4TargetV3.Local b registry state) root tree) ↔
      Acc (Child (B4TargetV3.Local b registry state)) root := by
  constructor
  · rintro ⟨tree,resolved⟩
    exact GeneralDictionaryDiagnosticAccessibility.resolved_accessible b registry state root tree resolved
  · exact diagnostic_exists b registry state root localExists

private theorem list_witness (children : List v.Demand) (trees : List Tree)
    (all : All₂ (Resolves (B4TargetV3.Local b registry state)) children trees) :
    ∀ child ∈ children, ∃ tree, Resolves (B4TargetV3.Local b registry state) child tree := by
  induction all with
  | nil => intro child member; cases member
  | cons first rest ih =>
    intro child member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨_,first⟩
    · exact ih child member

private theorem resolved_child (root : v.Demand) (tree : Tree)
    (resolved : Resolves (B4TargetV3.Local b registry state) root tree)
    (child : v.Demand) (edge : Child (B4TargetV3.Local b registry state) child root) :
    ∃ tree, Resolves (B4TargetV3.Local b registry state) child tree := by
  obtain ⟨key,children,selected,member⟩ := edge
  cases resolved with
  | pending rule => cases B4TargetV3.local_functional rule selected
  | rejected rule => cases B4TargetV3.local_functional rule selected
  | ambiguous rule => cases B4TargetV3.local_functional rule selected
  | selected rule all =>
    have same := (Frontier.selected.inj (B4TargetV3.local_functional selected rule)).2
    rw [same] at member
    exact list_witness b registry state _ _ all child member

private theorem resolved_local (root : v.Demand) (tree : Tree)
    (resolved : Resolves (B4TargetV3.Local b registry state) root tree) :
    ∃ frontier, B4TargetV3.Local b registry state root frontier := by
  cases resolved with
  | pending rule => exact ⟨_,rule⟩
  | rejected rule => exact ⟨_,rule⟩
  | ambiguous rule => exact ⟨_,rule⟩
  | selected rule all => exact ⟨_,rule⟩

/-- A finite diagnostic supplies local decisions on its entire independent
selected-child closure. Functionality excludes unrecorded alternative branches.
This is conditional on a given diagnostic, not actual source Local totality. -/
theorem closure_local (root : v.Demand) (tree : Tree)
    (resolved : Resolves (B4TargetV3.Local b registry state) root tree) :
    ∀ focus, Reach (B4TargetV3.Local b registry state) root focus →
      ∃ frontier, B4TargetV3.Local b registry state focus frontier := by
  have witnesses : ∀ focus, Reach (B4TargetV3.Local b registry state) root focus →
      ∃ tree, Resolves (B4TargetV3.Local b registry state) focus tree := by
    intro focus reached
    induction reached with
    | root => exact ⟨tree,resolved⟩
    | child reached edge ih =>
      obtain ⟨tree,valid⟩ := ih
      exact resolved_child b registry state _ tree valid _ edge
  intro focus reached
  obtain ⟨tree,valid⟩ := witnesses focus reached
  exact resolved_local b registry state focus tree valid

/-- Exact finite diagnostic criterion. No premise or conclusion states totality
of Local for all source states, nor termination of an operational executor. -/
theorem diagnostic_iff (root : v.Demand) :
    (∃ tree, Resolves (B4TargetV3.Local b registry state) root tree) ↔
    (∀ focus, Reach (B4TargetV3.Local b registry state) root focus →
      ∃ frontier, B4TargetV3.Local b registry state focus frontier) ∧
      Acc (Child (B4TargetV3.Local b registry state)) root := by
  constructor
  · rintro ⟨tree,resolved⟩
    exact ⟨closure_local b registry state root tree resolved,
      GeneralDictionaryDiagnosticAccessibility.resolved_accessible b registry state root tree resolved⟩
  · rintro ⟨localExists,accessible⟩
    exact diagnostic_exists b registry state root localExists accessible

end Yulang.GeneralDictionaryDiagnosticTotality
