import Yulang.GeneralDictionaryEarlyMergeDiagnostics
import Yulang.B4TargetV3Functionality

/-! Finite diagnostics imply accessibility even when children fail. This does
not make a failed diagnostic a successful dictionary or prove operational termination. -/
namespace Yulang.GeneralDictionaryDiagnosticAccessibility
open CommonRoleOutermostResolver
variable {v : B4Target.Vocabulary} (b : B4Target.SourceBoundary v)
    (registry : v.Registry) (state : v.State)

private theorem terminal_accessible (root : v.Demand) (frontier : Frontier v.Demand)
    (localRule : B4TargetV3.Local b registry state root frontier)
    (terminal : ∀ key children, frontier ≠ .selected key children) :
    Acc (Child (B4TargetV3.Local b registry state)) root := by
  refine .intro root ?_
  intro child edge
  obtain ⟨key,children,selected,member⟩ := edge
  exact False.elim (terminal key children (B4TargetV3.local_functional localRule selected))

mutual
 theorem resolved_accessible (root : v.Demand) (tree : Tree)
    (resolved : Resolves (B4TargetV3.Local b registry state) root tree) :
    Acc (Child (B4TargetV3.Local b registry state)) root := by
  cases tree with
  | pending =>
    cases resolved with
    | pending localRule => exact terminal_accessible b registry state root .pending localRule (by intros; intro h; cases h)
  | rejected =>
    cases resolved with
    | rejected localRule => exact terminal_accessible b registry state root .rejected localRule (by intros; intro h; cases h)
  | ambiguous =>
    cases resolved with
    | ambiguous localRule => exact terminal_accessible b registry state root .ambiguous localRule (by intros; intro h; cases h)
  | selected key trees =>
    cases resolved with
    | selected localRule all =>
      refine .intro root ?_
      intro child edge
      obtain ⟨other,others,selected,member⟩ := edge
      have same := (Frontier.selected.inj (B4TargetV3.local_functional selected localRule)).2
      rw [same] at member
      exact resolved_children_accessible _ _ all child member
 termination_by sizeOf tree

 theorem resolved_children_accessible (children : List v.Demand) (trees : List Tree)
    (resolved : All₂ (Resolves (B4TargetV3.Local b registry state)) children trees) :
    ∀ child ∈ children, Acc (Child (B4TargetV3.Local b registry state)) child := by
  cases resolved with
  | nil => intro child member; cases member
  | cons first rest =>
    intro child member
    rcases List.mem_cons.mp member with rfl | member
    · exact resolved_accessible _ _ first
    · exact resolved_children_accessible _ _ rest child member
 termination_by sizeOf trees
end

/-- A real reachable and inhabited support state has finite where inspection,
yet no four-way Classify at the selected parent because its where children fail.
The example is not asserted to be Stable. -/
theorem actual_accessible_without_classify :
    let registry := GeneralDictionaryEarlyMergeExample.registry
    let state := GeneralDictionaryEarlyMergeExample.finish
    let root := GeneralNominalExamples.displayRoot
    let b := (GeneralNominalSupportBoundary.boundary GeneralDeclarationExamples.roles).toSourceBoundary
    B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary GeneralDeclarationExamples.roles) registry root state ∧
    GeneralNominalSaturationState.Models state.current GeneralNominalExamples.model ∧
    Acc (Child (B4TargetV3.Local b registry state)) root ∧
    ∀ outcome, ¬ B4TargetV3.Classify b registry state root outcome := by
  dsimp only
  exact ⟨GeneralDictionaryEarlyMergeExample.reachable,GeneralDictionaryEarlyMergeExample.finish_model,
    resolved_accessible (GeneralNominalSupportBoundary.boundary GeneralDeclarationExamples.roles).toSourceBoundary
      GeneralDictionaryEarlyMergeExample.registry GeneralDictionaryEarlyMergeExample.finish
      GeneralNominalExamples.displayRoot _ GeneralDictionaryEarlyMergeDiagnostics.diagnostic,
    GeneralDictionaryEarlyMergeDiagnostics.root_no_classify⟩
end Yulang.GeneralDictionaryDiagnosticAccessibility
