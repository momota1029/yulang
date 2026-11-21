import Yulang.GeneralDeclarativeFollowerResolve324

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeFollowerDerived324
open GeneralDeclarativeFollower324 (later ready_iff ordinary_value)
open GeneralDeclarativeFollowerResolve324 (chosen_evidence blocked_without)
open GeneralDeclarativeHiddenState324 (root child final)
open GeneralDeclarativeHiddenResolve324 (branch dictionary final_selected child_chosen)
open GeneralDeclarativeHiddenDecl324 (registry interpretation)
open GeneralDeclarativeExampleSource320 (leaf)
open GeneralDeclarativeEvidence320 (Evidence)
open GeneralDeclarativeHead320 (Models)
open CommonRoleOutermostResolver (Classify Dictionary)

/-- Completion here comes from checked independent child/parent
diagnostics in this fixture. Their own input facts are genuine source
facts so these diagnostics do not rely on the follower they unblock. -/
def completed (owner : Nat) : Prop :=
  (owner = 1 ∧ Classify (branch (fun _ => False)) root (.selected dictionary)) ∨
  (owner = 2 ∧ Classify (branch (fun _ => False)) child (.selected (.node leaf.id [])))

theorem parent_finished : completed 1 := .inl ⟨rfl,final_selected _⟩

theorem child_finished : completed 2 :=
  .inr ⟨rfl,⟨.selected leaf.id [],.selected (child_chosen _) .nil,.selected .nil (.selected rfl)⟩⟩

theorem final_transition :
    branch (fun _ => False) later .pending ∧
    Classify (branch completed) later (.selected (.node leaf.id [])) ∧
    ∀ m, Models final m → Evidence registry interpretation m later (.node leaf.id []) :=
  ⟨blocked_without _ And.left,chosen_evidence completed parent_finished child_finished⟩

end Yulang.GeneralDeclarativeFollowerDerived324
