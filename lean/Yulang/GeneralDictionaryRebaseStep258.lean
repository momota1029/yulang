import Yulang.GeneralRebaseStep258
namespace Yulang.GeneralDictionaryRebaseStep258
open GeneralRebaseStep258
/-- I45 terminal packet table, not a general source observer. -/
def facts : List Fact := [.installed 0, .lower 0 0, .upper 0 1, .binder 0, .binder 1]
abbrev initialState := initial facts
abbrev finalState := done facts
def observe : Observer facts := fun _ => [facts]
def project (n : Nat) : State facts := if n = 0 then initialState else finalState

theorem writes_once : write initialState facts = finalState := by apply state_ext; decide

theorem first_step : Step observe initialState finalState :=
 ⟨facts, by simp [observe], writes_once.symm, by decide⟩

theorem final_stops : ∀ after, ¬ Step observe finalState after := by
 intro after step
 obtain ⟨proposal,_,equal,changed⟩ := step
 apply changed
 rw [equal]
 rfl

theorem first_unique (after : State facts) (step : Step observe initialState after) : after = finalState := by
 obtain ⟨proposal,member,equal,_⟩ := step
 have same : proposal = facts := by simpa [observe] using member
 subst proposal
 exact equal.trans writes_once

theorem no_two_steps (middle last : State facts) :
 ¬ (Step observe initialState middle ∧ Step observe middle last) := by
 rintro ⟨first,second⟩
 rw [first_unique middle first] at second
 exact final_stops last second

theorem terminating (state : State facts) : Acc (fun after before => Step observe before after) state :=
 accessible observe state

theorem fixed_aggregates : lowerAtoms finalState 0 = [0] ∧ upperAtoms finalState 0 = [1] ∧
 binderFacts finalState = [0,1] := by decide

theorem old_positive_project (n : Nat) : project (n+1) = finalState := by simp [project]

theorem old_repetition_blocked (n : Nat) : ¬ Step observe (project (n+1)) (project (n+2)) := by
 simp only [old_positive_project]
 exact final_stops _
end Yulang.GeneralDictionaryRebaseStep258
