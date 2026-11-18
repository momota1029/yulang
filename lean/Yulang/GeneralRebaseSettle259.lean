import Yulang.GeneralRebaseScheduler259
namespace Yulang.GeneralRebaseSettle259
open GeneralRebaseStep258 GeneralRebaseScheduler259
variable {basis : List Fact}

/-- Terminating iteration of the checked finite-fact scheduler. Unsupported
facts are an internal error; this is not a general language resolve function. -/
def settle (observe : Observer basis) (state : State basis) : Except (List Fact) (State basis) :=
 match _outcome : next observe state with
 | .error missing => .error missing
 | .ok none => .ok state
 | .ok (some after) => settle observe after
termination_by state.remaining.length
decreasing_by exact decreases observe (next_step observe state after _outcome)

theorem successful_terminal (observe : Observer basis) (state final : State basis)
 (success : settle observe state = .ok final) : next observe final = .ok none := by
 generalize equal : state.remaining.length = measure
 induction measure using Nat.strongRecOn generalizing state with
 | ind measure ih =>
   rw [settle] at success
   split at success
   · cases success
   · rename_i stopped
     cases Except.ok.inj success
     exact stopped
   · rename_i after advanced
     have smaller := decreases observe (next_step observe state after advanced)
     rw [equal] at smaller
     exact ih _ smaller after success rfl

theorem successful_path (observe : Observer basis) (state final : State basis)
 (success : settle observe state = .ok final) :
 ∃ steps, GeneralRebaseBudget258.Runs observe steps state final := by
 generalize equal : state.remaining.length = measure
 induction measure using Nat.strongRecOn generalizing state with
 | ind measure ih =>
   rw [settle] at success
   split at success
   · cases success
   · cases Except.ok.inj success
     exact ⟨0,.nil _⟩
   · rename_i after advanced
     have step := next_step observe state after advanced
     have smaller := decreases observe step
     rw [equal] at smaller
     obtain ⟨steps,rest⟩ := ih _ smaller after success rfl
     exact ⟨steps+1,.next step rest⟩

theorem successful_budget (observe : Observer basis) (state final : State basis)
 (success : settle observe state = .ok final) :
 ∃ steps, GeneralRebaseBudget258.Runs observe steps state final ∧ steps ≤ state.remaining.length := by
 obtain ⟨steps,path⟩ := successful_path observe state final success
 have bound := GeneralRebaseBudget258.budget observe path
 exact ⟨steps,path,by omega⟩

theorem successful_quiescent (observe : Observer basis) (state final : State basis)
 (success : settle observe state = .ok final) : ∀ after, ¬ Step observe final after :=
 terminal observe final (successful_terminal observe state final success)
end Yulang.GeneralRebaseSettle259
