import Yulang.GeneralRebaseSettle259
namespace Yulang.GeneralRebaseClosedObserver259
open GeneralRebaseStep258 GeneralRebaseCheckedWrite259 GeneralRebaseScheduler259 GeneralRebaseSettle259
variable {basis : List Fact}

def Closed (observe : Observer basis) : Prop := ∀ state proposal, proposal ∈ observe state → proposal ⊆ basis

theorem scan_error (state : State basis) (proposals : List Proposal) (missing : List Fact)
 (failed : scan state proposals = .error missing) :
 ∃ proposal ∈ proposals, commit state proposal = .error missing := by
 induction proposals with
 | nil => cases failed
 | cons proposal rest ih =>
   unfold scan at failed
   split at failed
   · rename_i error failedHere
     cases Except.error.inj failed
     exact ⟨proposal,List.mem_cons_self,failedHere⟩
   · obtain ⟨found,member,valid⟩ := ih failed
     exact ⟨found,List.mem_cons_of_mem _ member,valid⟩
   · cases failed

theorem next_no_error (observe : Observer basis) (closed : Closed observe)
 (state : State basis) (missing : List Fact) : next observe state ≠ .error missing := by
 intro failed
 obtain ⟨proposal,member,error⟩ := scan_error state (observe state) missing failed
 rw [supported state proposal (closed state proposal member)] at error
 cases error

theorem settle_no_error (observe : Observer basis) (closed : Closed observe)
 (state : State basis) (missing : List Fact) : settle observe state ≠ .error missing := by
 generalize equal : state.remaining.length = measure
 induction measure using Nat.strongRecOn generalizing state with
 | ind measure ih =>
   intro failed
   rw [settle] at failed
   split at failed
   · rename_i error outcome
     exact next_no_error observe closed state error outcome
   · cases failed
   · rename_i after advanced
     have smaller := decreases observe (next_step observe state after advanced)
     rw [equal] at smaller
     exact ih _ smaller after rfl failed

/-- Basis closure of the observer yields a computed terminal state and a
bounded trace. This premise is NOT automatically true of a source compiler. -/
theorem completion (observe : Observer basis) (closed : Closed observe) (state : State basis) :
 ∃ final steps, settle observe state = .ok final ∧
 GeneralRebaseBudget258.Runs observe steps state final ∧ steps ≤ state.remaining.length ∧
 (∀ after, ¬ Step observe final after) := by
 cases result : settle observe state with
 | error missing => exact False.elim (settle_no_error observe closed state missing result)
 | ok final =>
   obtain ⟨steps,path,bound⟩ := successful_budget observe state final result
   exact ⟨final,steps,rfl,path,bound,successful_quiescent observe state final result⟩
end Yulang.GeneralRebaseClosedObserver259
