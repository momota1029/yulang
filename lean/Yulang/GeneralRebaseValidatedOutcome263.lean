import Yulang.GeneralRebaseValidatedDriver263
namespace Yulang.GeneralRebaseValidatedOutcome263
open GeneralRebaseStep258 GeneralRebaseValidatedDriver263
variable {basis : List Fact} {ε : Type}

def At (observe : Observer basis) (validate : State basis → Except ε Unit)
 (state : State basis) : Failure ε → Prop
 | .validation reason => validate state = .error reason
 | .outside facts => validate state = .ok () ∧ GeneralRebaseScheduler259.next observe state = .error facts

theorem error_path (observe : Observer basis) (validate : State basis → Except ε Unit)
 (state : State basis) (failure : Failure ε) (failed : run observe validate state = .error failure) :
 ∃ current steps, GeneralRebaseBudget258.Runs observe steps state current ∧ At observe validate current failure := by
 generalize equal : state.remaining.length = measure
 induction measure using Nat.strongRecOn generalizing state with
 | ind measure ih =>
   rw [run] at failed
   split at failed
   · rename_i reason checked
     cases Except.error.inj failed
     exact ⟨state,0,.nil _,checked⟩
   · rename_i checked
     split at failed
     · rename_i missing scheduled
       cases Except.error.inj failed
       exact ⟨state,0,.nil _,checked,scheduled⟩
     · cases failed
     · rename_i after advanced
       have step := GeneralRebaseScheduler259.next_step _ state after advanced
       have smaller := decreases _ step
       rw [equal] at smaller
       obtain ⟨current,steps,path,diagnostic⟩ := ih _ smaller after failed rfl
       exact ⟨current,steps+1,.next step path,diagnostic⟩

theorem no_outside (observe : Observer basis) (validate : State basis → Except ε Unit)
 (closed : GeneralRebaseClosedObserver259.Closed observe) (state : State basis) (missing : List Fact) :
 run observe validate state ≠ .error (.outside missing) := by
 intro failed
 obtain ⟨current,_,_,diagnostic⟩ := error_path observe validate state (.outside missing) failed
 exact GeneralRebaseClosedObserver259.next_no_error observe closed current missing diagnostic.2

/-- Finite successful checked trace or a precise validation failure at a
reachable finite state. This theorem has no all-state validation premise. -/
theorem outcome (observe : Observer basis) (validate : State basis → Except ε Unit)
 (closed : GeneralRebaseClosedObserver259.Closed observe) (before : State basis) :
 (∃ after history, run observe validate before = .ok after ∧ Trace observe validate history before after ∧
   history.length ≤ before.remaining.length) ∨
 (∃ reason current steps, run observe validate before = .error (.validation reason) ∧
   GeneralRebaseBudget258.Runs observe steps before current ∧ steps ≤ before.remaining.length ∧
   validate current = .error reason) := by
 cases result : run observe validate before with
 | ok after =>
   obtain ⟨history,trace⟩ := successful_trace observe validate before after result
   have budget := GeneralRebaseBudget258.budget observe (to_runs observe validate trace)
   exact Or.inl ⟨after,history,rfl,trace,by omega⟩
 | error failure =>
   cases failure with
   | outside missing => exact False.elim (no_outside observe validate closed before missing result)
   | validation reason =>
     obtain ⟨current,steps,path,diagnostic⟩ := error_path observe validate before (.validation reason) result
     have budget := GeneralRebaseBudget258.budget observe path
     exact Or.inr ⟨reason,current,steps,rfl,path,by omega,diagnostic⟩
end Yulang.GeneralRebaseValidatedOutcome263
