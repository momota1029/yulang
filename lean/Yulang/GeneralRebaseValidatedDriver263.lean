import Yulang.GeneralRebaseClosedObserver259

namespace Yulang.GeneralRebaseValidatedDriver263
open GeneralRebaseStep258
variable {basis : List Fact} {ε : Type}

inductive Failure (ε : Type) where
 | validation (reason : ε)
 | outside (missing : List Fact)

/-- Check every currently selected obligation before choosing the next write.
Validation errors are internal diagnostics, not source-language rejection. -/
def run (observe : Observer basis) (validate : State basis → Except ε Unit)
 (state : State basis) : Except (Failure ε) (State basis) :=
 match validate state with
 | .error reason => .error (.validation reason)
 | .ok () =>
   match _outcome : GeneralRebaseScheduler259.next observe state with
   | .error missing => .error (.outside missing)
   | .ok none => .ok state
   | .ok (some after) => run observe validate after
termination_by state.remaining.length
decreasing_by exact decreases _ (GeneralRebaseScheduler259.next_step _ state after _outcome)

inductive Trace (observe : Observer basis) (validate : State basis → Except ε Unit) :
 List (State basis) → State basis → State basis → Prop where
 | done {state} : validate state = .ok () →
   GeneralRebaseScheduler259.next observe state = .ok none → Trace observe validate [] state state
 | next {before middle final history} : validate before = .ok () →
   GeneralRebaseScheduler259.next observe before = .ok (some middle) →
   Trace observe validate history middle final → Trace observe validate (before :: history) before final

theorem successful_trace (observe : Observer basis) (validate : State basis → Except ε Unit)
 (state final : State basis) (success : run observe validate state = .ok final) :
 ∃ history, Trace observe validate history state final := by
 generalize equal : state.remaining.length = measure
 induction measure using Nat.strongRecOn generalizing state with
 | ind measure ih =>
   rw [run] at success
   split at success
   · cases success
   · rename_i checked
     split at success
     · cases success
     · rename_i terminal
       cases Except.ok.inj success
       exact ⟨[],.done checked terminal⟩
     · rename_i after advanced
       have smaller := decreases _ (GeneralRebaseScheduler259.next_step _ state after advanced)
       rw [equal] at smaller
       obtain ⟨history,trace⟩ := ih _ smaller after success rfl
       exact ⟨state :: history,.next checked advanced trace⟩

theorem to_runs (observe : Observer basis) (validate : State basis → Except ε Unit)
 {history before after} (trace : Trace observe validate history before after) :
 GeneralRebaseBudget258.Runs observe history.length before after := by
 induction trace with
 | done => exact .nil _
 | next _ advanced _ ih => exact .next (GeneralRebaseScheduler259.next_step _ _ _ advanced) ih

theorem states_valid (observe : Observer basis) (validate : State basis → Except ε Unit)
 {history before after} (trace : Trace observe validate history before after) :
 (∀ state ∈ history, validate state = .ok ()) ∧ validate after = .ok () := by
 induction trace with
 | done checked _ => exact ⟨by simp,checked⟩
 | next checked _ _ ih =>
   refine ⟨?_,ih.2⟩
   intro state member
   rcases List.mem_cons.mp member with rfl | member
   · exact checked
   · exact ih.1 state member

theorem terminal (observe : Observer basis) (validate : State basis → Except ε Unit)
 {history before after} (trace : Trace observe validate history before after) :
 GeneralRebaseScheduler259.next observe after = .ok none := by
 induction trace with
 | done _ terminal => exact terminal
 | next _ _ _ ih => exact ih

theorem trace_success (observe : Observer basis) (validate : State basis → Except ε Unit)
 {history before after} (trace : Trace observe validate history before after) :
 run observe validate before = .ok after := by
 induction trace with
 | done checked terminal => rw [run,checked,terminal]
 | next checked advanced _ ih => rw [run,checked,advanced]; exact ih

theorem ordinary_settle (observe : Observer basis) (validate : State basis → Except ε Unit)
 {history before after} (trace : Trace observe validate history before after) :
 GeneralRebaseSettle259.settle observe before = .ok after := by
 induction trace with
 | done _ terminal => rw [GeneralRebaseSettle259.settle,terminal]
 | next _ advanced _ ih => rw [GeneralRebaseSettle259.settle,advanced]; exact ih

theorem certificate (observe : Observer basis) (validate : State basis → Except ε Unit)
 (before after : State basis) (success : run observe validate before = .ok after) :
 ∃ history, Trace observe validate history before after ∧
 GeneralRebaseBudget258.Runs observe history.length before after ∧
 history.length ≤ before.remaining.length ∧
 (∀ state ∈ history, validate state = .ok ()) ∧ validate after = .ok () ∧
 (∀ next, ¬ Step observe after next) := by
 obtain ⟨history,trace⟩ := successful_trace observe validate before after success
 have path := to_runs observe validate trace
 have checked := states_valid observe validate trace
 have budget := GeneralRebaseBudget258.budget observe path
 exact ⟨history,trace,path,by omega,checked.1,checked.2,
   GeneralRebaseScheduler259.terminal observe after (terminal observe validate trace)⟩
end Yulang.GeneralRebaseValidatedDriver263
