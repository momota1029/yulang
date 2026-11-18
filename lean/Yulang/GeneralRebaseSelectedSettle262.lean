import Yulang.GeneralRebaseSelectedCheck262

namespace Yulang.GeneralRebaseSelectedSettle262
open GeneralNominalCenters GeneralRebaseStep258
open GeneralSourceState (Output)
open GeneralSourceDictionaries (Occurrence)
open GeneralRebaseObservedPlan262 (observe)

inductive Failure (roles : Roles.RoleDecls) where
 | selected (failure : GeneralRebaseSelectedCheck262.Failure roles)
 | outside (facts : List Fact)

abbrev Current (fixed : Plan roles) (owner : Nat) (pool : List Output) :=
 State (GeneralRebaseStableClass261.facts fixed owner pool)

/-- Validate just the roots actually selected at this round, then perform
one existing checked finite-fact scheduling round. Errors remain internal. -/
def run (fixed : Plan roles) (owner : Nat) (pool : List Output)
 (inspect : Current fixed owner pool → GeneralNominalCenteredSteps.State roles)
 (roots : Current fixed owner pool → List (Occurrence roles))
 (plans : Current fixed owner pool → Occurrence roles → Plan roles)
 (state : Current fixed owner pool) : Except (Failure roles) (Current fixed owner pool) :=
 match GeneralRebaseSelectedCheck262.checkRoots (inspect state) (plans state) (roots state) with
 | .error failure => .error (.selected failure)
 | .ok () =>
   match _outcome : GeneralRebaseScheduler259.next (observe fixed owner pool inspect roots plans) state with
   | .error missing => .error (.outside missing)
   | .ok none => .ok state
   | .ok (some after) => run fixed owner pool inspect roots plans after
termination_by state.remaining.length
decreasing_by exact decreases _ (GeneralRebaseScheduler259.next_step _ state after _outcome)

/-- The list contains precisely the pre-write states, in execution order.
The terminal state's readiness and terminal scheduler result are also retained. -/
inductive Trace (fixed : Plan roles) (owner : Nat) (pool : List Output)
 (inspect : Current fixed owner pool → GeneralNominalCenteredSteps.State roles)
 (roots : Current fixed owner pool → List (Occurrence roles))
 (plans : Current fixed owner pool → Occurrence roles → Plan roles) :
 List (Current fixed owner pool) → Current fixed owner pool → Current fixed owner pool → Prop where
 | done {state} : GeneralRebaseSelectedCheck262.ReadyRoots (inspect state) (plans state) (roots state) →
   GeneralRebaseScheduler259.next (observe fixed owner pool inspect roots plans) state = .ok none →
   Trace fixed owner pool inspect roots plans [] state state
 | next {before middle final history} :
   GeneralRebaseSelectedCheck262.ReadyRoots (inspect before) (plans before) (roots before) →
   GeneralRebaseScheduler259.next (observe fixed owner pool inspect roots plans) before = .ok (some middle) →
   Trace fixed owner pool inspect roots plans history middle final →
   Trace fixed owner pool inspect roots plans (before :: history) before final

theorem successful_trace (fixed : Plan roles) (owner : Nat) (pool : List Output)
 (inspect) (roots) (plans) (state final : Current fixed owner pool)
 (success : run fixed owner pool inspect roots plans state = .ok final) :
 ∃ history, Trace fixed owner pool inspect roots plans history state final := by
 generalize equal : state.remaining.length = measure
 induction measure using Nat.strongRecOn generalizing state with
 | ind measure ih =>
   rw [run] at success
   split at success
   · cases success
   · rename_i checked
     have ready := (GeneralRebaseSelectedCheck262.check_exact ..).mp checked
     split at success
     · cases success
     · rename_i terminal
       cases Except.ok.inj success
       exact ⟨[],.done ready terminal⟩
     · rename_i after advanced
       have smaller := decreases _ (GeneralRebaseScheduler259.next_step _ state after advanced)
       rw [equal] at smaller
       obtain ⟨history,trace⟩ := ih _ smaller after success rfl
       exact ⟨state :: history,.next ready advanced trace⟩

theorem to_runs (fixed : Plan roles) (owner : Nat) (pool : List Output)
 (inspect) (roots) (plans) {history state final}
 (trace : Trace fixed owner pool inspect roots plans history state final) :
 GeneralRebaseBudget258.Runs (observe fixed owner pool inspect roots plans) history.length state final := by
 induction trace with
 | done => exact .nil _
 | next _ advanced _ ih => exact .next (GeneralRebaseScheduler259.next_step _ _ _ advanced) ih

theorem states_ready (fixed : Plan roles) (owner : Nat) (pool : List Output)
 (inspect) (roots) (plans) {history state final}
 (trace : Trace fixed owner pool inspect roots plans history state final) :
 (∀ before ∈ history, GeneralRebaseSelectedCheck262.ReadyRoots (inspect before) (plans before) (roots before)) ∧
 GeneralRebaseSelectedCheck262.ReadyRoots (inspect final) (plans final) (roots final) := by
 induction trace with
 | done ready _ => exact ⟨by simp,ready⟩
 | next ready _ _ ih =>
   refine ⟨?_,ih.2⟩
   intro before member
   rcases List.mem_cons.mp member with rfl | member
   · exact ready
   · exact ih.1 before member

theorem terminal (fixed : Plan roles) (owner : Nat) (pool : List Output)
 (inspect) (roots) (plans) {history state final}
 (trace : Trace fixed owner pool inspect roots plans history state final) :
 GeneralRebaseScheduler259.next (observe fixed owner pool inspect roots plans) final = .ok none := by
 induction trace with
 | done _ terminal => exact terminal
 | next _ _ _ ih => exact ih

theorem trace_success (fixed : Plan roles) (owner : Nat) (pool : List Output)
 (inspect) (roots) (plans) {history state final}
 (trace : Trace fixed owner pool inspect roots plans history state final) :
 run fixed owner pool inspect roots plans state = .ok final := by
 induction trace with
 | done ready stopped =>
   rw [run,(GeneralRebaseSelectedCheck262.check_exact ..).mpr ready,stopped]
 | next ready advanced _ ih =>
   rw [run,(GeneralRebaseSelectedCheck262.check_exact ..).mpr ready,advanced]
   exact ih

theorem ordinary_settle (fixed : Plan roles) (owner : Nat) (pool : List Output)
 (inspect) (roots) (plans) {history state final}
 (trace : Trace fixed owner pool inspect roots plans history state final) :
 GeneralRebaseSettle259.settle (observe fixed owner pool inspect roots plans) state = .ok final := by
 induction trace with
 | done _ stopped => rw [GeneralRebaseSettle259.settle,stopped]
 | next _ advanced _ ih => rw [GeneralRebaseSettle259.settle,advanced]; exact ih

/-- Successful execution derives readiness only for rounds actually visited;
there is no all-pool or all-state readiness assumption. -/
theorem certificate (fixed : Plan roles) (owner : Nat) (pool : List Output)
 (inspect) (roots) (plans) (state final : Current fixed owner pool)
 (success : run fixed owner pool inspect roots plans state = .ok final) :
 ∃ history, Trace fixed owner pool inspect roots plans history state final ∧
 GeneralRebaseBudget258.Runs (observe fixed owner pool inspect roots plans) history.length state final ∧
 history.length ≤ state.remaining.length ∧
 (∀ before ∈ history, GeneralRebaseSelectedCheck262.ReadyRoots (inspect before) (plans before) (roots before)) ∧
 GeneralRebaseSelectedCheck262.ReadyRoots (inspect final) (plans final) (roots final) ∧
 (∀ after, ¬ Step (observe fixed owner pool inspect roots plans) final after) := by
 obtain ⟨history,trace⟩ := successful_trace fixed owner pool inspect roots plans state final success
 have path := to_runs fixed owner pool inspect roots plans trace
 have budget := GeneralRebaseBudget258.budget _ path
 have ready := states_ready fixed owner pool inspect roots plans trace
 exact ⟨history,trace,path,by omega,ready.1,ready.2,
   GeneralRebaseScheduler259.terminal _ final (terminal fixed owner pool inspect roots plans trace)⟩
end Yulang.GeneralRebaseSelectedSettle262
