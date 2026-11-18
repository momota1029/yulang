import Yulang.GeneralRebaseUniversalBasis263
import Yulang.GeneralRebaseMultiSelection263
import Yulang.GeneralRebaseValidatedOutcome263
import Yulang.GeneralRebaseChildRequestPool262

namespace Yulang.GeneralRebaseUniversalObserver263
open GeneralRebaseStep258
open GeneralSourceState (Output)
open GeneralRebaseMultiSelection263 (Selection proposal check Ready Diagnostic)
open GeneralRebaseUniversalBasis263 (basis)

abbrev Current (owners : List Nat) (pool : List Output) := State (basis owners pool)

def observe (owners : List Nat) (pool : List Output)
 (inspect : Current owners pool → GeneralNominalCenteredSteps.State roles)
 (select : Current owners pool → List (Selection roles)) : Observer (basis owners pool) :=
 fun state => (select state).map (proposal (inspect state))

def validate (owners : List Nat) (pool : List Output)
 (inspect : Current owners pool → GeneralNominalCenteredSteps.State roles)
 (select : Current owners pool → List (Selection roles)) : Current owners pool → Except (Diagnostic roles) Unit :=
 fun state => check (inspect state) (select state)

def run (owners : List Nat) (pool : List Output)
 (inspect : Current owners pool → GeneralNominalCenteredSteps.State roles)
 (select : Current owners pool → List (Selection roles)) :=
 GeneralRebaseValidatedDriver263.run (observe owners pool inspect select) (validate owners pool inspect select)

/-- Pure address closure. No fixed representative Plan, layout equality,
binder agreement, semantic Models or readiness premise is used. -/
theorem closed (owners : List Nat) (pool : List Output)
 (inspect : Current owners pool → GeneralNominalCenteredSteps.State roles)
 (select : Current owners pool → List (Selection roles))
 (listed : ∀ state entry, entry ∈ select state → entry.owner ∈ owners)
 (coverage : ∀ state, GeneralRebaseChildRequestPool262.Covered (inspect state) pool) :
 GeneralRebaseClosedObserver259.Closed (observe owners pool inspect select) := by
 intro state proposed member
 obtain ⟨selected,chosen,rfl⟩ := List.mem_map.mp member
 apply GeneralRebaseUniversalBasis263.proposal_covered owners pool selected.plan selected.owner (listed state selected chosen)
 intro output member
 apply GeneralRebaseChildRequestPool262.requests_covered (inspect state) pool (coverage state) selected.root output
 simpa only [GeneralRebaseMultiSelection263.requests,GeneralRebaseExecutableRequests262.requests_eq] using member

theorem certificate (owners : List Nat) (pool : List Output)
 (inspect : Current owners pool → GeneralNominalCenteredSteps.State roles)
 (select : Current owners pool → List (Selection roles)) (before after : Current owners pool)
 (success : run owners pool inspect select before = .ok after) :
 ∃ history, GeneralRebaseValidatedDriver263.Trace (observe owners pool inspect select)
   (validate owners pool inspect select) history before after ∧
 GeneralRebaseBudget258.Runs (observe owners pool inspect select) history.length before after ∧
 history.length ≤ owners.length * (pool.length + pool.length * pool.length) ∧
 (∀ state ∈ history, Ready (inspect state) (select state)) ∧ Ready (inspect after) (select after) ∧
 (∀ next, ¬ Step (observe owners pool inspect select) after next) := by
 obtain ⟨history,trace,path,_,checked,final,terminal⟩ := GeneralRebaseValidatedDriver263.certificate _ _ before after success
 refine ⟨history,trace,path,GeneralRebaseUniversalBasis263.run_bound owners pool _ path,?_,?_,terminal⟩
 · intro state member
   exact (GeneralRebaseMultiSelection263.check_exact ..).mp (checked state member)
 · exact (GeneralRebaseMultiSelection263.check_exact ..).mp final

theorem outcome (owners : List Nat) (pool : List Output)
 (inspect : Current owners pool → GeneralNominalCenteredSteps.State roles)
 (select : Current owners pool → List (Selection roles))
 (listed : ∀ state entry, entry ∈ select state → entry.owner ∈ owners)
 (coverage : ∀ state, GeneralRebaseChildRequestPool262.Covered (inspect state) pool)
 (before : Current owners pool) :
 (∃ after history, run owners pool inspect select before = .ok after ∧
   GeneralRebaseValidatedDriver263.Trace (observe owners pool inspect select)
     (validate owners pool inspect select) history before after ∧
   history.length ≤ owners.length * (pool.length + pool.length * pool.length)) ∨
 (∃ reason current steps, run owners pool inspect select before = .error (.validation reason) ∧
   GeneralRebaseBudget258.Runs (observe owners pool inspect select) steps before current ∧
   steps ≤ owners.length * (pool.length + pool.length * pool.length) ∧ reason.selected ∈ select current ∧
   GeneralRebaseClassCheck261.check reason.selected.plan
     (GeneralRebaseMultiSelection263.requests (inspect current) reason.selected) = .error reason.reason) := by
 rcases GeneralRebaseValidatedOutcome263.outcome _ _ (closed owners pool inspect select listed coverage) before with success | failure
 · obtain ⟨after,history,success,trace,_⟩ := success
   exact Or.inl ⟨after,history,success,trace,GeneralRebaseUniversalBasis263.run_bound owners pool _
     (GeneralRebaseValidatedDriver263.to_runs _ _ trace)⟩
 · obtain ⟨reason,current,steps,failed,path,_,diagnostic⟩ := failure
   obtain ⟨selected,exactError⟩ := GeneralRebaseMultiSelection263.error_selected _ _ reason diagnostic
   exact Or.inr ⟨reason,current,steps,failed,path,GeneralRebaseUniversalBasis263.run_bound owners pool _ path,selected,exactError⟩
end Yulang.GeneralRebaseUniversalObserver263
