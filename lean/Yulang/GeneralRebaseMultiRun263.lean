import Yulang.GeneralRebaseMultiObserver263
import Yulang.GeneralRebaseValidatedOutcome263

namespace Yulang.GeneralRebaseMultiRun263
open GeneralNominalCenters GeneralRebaseStep258
open GeneralSourceState (Output)
open GeneralRebaseMultiSelection263 (Selection check Ready Diagnostic)
open GeneralRebaseMultiObserver263

def validate (owners : List Nat) (representative : Nat → Plan roles) (pool : List Output)
 (inspect : Current owners representative pool → GeneralNominalCenteredSteps.State roles)
 (select : Current owners representative pool → List (Selection roles)) :
 Current owners representative pool → Except (Diagnostic roles) Unit :=
 fun state => check (inspect state) (select state)

def run (owners : List Nat) (representative : Nat → Plan roles) (pool : List Output)
 (inspect : Current owners representative pool → GeneralNominalCenteredSteps.State roles)
 (select : Current owners representative pool → List (Selection roles)) :=
 GeneralRebaseValidatedDriver263.run (observe owners representative pool inspect select)
   (validate owners representative pool inspect select)

theorem certificate (owners : List Nat) (representative : Nat → Plan roles) (pool : List Output)
 (inspect : Current owners representative pool → GeneralNominalCenteredSteps.State roles)
 (select : Current owners representative pool → List (Selection roles)) (before after : Current owners representative pool)
 (success : run owners representative pool inspect select before = .ok after) :
 ∃ history, GeneralRebaseValidatedDriver263.Trace (observe owners representative pool inspect select)
   (validate owners representative pool inspect select) history before after ∧
 GeneralRebaseBudget258.Runs (observe owners representative pool inspect select) history.length before after ∧
 history.length ≤ owners.length * (pool.length + pool.length * pool.length) ∧
 (∀ state ∈ history, Ready (inspect state) (select state)) ∧ Ready (inspect after) (select after) ∧
 (∀ next, ¬ Step (observe owners representative pool inspect select) after next) := by
 obtain ⟨history,trace,path,_,checked,final,terminal⟩ :=
   GeneralRebaseValidatedDriver263.certificate _ _ before after success
 refine ⟨history,trace,path,GeneralRebaseOwnerTable263.run_bound owners representative pool _ path,?_,?_,terminal⟩
 · intro state member
   exact (GeneralRebaseMultiSelection263.check_exact ..).mp (checked state member)
 · exact (GeneralRebaseMultiSelection263.check_exact ..).mp final

theorem outcome (owners : List Nat) (representative : Nat → Plan roles) (pool : List Output)
 (inspect : Current owners representative pool → GeneralNominalCenteredSteps.State roles)
 (select : Current owners representative pool → List (Selection roles)) (listed : Listed owners representative pool select)
 (layout : LayoutCompatible owners representative pool select)
 (coverage : ∀ state, GeneralRebaseChildRequestPool262.Covered (inspect state) pool)
 (before : Current owners representative pool) :
 (∃ after history, run owners representative pool inspect select before = .ok after ∧
   GeneralRebaseValidatedDriver263.Trace (observe owners representative pool inspect select)
     (validate owners representative pool inspect select) history before after ∧
   history.length ≤ owners.length * (pool.length + pool.length * pool.length)) ∨
 (∃ reason current steps, run owners representative pool inspect select before = .error (.validation reason) ∧
   GeneralRebaseBudget258.Runs (observe owners representative pool inspect select) steps before current ∧
   steps ≤ owners.length * (pool.length + pool.length * pool.length) ∧ reason.selected ∈ select current ∧
   GeneralRebaseClassCheck261.check reason.selected.plan
     (GeneralRebaseMultiSelection263.requests (inspect current) reason.selected) = .error reason.reason) := by
 rcases GeneralRebaseValidatedOutcome263.outcome _ _
   (closed owners representative pool inspect select listed layout coverage) before with success | failure
 · obtain ⟨after,history,success,trace,_⟩ := success
   exact Or.inl ⟨after,history,success,trace,GeneralRebaseOwnerTable263.run_bound owners representative pool _
     (GeneralRebaseValidatedDriver263.to_runs _ _ trace)⟩
 · obtain ⟨reason,current,steps,failed,path,_,diagnostic⟩ := failure
   obtain ⟨selected,exactError⟩ := GeneralRebaseMultiSelection263.error_selected _ _ reason diagnostic
   exact Or.inr ⟨reason,current,steps,failed,path,GeneralRebaseOwnerTable263.run_bound owners representative pool _ path,
     selected,exactError⟩
end Yulang.GeneralRebaseMultiRun263
