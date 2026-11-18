import Yulang.GeneralRebaseSelectedSettle262

namespace Yulang.GeneralRebaseSelectedFailure262
open GeneralNominalCenters GeneralRebaseStep258
open GeneralSourceState (Output)
open GeneralRebaseSelectedSettle262 (Current Failure run)
open GeneralRebaseObservedPlan262 (observe)

def At (fixed : Plan roles) (owner : Nat) (pool : List Output)
 (inspect : Current fixed owner pool → GeneralNominalCenteredSteps.State roles)
 (roots : Current fixed owner pool → List (GeneralSourceDictionaries.Occurrence roles))
 (plans : Current fixed owner pool → GeneralSourceDictionaries.Occurrence roles → Plan roles)
 (state : Current fixed owner pool) : Failure roles → Prop
 | .selected reason => GeneralRebaseSelectedCheck262.checkRoots (inspect state) (plans state) (roots state) = .error reason
 | .outside facts => GeneralRebaseSelectedCheck262.checkRoots (inspect state) (plans state) (roots state) = .ok () ∧
   GeneralRebaseScheduler259.next (observe fixed owner pool inspect roots plans) state = .error facts

/-- An internal error has a real finite-rebase prefix leading to its diagnostic
state. No language-level rejection or source-Step simulation follows. -/
theorem error_path (fixed : Plan roles) (owner : Nat) (pool : List Output)
 (inspect) (roots) (plans) (state : Current fixed owner pool) (failure : Failure roles)
 (failed : run fixed owner pool inspect roots plans state = .error failure) :
 ∃ current steps, GeneralRebaseBudget258.Runs (observe fixed owner pool inspect roots plans) steps state current ∧
 At fixed owner pool inspect roots plans current failure := by
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
       obtain ⟨current,steps,path,atCurrent⟩ := ih _ smaller after failed rfl
       exact ⟨current,steps+1,.next step path,atCurrent⟩

theorem selected_provenance (fixed : Plan roles) (owner : Nat) (pool : List Output)
 (inspect) (roots) (plans) (state : Current fixed owner pool)
 (reason : GeneralRebaseSelectedCheck262.Failure roles)
 (failed : run fixed owner pool inspect roots plans state = .error (.selected reason)) :
 ∃ current steps, GeneralRebaseBudget258.Runs (observe fixed owner pool inspect roots plans) steps state current ∧
 steps ≤ state.remaining.length ∧ reason.root ∈ roots current ∧
 GeneralRebaseClassCheck261.check (plans current reason.root)
   (GeneralRebaseExecutableRequests262.requests (inspect current) reason.root) = .error reason.reason := by
 obtain ⟨current,steps,path,atCurrent⟩ := error_path fixed owner pool inspect roots plans state (.selected reason) failed
 have budget := GeneralRebaseBudget258.budget _ path
 obtain ⟨selected,diagnostic⟩ := GeneralRebaseSelectedCheck262.error_selected _ _ _ reason atCurrent
 exact ⟨current,steps,path,by omega,selected,diagnostic⟩
end Yulang.GeneralRebaseSelectedFailure262
