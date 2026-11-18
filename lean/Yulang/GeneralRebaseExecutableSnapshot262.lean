import Yulang.GeneralRebaseExecutableRequests262

namespace Yulang.GeneralRebaseExecutableSnapshot262
open GeneralNominalCenters GeneralRebaseStep258
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalCommonBridge (Assignment)
open GeneralRebaseSourceSnapshot261 (candidates)

def select (source : GeneralNominalCenteredSteps.State roles) (plan : Plan roles) (owner : Nat)
 (roots : State (GeneralRebaseStableClass261.facts plan owner (candidates source)) → List (Occurrence roles))
 (state : State (GeneralRebaseStableClass261.facts plan owner (candidates source))) :=
 (roots state).map (GeneralRebaseExecutableRequests262.requests source)

theorem select_eq (source : GeneralNominalCenteredSteps.State roles) (plan : Plan roles) (owner : Nat) (roots) :
 select source plan owner roots = GeneralRebaseSourceSnapshot261.select source plan owner roots := by
 funext state
 unfold select GeneralRebaseSourceSnapshot261.select
 apply List.map_congr_left
 intro root _
 exact GeneralRebaseExecutableRequests262.requests_eq source root

def observe (source : GeneralNominalCenteredSteps.State roles) (plan : Plan roles) (owner : Nat) (roots) :=
 GeneralRebaseCandidateDriver261.observe plan owner (candidates source) (select source plan owner roots)

theorem covered (source : GeneralNominalCenteredSteps.State roles) (plan : Plan roles) (owner : Nat) (roots) :
 GeneralRebaseCandidateDriver261.Covered plan owner (candidates source) (select source plan owner roots) := by
 rw [select_eq]
 exact GeneralRebaseSourceSnapshot261.all_covered source plan owner roots

/-- Actual finite snapshot selection is executable; source and plan stay fixed.
No hypothesis about alias coverage or observer correctness is required. -/
theorem completion (source : GeneralNominalCenteredSteps.State roles) (plan : Plan roles) (owner : Nat) (roots)
 (state : State (GeneralRebaseStableClass261.facts plan owner (candidates source))) :
 ∃ final steps, GeneralRebaseSettle259.settle (observe source plan owner roots) state = .ok final ∧
 GeneralRebaseBudget258.Runs (observe source plan owner roots) steps state final ∧
 steps ≤ state.remaining.length ∧ (∀ after, ¬ Step (observe source plan owner roots) final after) :=
 GeneralRebaseCandidateDriver261.completion _ _ _ _ (covered source plan owner roots) state

theorem step_actual (base : Assignment → Prop) (source : GeneralNominalCenteredSteps.State roles)
 (plan : Plan roles) (owner : Nat) (roots)
 (before after : State (GeneralRebaseStableClass261.facts plan owner (candidates source)))
 (step : Step (observe source plan owner roots) before after) :
 ∃ root ∈ roots before, ∀ assignment,
 GeneralRebaseStableClass261.Models base plan owner after assignment ↔
 GeneralRebaseStableClass261.Models base plan owner before assignment ∧
 GeneralNominalVersionedEffects231.ClassEffects source root plan assignment := by
 unfold observe at step
 rw [select_eq] at step
 exact GeneralRebaseSourceSnapshot261.step_actual base source plan owner roots before after step

/-- Successful finite runs retain one actual root per write. The same root
history witnesses the model equation simultaneously for every assignment. -/
theorem history_actual (base : Assignment → Prop) (source : GeneralNominalCenteredSteps.State roles)
 (plan : Plan roles) (owner : Nat) (roots) {steps before after}
 (run : GeneralRebaseBudget258.Runs (observe source plan owner roots) steps before after) :
 ∃ history : List (Occurrence roles), history.length = steps ∧
 (∀ root ∈ history, ∃ state, root ∈ roots state) ∧
 (∀ assignment, GeneralRebaseStableClass261.Models base plan owner after assignment ↔
 GeneralRebaseStableClass261.Models base plan owner before assignment ∧
 ∀ root ∈ history, GeneralNominalVersionedEffects231.ClassEffects source root plan assignment) := by
 induction run with
 | nil state => exact ⟨[],rfl,by simp,by simp⟩
 | @next n before middle after step _ ih =>
   obtain ⟨root,selected,meaning⟩ := step_actual base source plan owner roots before middle step
   obtain ⟨rest,length,selectedRest,models⟩ := ih
   refine ⟨root :: rest,by simp [length],?_,?_⟩
   · intro item member
     rcases List.mem_cons.mp member with rfl | prior
     · exact ⟨before,selected⟩
     · exact selectedRest item prior
   · intro assignment
     rw [models,meaning]
     simp only [List.mem_cons,forall_eq_or_imp]
     exact and_assoc

theorem finish_history (base : Assignment → Prop) (source : GeneralNominalCenteredSteps.State roles)
 (plan : Plan roles) (owner : Nat) (roots)
 (before : State (GeneralRebaseStableClass261.facts plan owner (candidates source))) :
 ∃ after, ∃ history : List (Occurrence roles),
 GeneralRebaseSettle259.settle (observe source plan owner roots) before = .ok after ∧
 history.length ≤ before.remaining.length ∧
 (∀ root ∈ history, ∃ state, root ∈ roots state) ∧
 (∀ assignment, GeneralRebaseStableClass261.Models base plan owner after assignment ↔
 GeneralRebaseStableClass261.Models base plan owner before assignment ∧
 ∀ root ∈ history, GeneralNominalVersionedEffects231.ClassEffects source root plan assignment) := by
 obtain ⟨after,n,success,run,bound,_⟩ := completion source plan owner roots before
 obtain ⟨history,length,selected,models⟩ := history_actual base source plan owner roots run
 exact ⟨after,history,success,by simpa [length] using bound,selected,models⟩
end Yulang.GeneralRebaseExecutableSnapshot262
