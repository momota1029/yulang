import Yulang.GeneralRebaseCandidateTrace261
import Yulang.GeneralRebaseMergeHistory261
namespace Yulang.GeneralRebaseStableMerge261
open GeneralNominalCommonBridge (Assignment)
open GeneralRebaseStep258
open GeneralNominalCenteredHeadAllocMergeState
open GeneralRebaseMergeRequests261 (candidate outputs)

abbrev facts (atoms) := GeneralRebaseStableClass261.facts (candidate atoms) 38 outputs
abbrev initialState (atoms) := initial (facts atoms)
abbrev finalState (atoms) := done (facts atoms)
abbrev Models (atoms) := GeneralRebaseStableClass261.Models GeneralRebaseMergeHistory261.Base (candidate atoms) 38 (candidates := outputs)

theorem facts_count (atoms) : (facts atoms).length = 6 := rfl

theorem initial_exact (atoms) (assignment : Assignment) : Models atoms (initialState atoms) assignment ↔
 GeneralRebaseMergeHistory261.Base assignment := GeneralRebaseFactSemantics259.initial_exact ..

theorem final_exact (atoms) (assignment : Assignment) : Models atoms (finalState atoms) assignment ↔
 GeneralRebaseMergeRun261.Models atoms (GeneralRebaseMergeRun261.finalState atoms) assignment := by
 change GeneralRebaseFactSemantics259.Models _ _ (done _) _ ↔ _
 rw [GeneralRebaseFactSemantics259.done_exact,GeneralRebaseStableClass261.all_exact]
 exact (and_congr (GeneralRebaseMergeHistory261.history_exact atoms assignment).symm Iff.rfl).trans
   (GeneralRebaseClassTable261.done_exact ..).symm

theorem final_uninhabited (atoms) : ¬ ∃ assignment, Models atoms (finalState atoms) assignment := by
 rintro ⟨assignment,valid⟩
 exact GeneralRebaseMergeRun261.final_uninhabited atoms ⟨assignment,(final_exact atoms assignment).mp valid⟩

/-- Actual requests remain in the fixed two-element candidate list for every
ordinary-atom list of this fixture. This is not arbitrary-source coverage. -/
theorem requests_covered (atoms) : ∀ output ∈ GeneralNominalCenteredHeadOutputs.requests
 (stage atoms).core GeneralNominalCenteredHeadAllocMergeConflict.focus, output ∈ outputs :=
 fun output inside => (GeneralRebaseMergeRequests261.requests_exact atoms output).mp inside

noncomputable def select (atoms)
 (inspect : State (facts atoms) → List (PresenceNormalForm.Atom Nat)) (state : State (facts atoms)) :=
 [GeneralNominalCenteredHeadOutputs.requests (stage (inspect state)).core GeneralNominalCenteredHeadAllocMergeConflict.focus]

theorem covered (atoms) (inspect) :
 GeneralRebaseCandidateDriver261.Covered (candidate atoms) 38 outputs (select atoms inspect) := by
 intro state selected member
 cases List.mem_singleton.mp member
 exact requests_covered (inspect state)

theorem completion (atoms) (inspect) (state : State (facts atoms)) : ∃ final steps,
 GeneralRebaseSettle259.settle (GeneralRebaseCandidateDriver261.observe (candidate atoms) 38 outputs (select atoms inspect)) state = .ok final ∧
 GeneralRebaseBudget258.Runs (GeneralRebaseCandidateDriver261.observe (candidate atoms) 38 outputs (select atoms inspect)) steps state final ∧
 steps ≤ state.remaining.length ∧
 (∀ after, ¬ Step (GeneralRebaseCandidateDriver261.observe (candidate atoms) 38 outputs (select atoms inspect)) final after) :=
 GeneralRebaseCandidateDriver261.completion _ _ _ _ (covered atoms inspect) state
end Yulang.GeneralRebaseStableMerge261
