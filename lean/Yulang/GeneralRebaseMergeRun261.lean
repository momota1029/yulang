import Yulang.GeneralRebaseMergeMeaning261
namespace Yulang.GeneralRebaseMergeRun261
open GeneralRebaseStep258
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredHeadAllocMergeSource
open GeneralNominalCenteredHeadAllocMergeInstall
open GeneralNominalCenteredHeadAllocMergeState
open GeneralNominalCenteredHeadAllocMergeStable
open GeneralNominalCenteredHeadAllocMergeConflict (focus)
open GeneralRebaseMergeRequests261 (candidate outputs)

abbrev facts (atoms) := GeneralRebaseClassTable261.facts (candidate atoms) 38 outputs
abbrev initialState (atoms) := initial (facts atoms)
abbrev finalState (atoms) := done (facts atoms)
abbrev observe (atoms) := GeneralRebaseClassRun261.observe (candidate atoms) 38 outputs
abbrev run (atoms) := GeneralRebaseClassRun261.run (candidate atoms) 38 outputs
abbrev History (atoms) := GeneralNominalCenteredHeadAllocMergedConflict.HistoryModels (stage atoms)
abbrev Models (atoms) := GeneralRebaseClassTable261.Models (History atoms) (candidate atoms) 38 outputs

theorem facts_count (atoms) : (facts atoms).length = 6 := rfl

theorem nonempty (atoms) : facts atoms ≠ [] := by
 intro empty
 have length := congrArg List.length empty
 rw [facts_count] at length
 cases length

theorem first (atoms) : run atoms (initialState atoms) = .ok (some (finalState atoms)) :=
 GeneralRebaseClassRun261.first _ _ _ (GeneralRebaseMergeRequests261.ready atoms) (nonempty atoms)

theorem stop (atoms) : run atoms (finalState atoms) = .ok none :=
 GeneralRebaseClassRun261.stops _ _ _ (GeneralRebaseMergeRequests261.ready atoms)

theorem first_step (atoms) : Step (observe atoms) (initialState atoms) (finalState atoms) :=
 (GeneralRebaseClassRun261.run_step _ _ _ (GeneralRebaseMergeRequests261.ready atoms) _ _).mp (first atoms)

theorem settle_initial (atoms) : GeneralRebaseSettle259.settle (observe atoms) (initialState atoms) = .ok (finalState atoms) :=
 GeneralRebaseClassRun261.settle_initial ..

theorem initial_inhabited (atoms) : Models atoms (initialState atoms) witness :=
 (GeneralRebaseClassTable261.initial_exact ..).mpr GeneralNominalCenteredHeadAllocV7MergeRegression.history

theorem final_exact (atoms) (assignment : Assignment) : Models atoms (finalState atoms) assignment ↔
 History atoms assignment ∧ GeneralNominalVersionedEffects231.ClassEffects (stage atoms).core focus (candidate atoms) assignment := by
 exact (GeneralRebaseClassTable261.done_exact (History atoms) (candidate atoms) 38 outputs assignment).trans
   (and_congr Iff.rfl (GeneralRebaseMergeRequests261.effects_exact atoms assignment))

theorem final_uninhabited (atoms) : ¬ ∃ assignment, Models atoms (finalState atoms) assignment := by
 rintro ⟨assignment,valid⟩
 exact GeneralRebaseMergeMeaning261.history_effects_impossible atoms
   ⟨assignment,(GeneralRebaseClassTable261.done_exact ..).mp valid⟩

/-- Forgetting the historical parent-output obligations admits uniform, even
though the history-preserving final state has no model. -/
theorem raw_only_inhabited (atoms) (good : Good atoms) :
 GeneralRebaseClassTable261.Models (GeneralNominalState.Models (stage atoms).core.erased.current.context.state)
  (candidate atoms) 38 outputs (finalState atoms) uniform :=
 (GeneralRebaseClassTable261.done_exact ..).mpr ⟨raw_uniform good,GeneralRebaseMergeMeaning261.uniform_effects atoms⟩

theorem old_final_regression : ∃ atoms, final = stage atoms ∧
 Models atoms (initialState atoms) witness ∧
 run atoms (initialState atoms) = .ok (some (finalState atoms)) ∧
 (¬ ∃ assignment, Models atoms (finalState atoms) assignment) ∧
 GeneralNominalCenteredHeadAllocV7Boundary.Local sourceRegistry final focus .rejected := by
 obtain ⟨atoms,_,_,same⟩ := final_shape
 exact ⟨atoms,same,initial_inhabited atoms,first atoms,final_uninhabited atoms,
   GeneralNominalCenteredHeadAllocV7MergeRegression.final_rejected⟩
end Yulang.GeneralRebaseMergeRun261
