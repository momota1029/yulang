import Yulang.GeneralRebaseBatchOrder259
open Yulang
namespace Cycle259DriverProbe
open GeneralRebaseStep258 GeneralRebaseScheduler259 GeneralRebaseSettle259
open GeneralVersionRebaseStep259 (facts initialState finalState)

def changesAfterInstall : Observer facts := fun state =>
 if state.remaining.isEmpty then [[.installed 999]] else [facts]

theorem initial_progress : next changesAfterInstall initialState = .ok (some finalState) := by
 change scan initialState [facts] = _
 have one := GeneralRebaseDriverFixtures259.version_next 0 initialState
 rw [next,GeneralVersionRebaseStep259.observe_exact,GeneralVersionRebaseStep259.run_first] at one
 exact one

theorem later_unsupported : next changesAfterInstall finalState = .error [.installed 999] := rfl

/-- Internal malformed observer, not a source-reachable language counterexample. -/
theorem no_whole_run_rollback_claim : settle changesAfterInstall initialState = .error [.installed 999] := by
 rw [settle]
 change settle changesAfterInstall finalState = _
 rw [settle]
 rw [later_unsupported]

#print axioms initial_progress
#print axioms later_unsupported
#print axioms no_whole_run_rollback_claim

#eval match settle (GeneralDictionaryObservedRebase259.observeAt 0) GeneralDictionaryRebaseStep258.initialState with
 | .ok result => s!"I45 remaining={result.remaining.length}"
 | .error missing => s!"I45 unexpected error={missing.length}"
#eval match settle (GeneralVersionRebaseStep259.observeAt 0) initialState with
 | .ok result => s!"239 remaining={result.remaining.length}"
 | .error missing => s!"239 unexpected error={missing.length}"
#eval match settle changesAfterInstall initialState with
 | .ok result => s!"malformed unexpected remaining={result.remaining.length}"
 | .error missing => s!"malformed unsupported-count={missing.length}"
end Cycle259DriverProbe
