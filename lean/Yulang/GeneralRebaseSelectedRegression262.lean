import Yulang.GeneralRebaseSelectedMeaning262
import Yulang.GeneralRebaseAliasRegression262

namespace Yulang.GeneralRebaseSelectedRegression262
open GeneralRebaseStep258
open GeneralRebaseMergeRequests261 (candidate outputs)
open GeneralNominalCenteredHeadAllocMergeInstall (aTarget)
open GeneralNominalCenteredHeadAllocMergeState (stage)
open GeneralNominalCenteredHeadAllocMergeConflict (focus)
open GeneralRebaseSelectedSettle262 (run Current)
open GeneralRebaseObservedPlan262 (observe)

/-- The same unused missing candidate as cycle261's boundary probe. -/
def unused : GeneralSourceState.Output := ⟨1,aTarget⟩
def candidates := outputs ++ [unused]
abbrev fixed := candidate []

theorem unused_missing : GeneralRebaseClassCheck261.check fixed candidates =
 .error (.missing [unused]) := rfl

theorem old_layout_failure (state : Current fixed 38 candidates) :
 GeneralRebaseCandidateValidation261.finish fixed 38 candidates (fun _ => []) state =
 .error (.layout (.missing [unused])) :=
 GeneralRebaseCandidateValidation261.layout_error _ _ _ _ state _ unused_missing

/-- The selected-only checker succeeds with no selected roots, despite the
same fixed pool's unused unknown request that the old checker rejected. -/
theorem unused_not_checked (state : Current fixed 38 candidates) :
 run fixed 38 candidates (fun _ => (stage []).core) (fun _ => []) (fun _ _ => fixed) state = .ok state := by
 rw [run]
 rfl

/-- Deliberately pairing the leaf demand with the parent's Plan is an internal
compiler mismatch; it is not a source program rejection theorem. -/
abbrev wrong := GeneralNominalCenteredHeadAllocMergeSource.plan

theorem selected_missing :
 GeneralRebaseSelectedCheck262.checkRoots (stage []).core (fun _ => wrong) [focus] =
 .error ⟨focus,.missing outputs⟩ := by
 rw [GeneralRebaseSelectedCheck262.checkRoots,GeneralRebaseAliasRegression262.actual_requests]
 rfl

theorem selected_failure (state : Current wrong 37 outputs) :
 run wrong 37 outputs (fun _ => (stage []).core) (fun _ => [focus]) (fun _ _ => wrong) state =
 .error (.selected ⟨focus,.missing outputs⟩) := by
 rw [run,selected_missing]

abbrev goodObserve := observe fixed 38 outputs (fun _ => (stage []).core) (fun _ => [focus]) (fun _ _ => fixed)

theorem good_ready : GeneralRebaseSelectedCheck262.ReadyRoots (stage []).core (fun _ => fixed) [focus] := by
 intro root member
 cases List.mem_singleton.mp member
 rw [GeneralRebaseAliasRegression262.actual_requests]
 exact GeneralRebaseMergeRequests261.ready []

theorem next_good (state : Current fixed 38 outputs) :
 GeneralRebaseScheduler259.next goodObserve state = .ok (tryWrite state (GeneralRebaseStableMerge261.facts [])) := by
 change GeneralRebaseScheduler259.scan state
   [GeneralRebaseStableClass261.facts fixed 38 (GeneralRebaseExecutableRequests262.requests (stage []).core focus)] = _
 rw [GeneralRebaseAliasRegression262.actual_requests]
 unfold GeneralRebaseScheduler259.scan
 rw [GeneralRebaseCheckedWrite259.supported state _ (fun _ member => member)]
 cases tryWrite state (GeneralRebaseStableMerge261.facts []) <;> rfl

theorem next_initial : GeneralRebaseScheduler259.next goodObserve (GeneralRebaseStableMerge261.initialState []) =
 .ok (some (GeneralRebaseStableMerge261.finalState [])) := by
 rw [next_good]
 unfold tryWrite
 rw [GeneralRebaseStableMergeDriver261.write_full]
 have different : (GeneralRebaseStableMerge261.finalState []).remaining ≠ (GeneralRebaseStableMerge261.initialState []).remaining := by
   intro same
   have size := congrArg List.length same
   change 0 = 6 at size
   cases size
 simp only [different,ite_false]

theorem next_final : GeneralRebaseScheduler259.next goodObserve (GeneralRebaseStableMerge261.finalState []) = .ok none := by
 rw [next_good]
 simp [tryWrite,GeneralRebaseStableMergeDriver261.write_full]

theorem run_good :
 run fixed 38 outputs (fun _ => (stage []).core) (fun _ => [focus]) (fun _ _ => fixed)
 (GeneralRebaseStableMerge261.initialState []) = .ok (GeneralRebaseStableMerge261.finalState []) :=
 GeneralRebaseSelectedSettle262.trace_success _ _ _ _ _ _ (.next good_ready next_initial (.done good_ready next_final))

/-- Even selected-request translation validation does not prove consistency
of the retained historical constraints. -/
theorem success_not_satisfiability :
 run fixed 38 outputs (fun _ => (stage []).core) (fun _ => [focus]) (fun _ _ => fixed)
 (GeneralRebaseStableMerge261.initialState []) = .ok (GeneralRebaseStableMerge261.finalState []) ∧
 ¬ ∃ assignment, GeneralRebaseStableMerge261.Models [] (GeneralRebaseStableMerge261.finalState []) assignment :=
 ⟨run_good,GeneralRebaseStableMerge261.final_uninhabited []⟩
end Yulang.GeneralRebaseSelectedRegression262
