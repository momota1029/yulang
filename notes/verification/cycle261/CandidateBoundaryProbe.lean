import Yulang.GeneralRebaseStableMergeFinish261
namespace Yulang.CandidateBoundaryProbe261
open GeneralRebaseStep258
open GeneralRebaseMergeRequests261 (candidate outputs)
open GeneralNominalCenteredHeadAllocMergeInstall (aTarget)

def unused : GeneralSourceState.Output := ⟨1,aTarget⟩
def candidates := outputs ++ [unused]
abbrev plan := candidate []
abbrev basis := GeneralRebaseStableClass261.facts plan 38 candidates

theorem unused_missing : GeneralRebaseClassCheck261.check plan candidates =
 .error (.missing [unused]) := rfl

theorem empty_selection_covered : GeneralRebaseCandidateDriver261.Covered plan 38 candidates (fun _ => []) := by
 intro state requests included
 cases included

/-- No dynamic request is selected, so the unvalidated scheduler is already
finished, even though an unused layout candidate has no associated body. -/
theorem empty_settles (state : State basis) :
 GeneralRebaseSettle259.settle (GeneralRebaseCandidateDriver261.observe plan 38 candidates (fun _ => [])) state = .ok state := by
 rw [GeneralRebaseSettle259.settle]
 rfl

theorem unused_layout_error (state : State basis) :
 GeneralRebaseCandidateValidation261.finish plan 38 candidates (fun _ => []) state =
 .error (.layout (.missing [unused])) :=
 GeneralRebaseCandidateValidation261.layout_error _ _ _ _ state _ unused_missing

-- The error is a conservative internal layout error, not a source-rejection result.
end Yulang.CandidateBoundaryProbe261

#print axioms Yulang.CandidateBoundaryProbe261.unused_missing
#print axioms Yulang.CandidateBoundaryProbe261.empty_selection_covered
#print axioms Yulang.CandidateBoundaryProbe261.empty_settles
#print axioms Yulang.CandidateBoundaryProbe261.unused_layout_error
