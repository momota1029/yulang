import Yulang.GeneralRebaseCheckedWrite259
namespace Yulang.GeneralRebaseCheckedFixtures259
open GeneralRebaseStep258
open GeneralRebaseCheckedWrite259

/-- Actual I45 initial inspection, then closure-check before any write.
The none branch is unreachable for this fixed source, as loose_exact proves. -/
def looseRun (state : State GeneralDictionaryRebaseStep258.facts) :
 Except (List Fact) (Option (State GeneralDictionaryRebaseStep258.facts)) :=
 match GeneralRebaseReportDecoder259.compile
   (GeneralDictionaryReportProjection257.transport 0
     (GeneralNominalPacketSupport.report (GeneralDictionaryLooseIterationBook240.packet 0))) with
 | none => .ok none
 | some proposal => commit state proposal

def versionRun (state : State GeneralVersionRebaseStep259.facts) :
 Except (List Fact) (Option (State GeneralVersionRebaseStep259.facts)) :=
 match GeneralVersionRebaseStep259.proposal 0 with
 | none => .ok none
 | some proposal => commit state proposal

theorem loose_exact (state : State GeneralDictionaryRebaseStep258.facts) :
 looseRun state = .ok (GeneralDictionaryRebaseCurrent259.run state) := by
 unfold looseRun
 rw [GeneralRebaseReportDecoder259.actual]
 change commit state GeneralDictionaryRebaseStep258.facts = _
 rw [supported state _ (fun _ member => member)]
 rw [GeneralDictionaryRebaseCurrent259.run,GeneralDictionaryRebaseRun259.run_exact]

theorem version_exact (state : State GeneralVersionRebaseStep259.facts) :
 versionRun state = .ok (GeneralVersionRebaseStep259.run state) := by
 unfold versionRun
 rw [GeneralVersionRebaseStep259.proposal_exact]
 change commit state GeneralVersionRebaseStep259.facts = _
 rw [supported state _ (fun _ member => member),GeneralVersionRebaseStep259.run_exact]

theorem loose_first : looseRun GeneralDictionaryRebaseStep258.initialState =
 .ok (some GeneralDictionaryRebaseStep258.finalState) := by
 rw [loose_exact,GeneralDictionaryRebaseCurrent259.first]

theorem loose_stop : looseRun GeneralDictionaryRebaseStep258.finalState = .ok none := by
 rw [loose_exact,GeneralDictionaryRebaseCurrent259.stops]

theorem version_first : versionRun GeneralVersionRebaseStep259.initialState =
 .ok (some GeneralVersionRebaseStep259.finalState) := by
 rw [version_exact,GeneralVersionRebaseStep259.run_first]

theorem version_stop : versionRun GeneralVersionRebaseStep259.finalState = .ok none := by
 rw [version_exact,GeneralVersionRebaseStep259.run_stop]

/-- Deliberately malformed internal proposal, not a source-reachable program. -/
theorem unsupported_mixed : commit GeneralDictionaryRebaseStep258.initialState
 [.installed 0,.installed 999] = .error [.installed 999] := rfl

theorem version_unsupported : commit GeneralVersionRebaseStep259.initialState
 [.lower 0 1] = .error [.lower 0 1] := rfl
end Yulang.GeneralRebaseCheckedFixtures259
